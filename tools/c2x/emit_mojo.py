"""
emit_mojo.py - EPA SWMM 5.2.4 C  ->  Mojo 1.2 (one generated module, mojo/swmm5/engine.mojo; the C runtime is
mojo/swmm5/rt.mojo, imported as rt; the command line is mojo/swmm5/main.mojo).

Mojo has raw pointers (Pointer[T, MutUntrackedOrigin], aliased P[T]), fixed-width integers that wrap, IEEE
floats and value structs, so the translation keeps C's data and its pointers, as the Zig back end does
(emit_zig.py; this back end reuses its naming, type classification, literal folding and control-flow facts),
and writes Mojo's statements, which are Python's:

  int/unsigned/long/unsigned long/short/char -> Int32/UInt32/Int64/UInt64/Int16/Int8 (+ - * wrap in Mojo too)
  double/float                               -> Float64/Float32
  T* ; void* ; FILE*                         -> P[T] ; VP (P[NoneType]) ; P[rt.FILE]; NULL -> rt.null[T]()
  function pointer                           -> Int32: a number for each function whose address is taken,
                                                called through a generated dispatcher per signature (Mojo
                                                1.2 cannot keep a function value in a struct field)
  struct ; union                             -> a Mojo struct (Copyable, Movable), copied with .copy();
                                                a union is a struct of raw words read as its members
  an array object (local, global, field)     -> its storage, and as a value the pointer to its first element
                                                (multi-dimensional arrays are flattened: a[i][j] is
                                                a.unsafe_offset(i * 3)[unsafe_offset=j]); an array field of a
                                                struct is a block of raw words inside the struct, so a copy
                                                of the struct copies the array
  globals (and static locals)                -> fields of one Globals struct, allocated at start-up and passed
                                                to every function as its first parameter G (Mojo 1.2 has no
                                                global variables)
  locals                                     -> declared at the top of the function, zero-initialised; a local
                                                whose address is taken, every local array and every local
                                                struct lives in a stack slot (stack_allocation), as in C
  / and % on signed integers                 -> rt.idiv32/rt.irem32 (C truncates, Mojo's // floors)
  << >> with a computed count                -> rt.shl32 ... (x86 masks the count)
  double -> int                              -> rt.d2i32 ... (x86-64 cvttsd2si: NaN or out of range -> INT_MIN)
  int -> double, double -> float ...         -> Float64(x), Float32(x) ... written out
  assignment, ++, -- used as values          -> rt.set(place, v), rt.postinc(place) ...: the place is passed by
                                                reference (a Mojo `mut` argument), so it is evaluated once
  switch                                     -> if/elif, or a one-pass while loop with a fall-through flag
  for(;;)                                    -> a while loop with the increment repeated before every continue
  float literals                             -> Float64(<shortest decimal>) (Mojo rounds each literal once, as
                                                C does: checked on every literal the engine uses); float
                                                (single) literals from their bits
  libm (exp, log, pow, sin, ...)             -> rt.exp ...: glibc's own functions through external_call, behind
                                                wrappers LLVM may not inline or fold; fabs/sqrt/floor/ceil ->
                                                rt.fabs and Mojo's sqrt/floor/ceil (exact instructions)
The build passes --fp-mode contract=off: Mojo's default fuses a*b+c into one FMA, which C (gcc -O2 on x86-64
without -mfma) never does. Written by Claude (Anthropic) for Robert Dickinson; see mojo/README.md.
"""
import os, re, sys, collections, struct
from fractions import Fraction
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, record_name, decl_key
from emit_zig import (ZigEmitter, E, info, wrap_int, f32_round, var_init, LIBC, VARIADIC)

MOJO_KEYWORDS = set('''def fn struct trait var let alias comptime import from as if elif else while for in return
break continue pass raise raises try except finally with and or not is True False None owned borrowed inout mut
out ref read deinit self Self lambda yield async await match case global nonlocal del assert print len range
Int Int8 Int16 Int32 Int64 UInt UInt8 UInt16 UInt32 UInt64 Float32 Float64 Bool String List Dict Pointer
NoneType abs min max sqrt floor ceil size_of bitcast stack_allocation rt P VP G Globals main object type
SIMD Scalar DType StaticTuple Optional Span Error'''.split())

INT_T = {('i8'): 'Int8', 'u8': 'UInt8', 'i16': 'Int16', 'u16': 'UInt16', 'i32': 'Int32', 'u32': 'UInt32',
         'i64': 'Int64', 'u64': 'UInt64'}
FLT_T = {'f64': 'Float64', 'f32': 'Float32'}
D2I = {'Int32': 'rt.d2i32', 'Int64': 'rt.d2i64', 'UInt32': 'rt.d2u32', 'UInt64': 'rt.d2u64', 'Int16': 'rt.d2i16',
       'Int8': 'rt.d2i8', 'UInt8': 'rt.d2u8', 'UInt16': 'rt.d2u16'}
# C library functions that need the runtime's state as their first argument
RT_STATE = {'strtok', 'mkstemp', 'ctime'}
MATH_EXT = {'exp', 'log', 'log10', 'pow', 'sin', 'cos', 'tan', 'asin', 'acos', 'atan'}


def mstr(b):
    """a Mojo string literal for ASCII bytes b (no NUL)"""
    out = []
    for ch in b:
        if ch == 0x5c:
            out.append('\\\\')
        elif ch == 0x22:
            out.append('\\"')
        elif 32 <= ch < 127:
            out.append(chr(ch))
        elif ch == 10:
            out.append('\\n')
        elif ch == 9:
            out.append('\\t')
        elif ch == 13:
            out.append('\\r')
        else:
            out.append('\\x%02x' % ch)
    return '"' + ''.join(out) + '"'


def flt64_text(v):
    """Mojo source for the double v (finite): Float64(<repr>), which Mojo rounds once to v"""
    if v != v or v in (float('inf'), float('-inf')):
        raise ValueError('special float literal')
    if v == 0:
        return 'Float64(-0.0)' if struct.pack('<d', v)[7] & 0x80 else 'Float64(0.0)'
    r = repr(v)
    return 'Float64(%s)' % r


def flt32_text(v):
    b = struct.unpack('<I', struct.pack('<f', v))[0]
    return 'rt.f32b(UInt32(0x%08x))' % b


class MojoEmitter(ZigEmitter):
    def __init__(self, F):
        self.F = F
        self.problems = []
        self.defects = []
        self.fn_types = collections.OrderedDict()
        self._names()
        self.fn_ids = collections.OrderedDict()      # function key -> id (address taken)
        self.fp_sigs = collections.OrderedDict()     # signature -> dispatcher name
        self.lits = collections.OrderedDict()        # non-ASCII string literal bytes -> Globals field

    # ================================================================== naming
    def _names(self):
        F = self.F
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        taken = set()

        def fresh(n, suffix='_'):
            nn = n
            while nn in taken or nn in MOJO_KEYWORDS or nn.startswith('__'):
                nn += suffix
            taken.add(nn)
            return nn
        self.fname = {}
        for (b, n), c in F.funcs.items():
            self.fname[(b, n)] = fresh(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        # globals live in the Globals struct, so their names need only be distinct among themselves
        gtaken = set()

        def gfresh(n):
            nn = n
            while nn in gtaken or nn in MOJO_KEYWORDS or nn.startswith('__'):
                nn += '_'
            gtaken.add(nn)
            return nn
        self.gname = {}
        for k, c in F.globals.items():
            n = c.spelling
            b = F.global_owner[k]
            self.gname[k] = gfresh(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.slname = {}
        for (b, n), c in F.funcs.items():
            def walk(x):
                for y in x.get_children():
                    if y.kind == K.VAR_DECL and y.storage_class == front.ci.StorageClass.STATIC:
                        self.slname[decl_key(y)] = gfresh('%s_%s' % (self.fname[(b, n)], y.spelling))
                    walk(y)
            walk(c)
        self.gtaken = gtaken
        self.recname = {}
        for name in F.records:
            self.recname[name] = fresh(name)
        self.ename = {}
        for n in F.enum_consts:
            self.ename[n] = fresh(n)
        vals = collections.defaultdict(set)
        for b, m in F.macros.items():
            for n, v in m.items():
                vals[n].add(v)
        self.mname = {}
        self.mval = {}
        for n in sorted(vals):
            vs = vals[n]
            if len(vs) != 1:
                continue
            kind, s = next(iter(vs))
            if kind not in ('int', 'float') or n in F.enum_consts:
                continue
            if n in cnt or n in self.recname:
                continue
            self.mname[n] = fresh(n)
            self.mval[n] = (kind, s)
        self.top = taken

    # ================================================================== types
    def rec(self, t):
        n = record_name(t)
        return self.recname.get(n, n)

    def flat(self, t):
        """(base element type, total element count) of an array type (multi-dimensional arrays flattened)"""
        t = canon(t)
        n = 1
        while t.kind == T.CONSTANTARRAY:
            n *= t.element_count
            t = canon(t.element_type)
        return t, n

    def mt(self, t):
        """the Mojo type of a value of C type t (an array decays to a pointer to its first scalar element)"""
        i = info(t)
        k = i[0]
        if k == 'int':
            return INT_T[i[1]]
        if k == 'flt':
            return FLT_T[i[1]]
        if k == 'void':
            return 'None'
        if k == 'rec':
            return self.rec(t)
        if k == 'arr':
            return 'P[%s]' % self.mt(self.flat(t)[0])
        if k == 'fn':
            return 'Int32'
        p = canon(i[1])
        if p.kind == T.VOID:
            return 'VP'
        if p.kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return 'Int32'
        if front.is_file_ptr(t):
            return 'P[rt.FILE]'
        if p.kind == T.CONSTANTARRAY:
            return 'P[%s]' % self.mt(self.flat(p)[0])
        return 'P[%s]' % self.mt(p)

    def pointee_mt(self, t):
        """the Mojo element type a C pointer of type t points to (flattened for a pointer to an array)"""
        p = canon(info(t)[1]) if info(t)[0] == 'ptr' else canon(self.flat(t)[0])
        if p.kind == T.VOID:
            return 'NoneType'
        if p.kind == T.CONSTANTARRAY:
            return self.mt(self.flat(p)[0])
        if front.is_file_ptr(t):
            return 'rt.FILE'
        return self.mt(p)

    def stride(self, t):
        """elements of the flattened base type one step of a pointer of type t moves"""
        i = info(t)
        p = canon(i[1]) if i[0] == 'ptr' else canon(i[1])
        if i[0] == 'arr':
            p = canon(i[1])
        if p.kind == T.CONSTANTARRAY:
            return self.flat(p)[1]
        return 1

    def has_record(self, t):
        t = canon(t)
        while t.kind == T.CONSTANTARRAY:
            t = canon(t.element_type)
        return t.kind == T.RECORD

    def sizeof_code(self, t):
        """C sizeof(t) as Mojo code: records use Mojo's layout (the allocations and byte copies use it too)"""
        t = canon(t)
        if self.has_record(t):
            base, n = self.flat(t)
            return 'UInt64(%s)' % ('size_of[%s]()' % self.rec(base) if n == 1 else '%d * size_of[%s]()' % (n, self.rec(base)))
        return str(t.get_size())

    def zero(self, t):
        i = info(t)
        if i[0] == 'int':
            return '%s(0)' % INT_T[i[1]]
        if i[0] == 'flt':
            return '%s(0.0)' % FLT_T[i[1]]
        if i[0] in ('ptr', 'arr'):
            m = self.mt(t)
            if m == 'Int32':
                return 'Int32(0)'
            if m == 'VP':
                return 'rt.null[NoneType]()'
            return 'rt.null[%s]()' % m[2:-1]
        if i[0] == 'rec':
            return '%s()' % self.rec(t)
        if i[0] == 'fn':
            return 'Int32(0)'
        return 'None'

    # ================================================================== literals
    def int_lit(self, v, mt):
        return '%s(%d)' % (mt, v)

    def flt_text(self, v, bits):
        if v != v:
            return 'rt.nan64()' if bits == 64 else 'Float32(rt.nan64())'
        if v in (float('inf'), float('-inf')):
            s = 'rt.inf64()' if bits == 64 else 'Float32(rt.inf64())'
            return '(-%s)' % s if v < 0 else s
        return flt64_text(v) if bits == 64 else flt32_text(v)

    # ================================================================== conversions
    def conv(self, e, dst):
        d = canon(dst)
        di = info(d)
        if di[0] == 'void':
            return e.code
        if e.isbool:
            if di[0] == 'int':
                return '%s(%s)' % (INT_T[di[1]], e.code)
            if di[0] == 'flt':
                return '%s(Int32(%s))' % (FLT_T[di[1]], e.code)
            self.problem(None, 'bool to %s' % d.spelling)
            return e.code
        si = info(e.t)
        if di[0] == 'int':
            dm = INT_T[di[1]]
            if si[0] == 'int':
                if e.lit is not None:
                    v = wrap_int(e.lit, di[2], di[3])
                    if re.fullmatch(r'[A-Za-z_]\w*', e.code) and v == e.lit and e.code in self.mname.values():
                        return '%s(%s)' % (dm, e.code)
                    return self.int_lit(v, dm)
                if INT_T[si[1]] == dm:
                    return e.code
                return '%s(%s)' % (dm, e.code)
            if si[0] == 'flt':
                if e.lit is not None:
                    v = e.lit
                    if v == v and -2 ** 63 <= v < 2 ** 63:
                        n = int(v)
                        if di[2] == 64 or (di[3] and -2 ** 31 <= n < 2 ** 31):
                            return self.int_lit(wrap_int(n, di[2], di[3]), dm)
                src = e.code if si[2] == 64 else 'Float64(%s)' % e.code
                return '%s(%s)' % (D2I[dm], src)
            if si[0] in ('ptr', 'arr', 'fn'):
                if self.mt(e.t) == 'Int32':
                    return '%s(%s)' % (dm, e.code)
                self.problem(None, 'pointer to integer')
                return '%s(Int(%s))' % (dm, e.code)
        if di[0] == 'flt':
            dm = FLT_T[di[1]]
            if si[0] == 'int':
                if e.lit is not None:
                    v = float(e.lit) if di[2] == 64 else f32_round(float(e.lit))
                    return self.flt_text(v, di[2])
                return '%s(%s)' % (dm, e.code)
            if si[0] == 'flt':
                if si[2] == di[2]:
                    return e.code
                if e.lit is not None:
                    v = e.lit if di[2] == 64 else f32_round(e.lit)
                    return self.flt_text(v, di[2])
                return '%s(%s)' % (dm, e.code)
        if di[0] == 'ptr':
            dm = self.mt(d)
            if dm == 'Int32':                      # function pointer
                if (si[0] == 'int' and e.lit == 0) or e.code.startswith('rt.null[') or e.code.startswith('(rt.null['):
                    return 'Int32(0)'
                if si[0] == 'fn':
                    return self.fn_id_code(e.code)
                return e.code
            if si[0] == 'int' and e.lit == 0:
                return self.zero(d)
            if e.code.startswith('rt.null['):
                return self.zero(d)
            if si[0] == 'arr' or (si[0] == 'ptr' and e.t.kind == T.INCOMPLETEARRAY):
                if e.strlit is not None:
                    return self.strlit_ptr(e.strlit)
                sm = self.mt(e.t)
                if sm == dm:
                    return e.code
                return '%s.unsafe_bitcast[%s]()' % (self.paren(e.code), self.pointee_mt(d))
            if si[0] == 'ptr':
                sm = self.mt(e.t)
                if sm == dm:
                    return e.code
                return '%s.unsafe_bitcast[%s]()' % (self.paren(e.code), self.pointee_mt(d))
            if si[0] == 'int':
                self.problem(None, 'integer to pointer')
                return '%s(unsafe_from_address=Int(%s))' % (dm, e.code)
        if di[0] in ('rec', 'arr'):
            return e.code
        if di[0] == 'fn':
            return e.code
        self.problem(None, 'conversion %s -> %s' % (e.t.spelling, d.spelling))
        return e.code

    def fn_id_code(self, name):
        """the number standing for function `name` as a C function pointer"""
        key = self.fkey_by_name.get(name)
        if key is None:
            self.problem(None, 'address of unknown function %s' % name)
            return 'Int32(0)'
        if key not in self.fn_ids:
            self.fn_ids[key] = len(self.fn_ids) + 1
        return 'Int32(%d)' % self.fn_ids[key]

    def as_bool(self, e):
        if e.isbool:
            return e.code
        i = info(e.t)
        if i[0] in ('int', 'flt'):
            if e.lit is not None:
                return 'True' if e.lit != 0 else 'False'
            return '(%s != 0)' % e.code
        if i[0] in ('ptr',):
            if self.mt(e.t) == 'Int32':
                return '(%s != 0)' % e.code
            return '(not rt.isnull(%s))' % e.code
        if i[0] in ('arr', 'fn'):
            return 'True'
        self.problem(None, 'condition of type %s' % e.t.spelling)
        return e.code

    @staticmethod
    def paren(s):
        if re.fullmatch(r'[\w.\[\]]+', s) and not s.startswith('-'):
            return s
        if s.startswith('(') and s.endswith(')') and ZigEmitter._balanced(s[1:-1]):
            return s
        return '(' + s + ')'

    # ================================================================== expressions
    def x_INTEGER_LITERAL(self, c):
        e = ZigEmitter.x_INTEGER_LITERAL(self, c)
        if e.code in self.mname.values():
            return e
        return E(self.int_lit(e.lit, self.mt(e.t)), e.t, lit=e.lit)

    def x_CHARACTER_LITERAL(self, c):
        r = evaluate(c)
        v = r[1] if r else 0
        t = canon(c.type)
        return E(self.int_lit(v, self.mt(t)), t, lit=v)

    def x_INIT_LIST_EXPR(self, c):
        self.problem(c, 'initializer list used as an expression')
        return E(self.zero(c.type), canon(c.type))

    def x_STRING_LITERAL(self, c):
        b = self.string_bytes(c)
        return E(self.strlit_ptr(b), canon(c.type), strlit=b)

    def strlit_ptr(self, b):
        if all(32 <= ch < 127 or ch in (9, 10, 13, 8) for ch in b):
            return 'rt.s(%s)' % mstr(b)
        if b not in self.lits:
            self.lits[b] = '__lit%d' % len(self.lits)
        return 'G[].%s' % self.lits[b]

    def x_GNU_NULL_EXPR(self, c):
        return E(self.zero(c.type), canon(c.type))

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        t = canon(c.type)
        if d is None:
            self.problem(c, 'unresolved name %s' % c.spelling)
            return E(c.spelling, t)
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return E(self.int_lit(d.enum_value, 'Int32'), t, lit=d.enum_value)
            return E(self.ename[d.spelling], t, lit=d.enum_value)
        if d.kind == K.FUNCTION_DECL:
            return E(self.func_name(d), canon(d.type))
        if d.kind == K.PARM_DECL:
            return E(self.local_ref(d), t)
        if d.kind == K.VAR_DECL:
            if d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL:
                if d.storage_class == front.ci.StorageClass.STATIC:
                    return E('G[].%s' % self.slname[decl_key(d)], t)
                if d.storage_class != front.ci.StorageClass.EXTERN:
                    return E(self.local_ref(d), t)
            if d.spelling in ('stdout', 'stderr'):
                return E('G[].R_[].stdout', t)
            return E('G[].%s' % self.global_name(d), t)
        self.problem(c, 'reference to %s' % d.kind)
        return E(d.spelling, t)

    def local_ref(self, d):
        k = decl_key(d)
        if k not in self.locals:
            self.problem(d, 'local %s used before its declaration' % d.spelling)
            return d.spelling
        nm = self.locals[k]
        if self.lkind.get(k) == 'slot':
            return '%s[]' % nm
        return nm

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                return E(self.zero(c.type), canon(c.type))
            return self.ex(ch[0])
        inner = ch[0]
        it, ct = canon(inner.type), canon(c.type)
        e = self.ex(inner)
        if it == ct and not (it.kind in (T.CONSTANTARRAY,) and ct.kind == T.POINTER):
            return e
        if ct.kind == T.POINTER and it.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if e.strlit is not None:
                return E(self.strlit_ptr(e.strlit), ct)
            return E(e.code, ct)                  # array decay: the code already is the element pointer
        if ct.kind == T.POINTER and it.kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return E(self.fn_id_code(e.code), ct)
        return self.converted(e, ct)

    def x_CSTYLE_CAST_EXPR(self, c):
        inner = kids(c)[-1]
        t = canon(c.type)
        if t.kind == T.VOID:
            e = self.ex(inner)
            return E(e.code, t)
        s = strip(inner)
        if s.kind == K.CALL_EXPR and s.spelling in ('malloc', 'calloc', 'realloc') and t.kind == T.POINTER:
            e = self.ex(inner)
            return E(self.conv(e, t), t)
        e = self.ex(inner)
        it = canon(inner.type)
        if t.kind == T.POINTER and it.kind in (T.CONSTANTARRAY,):
            return E(self.conv(e, t), t)
        return self.converted(e, t)

    def x_CXX_UNARY_EXPR(self, c):
        """sizeof: a C constant, or Mojo's size for anything holding a record"""
        t = canon(c.type)
        toks = [x.spelling for x in c.get_tokens()]
        target = None
        for ch in c.get_children():
            if ch.kind == K.TYPE_REF:
                target = ch.type
            elif target is None:
                target = ch.type
        if toks and toks[0] == 'sizeof' and target is not None and self.has_record(target):
            return E(self.sizeof_code(target), t)
        if toks and toks[0] == 'sizeof' and target is None:
            # sizeof(type) with a builtin type: clang gives no child
            pass
        v = evaluate(c)
        if v is None:
            self.problem(c, 'sizeof without a value')
            return E('UInt64(0)', t, lit=0)
        return E(self.int_lit(v[1], 'UInt64'), t, lit=v[1])

    # ---------------------------------------------------------------- lvalues and places
    def place(self, c):
        """Mojo place (assignable) for the C lvalue c"""
        s = c
        while s.kind == K.PAREN_EXPR:
            s = kids(s)[0]
        if s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1 and canon(kids(s)[0].type) == canon(s.type):
            return self.place(kids(s)[0])
        return self.ex(s).code

    lv = place

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, ixe = kids(c)
        if info(base.type)[0] == 'int':
            base, ixe = ixe, base
        t = canon(c.type)
        b = self.array_base(base)
        if t.kind == T.CONSTANTARRAY:
            n = self.flat(t)[1]
            return E('%s.unsafe_offset(%s)' % (self.paren(b), self.index(ixe, n)), t)
        return E('%s[unsafe_offset=%s]' % (self.paren(b), self.index(ixe)), t)

    def index(self, ixe, mul=1):
        e = self.ex(ixe)
        if e.isbool:
            code = 'Int(Int32(%s))' % e.code
        elif e.lit is not None:
            return str(e.lit * mul)
        else:
            i = info(e.t)
            if i[0] != 'int':
                self.problem(ixe, 'non-integer index')
            code = 'Int(%s)' % e.code
        return code if mul == 1 else '%s * %d' % (code, mul)

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        f = c.referenced
        fn = f.spelling
        bt = canon(base.type)
        b = self.ex(base).code
        if bt.kind == T.POINTER:
            obj = '%s[]' % self.paren(b)
            rt_ = canon(bt.get_pointee())
        else:
            obj = b
            rt_ = bt
        ft = canon(c.type)
        if record_name(rt_) in self.F.unions:
            # a union member: the union's raw words read as the member's type
            if ft.kind == T.CONSTANTARRAY:
                return E('rt.addr(%s).unsafe_bitcast[%s]()' % (obj, self.mt(self.flat(ft)[0])), ft)
            return E('rt.addr(%s).unsafe_bitcast[%s]()[]' % (obj, self.mt(ft)), ft)
        if ft.kind == T.CONSTANTARRAY:
            return E('rt.addr(%s.%s).unsafe_bitcast[%s]()' % (obj, fn, self.mt(self.flat(ft)[0])), ft)
        return E('%s.%s' % (obj, fn), ft)

    # ---------------------------------------------------------------- unary
    def x_UNARY_OPERATOR(self, c):
        op = unop(c)
        a = kids(c)[0]
        t = canon(c.type)
        if op == '&':
            return E(self.address_of(a), t)
        if op == '*':
            ai = info(a.type)
            if ai[0] == 'ptr' and canon(ai[1]).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
                return self.ex(a)
            if t.kind == T.CONSTANTARRAY:
                return E(self.val(a), t)           # *p of a pointer to an array: the same address
            return E('%s[]' % self.paren(self.val(a)), t)
        if op == '!':
            return E('(not %s)' % self.paren(self.cond(a)), t, isbool=True)
        if op in ('pre++', 'pre--', 'post++', 'post--'):
            return self.incdec_expr(a, op, t)
        e = self.ex(a)
        i = info(t)
        if op == '+':
            return E(self.conv(e, t), t, lit=e.lit)
        if op == '-':
            if i[0] == 'int':
                if e.lit is not None:
                    v = wrap_int(-e.lit, i[2], i[3])
                    return E(self.int_lit(v, INT_T[i[1]]), t, lit=v)
                return E('(-%s)' % self.paren(self.conv(e, t)), t)
            if e.lit is not None:
                v = -e.lit
                return E(self.flt_text(v, i[2]), t, lit=v)
            return E('(-%s)' % self.paren(self.conv(e, t)), t)
        if op == '~':
            if e.lit is not None:
                v = wrap_int(~e.lit, i[2], i[3])
                return E(self.int_lit(v, INT_T[i[1]]), t, lit=v)
            return E('(~%s)' % self.paren(self.conv(e, t)), t)
        self.problem(c, 'unary ' + op)
        return e

    def address_of(self, a):
        sa = a
        while sa.kind == K.PAREN_EXPR or (sa.kind == K.UNEXPOSED_EXPR and len(kids(sa)) == 1 and canon(kids(sa)[0].type) == canon(sa.type)):
            sa = kids(sa)[0]
        st = canon(sa.type)
        if st.kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return self.fn_id_code(self.ex(sa).code)
        if sa.kind == K.UNARY_OPERATOR and unop(sa) == '*':
            return self.val(kids(sa)[0])
        if st.kind == T.CONSTANTARRAY:
            return self.ex(sa).code                # an array object: its code is its address
        if sa.kind == K.DECL_REF_EXPR and sa.referenced is not None:
            d = sa.referenced
            k = decl_key(d)
            if k in self.locals:
                if self.lkind.get(k) == 'slot':
                    return self.locals[k]
                self.problem(sa, 'address of a local not in a stack slot: %s' % d.spelling)
                return 'rt.addr(%s)' % self.locals[k]
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ixe = kids(sa)
            if info(base.type)[0] == 'int':
                base, ixe = ixe, base
            b = self.array_base(base)
            ix = self.index(ixe)
            return b if ix == '0' else '%s.unsafe_offset(%s)' % (self.paren(b), ix)
        return 'rt.addr(%s)' % self.place(sa)

    def incdec_expr(self, a, op, t):
        i = info(t)
        pl = self.place(a)
        kind = op.split('+')[0].split('-')[0] if False else op
        pre = op.startswith('pre')
        inc = '++' in op
        if i[0] == 'ptr':
            fn = 'rt.%s%sp' % ('pre' if pre else 'post', 'inc' if inc else 'dec')
            return E('%s(%s)' % (fn, pl), t)
        fn = 'rt.%s%s' % ('pre' if pre else 'post', 'inc' if inc else 'dec')
        return E('%s(%s)' % (fn, pl), t)

    # ---------------------------------------------------------------- binary
    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        t = canon(c.type)
        if op == '=':
            return self.assign_expr(l, r)
        if op in ('&&', '||'):
            return E('(%s %s %s)' % (self.cond(l), 'and' if op == '&&' else 'or', self.cond(r)), t, isbool=True)
        if op == ',':
            self.problem(c, 'comma operator used as a value')
            return self.ex(r)
        li, ri = info(l.type), info(r.type)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            le, re_ = self.ex(l), self.ex(r)
            if li[0] in ('ptr', 'arr', 'fn') or ri[0] in ('ptr', 'arr', 'fn'):
                return self.ptr_compare(op, l, r, le, re_, t)
            a, b = self.conv(le, l.type), self.conv(re_, r.type)
            return E('(%s %s %s)' % (a, op, b), t, isbool=True)
        if li[0] in ('ptr', 'arr') or ri[0] in ('ptr', 'arr'):
            return self.ptr_arith(op, l, r, t)
        le, re_ = self.ex(l), self.ex(r)
        return self.arith(op, le, re_, t, l.type, r.type)

    def arith(self, op, le, re_, t, lt, rt_):
        i = info(t)
        if op in ('<<', '>>'):
            a = self.conv(le, t)
            if le.lit is not None and re_.lit is not None:
                v = wrap_int(le.lit << re_.lit if op == '<<' else le.lit >> re_.lit, i[2], i[3])
                return E(self.int_lit(v, INT_T[i[1]]), t, lit=v)
            if re_.lit is not None and 0 <= re_.lit < i[2]:
                return E('(%s %s %s)' % (a, op, self.int_lit(re_.lit, INT_T[i[1]])), t)
            b = self.conv(re_, self.int_t)
            fn = {('Int32', '<<'): 'rt.shl32', ('Int32', '>>'): 'rt.shr32', ('Int64', '<<'): 'rt.shl64',
                  ('Int64', '>>'): 'rt.shr64', ('UInt32', '<<'): 'rt.shlu32', ('UInt32', '>>'): 'rt.shru32',
                  ('UInt64', '<<'): 'rt.shlu64', ('UInt64', '>>'): 'rt.shru64'}[(INT_T[i[1]], op)]
            return E('%s(%s, %s)' % (fn, a, b), t)
        a = self.conv(le, t)
        b = self.conv(re_, t)
        if i[0] == 'int':
            if le.lit is not None and re_.lit is not None and not le.isbool and not re_.isbool:
                x = wrap_int(le.lit, i[2], i[3])
                y = wrap_int(re_.lit, i[2], i[3])
                v = None
                if op == '+':
                    v = x + y
                elif op == '-':
                    v = x - y
                elif op == '*':
                    v = x * y
                elif op in ('/', '%') and y != 0:
                    q = abs(x) // abs(y)
                    if (x < 0) != (y < 0):
                        q = -q
                    v = q if op == '/' else x - q * y
                elif op == '&':
                    v = x & y
                elif op == '|':
                    v = x | y
                elif op == '^':
                    v = x ^ y
                if v is not None:
                    v = wrap_int(v, i[2], i[3])
                    return E(self.int_lit(v, INT_T[i[1]]), t, lit=v)
            if op in ('+', '-', '*', '&', '|', '^'):
                return E('(%s %s %s)' % (a, op, b), t)
            m = INT_T[i[1]]
            if op == '/':
                if i[3]:
                    return E('rt.idiv%d(%s, %s)' % (i[2], a, b) if i[2] in (32, 64) else '%s(rt.idiv32(Int32(%s), Int32(%s)))' % (m, a, b), t)
                return E('(%s // %s)' % (a, b), t)
            if op == '%':
                if i[3]:
                    return E('rt.irem%d(%s, %s)' % (i[2], a, b) if i[2] in (32, 64) else '%s(rt.irem32(Int32(%s), Int32(%s)))' % (m, a, b), t)
                return E('(%s %% %s)' % (a, b), t)
        if i[0] == 'flt':
            if op in ('+', '-', '*', '/'):
                return E('(%s %s %s)' % (a, op, b), t)
        self.problem(None, 'arithmetic %s on %s' % (op, t.spelling))
        return E('(%s %s %s)' % (a, op, b), t)

    def ptr_compare(self, op, l, r, le, re_, t):
        li, ri = info(l.type), info(r.type)
        lfn = li[0] == 'fn' or self.mt(l.type) == 'Int32' if li[0] in ('ptr', 'fn') else False
        rfn = ri[0] == 'fn' or self.mt(r.type) == 'Int32' if ri[0] in ('ptr', 'fn') else False
        if lfn or rfn:
            def fcode(e, ty):
                c = self.conv(e, ty)
                if (info(ty)[0] == 'int' and e.lit == 0) or 'rt.null[' in c:
                    return 'Int32(0)'
                return c
            return E('(%s %s %s)' % (fcode(le, l.type), op, fcode(re_, r.type)), t, isbool=True)
        if li[0] == 'int' and le.lit == 0:
            x = self.conv(re_, r.type)
            return E('rt.isnull(%s)' % x if op == '==' else '(not rt.isnull(%s))' % x, t, isbool=True)
        if ri[0] == 'int' and re_.lit == 0:
            x = self.conv(le, l.type)
            return E('rt.isnull(%s)' % x if op == '==' else '(not rt.isnull(%s))' % x, t, isbool=True)
        a, b = self.conv(le, l.type), self.conv(re_, r.type)
        return E('(Int(%s) %s Int(%s))' % (a, op, b), t, isbool=True)

    def ptr_arith(self, op, l, r, t):
        li, ri = info(l.type), info(r.type)
        if op == '-' and li[0] in ('ptr', 'arr') and ri[0] in ('ptr', 'arr'):
            ty = canon(l.type)
            el = canon(info(ty)[1])
            size = 'size_of[%s]()' % self.pointee_mt(ty) if el.kind != T.VOID else '1'
            return E('rt.pdiff(%s, %s, %s * %d)' % (self.val(l), self.val(r), size, self.stride(ty)), t)
        if li[0] in ('ptr', 'arr'):
            p, n, neg = l, r, op == '-'
        else:
            p, n, neg = r, l, False
        pc = self.val(p) if info(p.type)[0] == 'ptr' else self.conv(self.ex(p), t)
        st = self.stride(canon(p.type))
        ne = self.ex(n)
        if ne.lit is not None and not ne.isbool:
            v = (-ne.lit if neg else ne.lit) * st
            return E('%s.unsafe_offset(%d)' % (self.paren(pc), v), t)
        nc = 'Int(%s)' % self.conv(ne, n.type)
        if st != 1:
            nc = '%s * %d' % (nc, st)
        return E('%s.unsafe_offset(%s%s)' % (self.paren(pc), '-' if neg else '', nc if not neg else '(%s)' % nc), t)

    # ---------------------------------------------------------------- assignment
    def assign_expr(self, l, r):
        t = canon(l.type)
        v = self.val(r, t)
        if info(t)[0] == 'rec':
            v = '%s.copy()' % self.paren(v)
        return E('rt.set(%s, %s)' % (self.place(l), v), t)

    def compound_value(self, c, cur):
        """Mojo code for the new value of l in l op= r, where cur is code reading l"""
        l, r = kids(c)
        common, op = self.compound_parts(c)
        lt = canon(l.type)
        li = info(lt)
        if li[0] == 'ptr':
            ne = self.ex(r)
            st = self.stride(lt)
            if ne.lit is not None:
                v = ne.lit * st
                return '%s.unsafe_offset(%d)' % (self.paren(cur), v if op == '+' else -v)
            nc = 'Int(%s)' % self.conv(ne, r.type)
            if st != 1:
                nc = '%s * %d' % (nc, st)
            return '%s.unsafe_offset(%s%s)' % (self.paren(cur), '' if op == '+' else '-', nc if op == '+' else '(%s)' % nc)
        le = E(cur, lt)
        re_ = self.ex(r)
        if op in ('<<', '>>'):
            v = self.arith(op, E(self.conv(le, common), common), re_, common, common, r.type)
        else:
            v = self.arith(op, E(self.conv(le, common), common), E(self.conv(re_, common), common), common, common, common)
        return self.conv(v, lt)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        l, r = kids(c)
        t = canon(l.type)
        if not self.simple_lv(l):
            self.problem(c, 'compound assignment as a value on a place with side effects')
        pl = self.place(l)
        return E('rt.set(%s, %s)' % (pl, self.compound_value(c, pl)), t)

    # ---------------------------------------------------------------- ?:
    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        t = canon(c.type)
        if t.kind == T.VOID:
            self.problem(c, 'void ?: used as a value')
            return E('None', t)
        ea, eb = self.ex(a), self.ex(b)
        return E('(%s if %s else %s)' % (self.conv(ea, t), self.cond(cc), self.conv(eb, t)), t)

    # ---------------------------------------------------------------- calls
    def x_CALL_EXPR(self, c):
        name = c.spelling
        args = list(c.get_arguments())
        d = c.referenced
        t = canon(c.type)
        if d is not None and d.kind == K.FUNCTION_DECL:
            fdef = self.func_def(d)
            if fdef is None:
                return self.libc(c, name, args, d)
            ptypes = [p.type for p in fdef.get_arguments()]
            codes = [self.arg_code(a, pt) for a, pt in zip(args, ptypes)]
            return E('%s(%s)' % (self.fname[self.def_key(fdef)], ', '.join(['G'] + codes)), t)
        callee = kids(c)[0]
        ct = canon(strip(callee).type)
        ft = canon(ct.get_pointee()) if ct.kind == T.POINTER else ct
        ptypes = list(ft.argument_types())
        codes = [self.arg_code(a, pt) for a, pt in zip(args, ptypes)]
        fe = self.ex(callee)
        fid = self.conv(fe, ct) if ct.kind == T.POINTER else fe.code
        disp = self.dispatcher(ft)
        return E('%s(%s)' % (disp, ', '.join(['G', fid] + codes)), t)

    def arg_code(self, a, pt):
        v = self.val(a, pt)
        if info(pt)[0] == 'rec':
            v = '%s.copy()' % self.paren(v)
        return v

    def dispatcher(self, ft):
        ft = canon(ft)
        sig = (tuple(self.mt(x) for x in ft.argument_types()), self.mt(ft.get_result()))
        if sig not in self.fp_sigs:
            self.fp_sigs[sig] = ('__fpcall%d' % (len(self.fp_sigs) + 1), ft)
        return self.fp_sigs[sig][0]

    def libc(self, c, name, args, d):
        t = canon(c.type)
        ptypes = list(canon(d.type).argument_types())
        if name in ('fabs', 'sqrt', 'floor', 'ceil'):
            a = self.val(args[0], ptypes[0])
            return E('%s(%s)' % ({'fabs': 'rt.fabs'}.get(name, name), a), t)
        if name in VARIADIC:
            nfix = VARIADIC[name]
            fixed = [self.val(a, pt) for a, pt in zip(args[:nfix], ptypes)]
            rest = [self.vararg(a, name == 'sscanf') for a in args[nfix:]]
            return E('rt.%s(%s)' % (name, ', '.join(fixed + rest)), t)
        if name not in LIBC:
            self.problem(c, 'library function ' + name)
        codes = [self.val(a, pt) for a, pt in zip(args, ptypes)]
        if name in RT_STATE:
            codes = ['G[].R_'] + codes
        if name == 'fseeko':
            name = 'fseek'
        return E('rt.%s(%s)' % (name, ', '.join(codes)), t)

    def vararg(self, a, scanf):
        e = self.ex(a)
        at = canon(a.type)
        i = info(at)
        if scanf:
            if i[0] in ('ptr', 'arr'):
                pt = canon(i[1]) if i[0] == 'ptr' else canon(self.flat(at)[0])
                pi = info(pt)
                code = self.conv(e, at) if i[0] == 'ptr' else e.code
                if pt.kind in (T.CHAR_S, T.SCHAR, T.CHAR_U):
                    return 'rt.tps(%s)' % code
                m = {'i32': 'rt.tpi', 'i64': 'rt.tpl', 'u32': 'rt.tpu', 'f64': 'rt.tpd', 'f32': 'rt.tpf'}.get(pi[1])
                if m is None:
                    self.problem(a, 'sscanf target %s' % at.spelling)
                    return code
                return '%s(%s)' % (m, code)
            self.problem(a, 'sscanf target %s' % at.spelling)
            return e.code
        code = self.conv(e, at)
        if i[0] == 'int':
            return {'i32': 'rt.ai', 'i64': 'rt.al', 'u32': 'rt.au', 'u64': 'rt.aul'}.get(i[1], 'rt.ai') + '(%s)' % (
                code if i[1] in ('i32', 'i64', 'u32', 'u64') else 'Int32(%s)' % code)
        if i[0] == 'flt':
            return 'rt.ad(%s)' % (code if i[2] == 64 else 'Float64(%s)' % code)
        if i[0] in ('ptr', 'arr'):
            return 'rt.astr(%s)' % code
        self.problem(a, 'printf argument %s' % at.spelling)
        return code

    # ================================================================== statements
    def stmt(self, c, ind):
        k = c.kind
        p = '    ' * ind
        if k == K.COMPOUND_STMT:
            return self.block_items(kids(c), ind)
        if k == K.DECL_STMT:
            out = []
            for d in kids(c):
                out += self.local_decl(d, ind)
            return out
        if k == K.IF_STMT:
            return self.if_stmt(c, ind)
        if k == K.WHILE_STMT:
            ch = kids(c)
            self.loops.append(('while', None))
            out = [p + 'while %s:' % self.loop_cond(ch[0])] + self.body(ch[1], ind + 1)
            self.loops.pop()
            return out
        if k == K.DO_STMT:
            ch = kids(c)
            cnd = self.loop_cond(ch[1])
            self.loops.append(('do', cnd))
            body = self.body(ch[0], ind + 1)
            self.loops.pop()
            out = [p + 'while True:'] + body
            if self.completes(ch[0]) and cnd != 'True':
                out += [p + '    if not %s:' % self.paren(cnd), p + '        break']
            return out
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            ctx = self.loops[-1] if self.loops else None
            if ctx and ctx[0] == 'switch-if':
                return []
            return [p + 'break']
        if k == K.CONTINUE_STMT:
            return self.continue_stmt(ind)
        if k == K.RETURN_STMT:
            ch = kids(c)
            pop = [p + 'G[].R_[].sp = __sp'] if self.has_slots else []
            if not ch:
                return pop + [p + 'return']
            if canon(self.cur_ret).kind == T.VOID:
                return [p + x for x in self.expr_stmt(ch[0])] + pop + [p + 'return']
            v = self.val(ch[0], self.cur_ret)
            if info(self.cur_ret)[0] == 'rec':
                v = '%s.copy()' % self.paren(v)
            if self.has_slots:
                return [p + '__rv = %s' % v] + pop + [p + 'return __rv']
            return [p + 'return %s' % v]
        if k == K.NULL_STMT:
            return []
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unhandled statement %s' % k.name)
            return []
        return [p + x for x in self.expr_stmt(c)]

    def body(self, c, ind):
        lines = ZigEmitter.body(self, c, ind)
        if not [l for l in lines if l.strip()]:
            return ['    ' * ind + 'pass']
        return lines

    def loop_cond(self, c):
        if c is None:
            return 'True'
        v = evaluate(strip(c)) if strip(c).kind in (K.INTEGER_LITERAL, K.FLOATING_LITERAL) else None
        if v is not None and v[1] != 0:
            return 'True'
        return self.cond(c)

    def if_stmt(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        out = [p + 'if %s:' % self.cond(ch[0])]
        out += self.body(ch[1], ind + 1)
        e = ch[2] if len(ch) > 2 else None
        while e is not None:
            if e.kind == K.IF_STMT:
                ec = kids(e)
                out.append(p + 'elif %s:' % self.cond(ec[0]))
                out += self.body(ec[1], ind + 1)
                e = ec[2] if len(ec) > 2 else None
            else:
                out.append(p + 'else:')
                out += self.body(e, ind + 1)
                e = None
        return out

    def continue_stmt(self, ind):
        p = '    ' * ind
        out = []
        for i in range(len(self.loops) - 1, -1, -1):
            kind, info_ = self.loops[i]
            if kind == 'switch-loop':
                self.switch_continue[-1] = True
                return [p + '__cont = True', p + 'break']
            if kind == 'switch-if':
                continue
            if kind == 'for' and info_:
                out += [p + x for x in info_]
            elif kind == 'do':
                if info_ == 'True':
                    return out + [p + 'continue']
                return [p + 'if not %s:' % self.paren(info_), p + '    break', p + 'continue']
            return out + [p + 'continue']
        return out + [p + 'continue']

    def for_stmt(self, c, ind):
        p = '    ' * ind
        init, cond, inc, body = self.for_parts(c)
        out = []
        if init is not None:
            if init.kind == K.DECL_STMT:
                for d in kids(init):
                    out += self.local_decl(d, ind)
            else:
                out += [p + x for x in self.expr_stmt(init)]
        cs = self.loop_cond(cond)
        incs = self.expr_stmt(inc) if inc is not None else []
        self.loops.append(('for', incs))
        b = self.body(body, ind + 1)
        self.loops.pop()
        out.append(p + 'while %s:' % cs)
        out += b
        if self.completes(body):
            out += [p + '    ' + x for x in incs]
        elif incs and self.has_continue(body):
            pass        # every continue already ran the increment
        return out

    def switch(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        e = self.ex(ch[0])
        sel = self.conv(e, self.promoted(ch[0].type)) if not e.isbool else 'Int32(%s)' % e.code
        body = ch[-1]
        items = kids(body) if body.kind == K.COMPOUND_STMT else [body]
        sections = []
        for it in items:
            if it.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                labels = []
                x = it
                while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                    xc = kids(x)
                    if x.kind == K.CASE_STMT:
                        labels.append(self.case_code(xc[0], ch[0].type))
                        x = xc[1]
                    else:
                        labels.append(None)
                        x = xc[0]
                if sections and not sections[-1][1]:
                    sections[-1][0].extend(labels)
                else:
                    sections.append([labels, []])
                sections[-1][1].append(x)
            elif sections:
                sections[-1][1].append(it)
        self.nlabel += 1
        sv = '__sw%d' % self.nlabel
        self.hoisted.append((sv, self.mt(self.promoted(ch[0].type)), self.zero(self.promoted(ch[0].type))))
        pre = [p + '%s = %s' % (sv, sel)]
        allvals = [l for sec in sections for l in sec[0] if l is not None]

        def test(labels):
            vals = [l for l in labels if l is not None]
            conds = ['%s == %s' % (sv, v) for v in vals]
            if None in labels:
                conds.append(' and '.join('%s != %s' % (sv, v) for v in allvals) if allvals else 'True')
            return ' or '.join(conds) if len(conds) == 1 else ' or '.join('(%s)' % x for x in conds)

        simple = all(self.ends_clean(sec[1]) for sec in sections[:-1]) and all(not self.inner_break(sec[1]) for sec in sections)
        if simple:
            out = list(pre)
            first = True
            ordered = [s for s in sections if None not in s[0]] + [s for s in sections if None in s[0]]
            for labels, stmts in ordered:
                if None in labels:
                    head = (p + 'else:') if not first else (p + 'if True:')
                else:
                    head = p + ('if %s:' if first else 'elif %s:') % test(labels)
                first = False
                self.loops.append(('switch-if', None))
                lines = self.block_items(stmts, ind + 1)
                self.loops.pop()
                if not [l for l in lines if l.strip()]:
                    lines = [p + '    pass']
                out += [head] + lines
            return out
        # general case: a one-pass loop; a C break leaves it, fall-through goes on through a flag
        self.nlabel += 1
        ft = '__ft%d' % self.nlabel
        self.hoisted.append((ft, 'Bool', 'False'))
        self.switch_continue.append(False)
        self.loops.append(('switch-loop', None))
        out = list(pre) + [p + '%s = False' % ft, p + 'while True:']
        for si, (labels, stmts) in enumerate(sections):
            lines = self.block_items(stmts, ind + 2)
            out.append(p + '    if %s or %s:' % (ft, self.paren(test(labels))))
            out += lines or [p + '        pass']
            if self.completes_list(stmts):
                out.append(p + '        %s = True' % ft)
        out.append(p + '    break')
        self.loops.pop()
        if self.switch_continue.pop():
            if not any(h[0] == '__cont' for h in self.hoisted):
                self.hoisted.append(('__cont', 'Bool', 'False'))
            out = [p + '__cont = False'] + out + [p + 'if __cont:'] + self.continue_stmt(ind + 1)
        return out

    def case_code(self, x, st):
        e = self.ex(x)
        pt = self.promoted(st)
        if e.lit is not None:
            i = info(pt)
            v = wrap_int(e.lit, i[2], i[3])
            return self.int_lit(v, INT_T[i[1]])
        return self.conv(e, pt)

    def ends_clean(self, stmts):
        """the section cannot fall through: it ends with a break, or control cannot reach its end"""
        if not stmts:
            return False
        last = stmts[-1]
        if last.kind in (K.BREAK_STMT, K.RETURN_STMT):
            return True
        if not self.completes_list(stmts) and not self.has_continue_or_break_out(last):
            return True
        if last.kind == K.COMPOUND_STMT:
            return self.ends_clean(kids(last))
        if last.kind == K.IF_STMT:
            ch = kids(last)
            return len(ch) == 3 and self.ends_clean([ch[1]]) and self.ends_clean([ch[2]])
        return False

    def has_continue_or_break_out(self, c):
        """a continue anywhere, or a break at this switch's level, inside c (not inside a nested loop)"""
        def walk(x, in_switch):
            if x.kind == K.CONTINUE_STMT:
                return True
            if x.kind == K.BREAK_STMT and not in_switch:
                return True
            if x.kind in (K.FOR_STMT, K.WHILE_STMT, K.DO_STMT):
                return False
            if x.kind == K.SWITCH_STMT:
                return any(walk(y, True) for y in kids(x))
            return any(walk(y, in_switch) for y in kids(x))
        return walk(c, False)

    def inner_break(self, stmts):
        """a switch-level break that is not the final statement of its section"""
        def has_break(c):
            if c.kind == K.BREAK_STMT:
                return True
            if c.kind in (K.FOR_STMT, K.WHILE_STMT, K.DO_STMT, K.SWITCH_STMT):
                return False
            return any(has_break(x) for x in kids(c))
        for i, s_ in enumerate(stmts):
            last = i == len(stmts) - 1
            if s_.kind == K.BREAK_STMT:
                if not last:
                    return True
                continue
            if s_.kind == K.COMPOUND_STMT:
                if self.inner_break(kids(s_)):
                    return True
                continue
            if s_.kind == K.IF_STMT and last and self.ends_clean([s_]):
                ch = kids(s_)
                if self.inner_break([ch[1]]) or (len(ch) == 3 and self.inner_break([ch[2]])):
                    return True
                continue
            if has_break(s_):
                return True
        return False

    # ---------------------------------------------------------------- expression statements
    def expr_stmt(self, c):
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1 and canon(kids(s)[0].type) == canon(s.type)):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and canon(s.type).kind == T.VOID:
            inner = kids(s)[-1]
            si = strip(inner)
            if si.kind in (K.DECL_REF_EXPR,):
                return []
            return self.expr_stmt(inner)
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            v = self.val(r, l.type)
            if info(l.type)[0] == 'rec':
                v = '%s.copy()' % self.paren(v)
            return ['%s = %s' % (self.place(l), v)]
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmt(l) + self.expr_stmt(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            l, r = kids(s)
            pl = self.place(l)
            op = binop(s)[:-1]
            lt = canon(l.type)
            li = info(lt)
            common, _ = self.compound_parts(s)
            if self.simple_lv(l):
                if li[0] in ('int', 'flt') and canon(common) == lt and op in ('+', '-', '*') + (('/',) if li[0] == 'flt' else ()):
                    return ['%s %s= %s' % (pl, op, self.val(r, lt))]
                return ['%s = %s' % (pl, self.compound_value(s, pl))]
            self.problem(s, 'compound assignment to a place with side effects')
            return ['%s = %s' % (pl, self.compound_value(s, pl))]
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            i = info(a.type)
            pl = self.place(a)
            inc = '++' in unop(s)
            if i[0] == 'ptr':
                return ['%s = %s.unsafe_offset(%d)' % (pl, self.paren(pl), self.stride(canon(a.type)) * (1 if inc else -1))]
            if i[0] == 'flt':
                return ['%s %s= %s(1.0)' % (pl, '+' if inc else '-', FLT_T[i[1]])]
            return ['%s %s= 1' % (pl, '+' if inc else '-')]
        if s.kind == K.CONDITIONAL_OPERATOR:
            cc, a, b = kids(s)
            la, lb = self.expr_stmt(a) or ['pass'], self.expr_stmt(b) or ['pass']
            return ['if %s:' % self.cond(cc)] + ['    ' + x for x in la] + ['else:'] + ['    ' + x for x in lb]
        if s.kind == K.DECL_REF_EXPR:
            return []
        e = self.ex(s)
        if canon(s.type).kind == T.VOID:
            return [e.code]
        if e.lit is not None and s.kind != K.CALL_EXPR:
            return []
        return ['_ = %s' % e.code]

    # ---------------------------------------------------------------- declarations
    def declare_local(self, d, mty, kind):
        n = d.spelling
        nn, i = n, 2
        while nn in self.used_names or nn in self.top or nn in MOJO_KEYWORDS or nn.startswith('__'):
            nn = '%s_%d' % (n, i)
            i += 1
        self.used_names.add(nn)
        self.locals[decl_key(d)] = nn
        self.lkind[decl_key(d)] = kind
        return nn

    def local_kind(self, d):
        t = canon(d.type)
        if t.kind == T.CONSTANTARRAY:
            return 'arr'
        if t.kind == T.RECORD:
            return 'slot'
        if decl_key(d) in self.addr_taken:
            return 'slot'
        return 'var'

    def local_decl(self, d, ind):
        p = '    ' * ind
        if d.kind != K.VAR_DECL:
            return []
        if d.storage_class == front.ci.StorageClass.EXTERN:
            return []
        if d.storage_class == front.ci.StorageClass.STATIC:
            self.static_locals.append((d, self.cur_file))
            return []
        t = canon(d.type)
        it = var_init(d)
        kind = self.local_kind(d)
        name = self.declare_local(d, None, kind)
        if kind == 'arr':
            base, n = self.flat(t)
            self.slots.append((name, self.mt(base), n))
            if it is None:
                return []
            return [p + x for x in self.array_init(name, t, it)]
        if kind == 'slot':
            self.slots.append((name, self.mt(t), 1))
            if it is None:
                return []
            v = self.init_value(it, t)
            if info(t)[0] == 'rec' and strip(it).kind != K.INIT_LIST_EXPR:
                v = '%s.copy()' % self.paren(v)
            return [p + '%s[] = %s' % (name, v)]
        self.hoisted.append((name, self.mt(t), self.zero(t)))
        if it is None:
            return []
        return [p + '%s = %s' % (name, self.init_value(it, t))]

    def init_value(self, it, t):
        t = canon(t)
        s = strip(it)
        if s.kind == K.INIT_LIST_EXPR:
            if info(t)[0] == 'rec':
                return self.record_init(s, t)
            items = kids(s)
            if len(items) == 1:
                return self.val(items[0], t)
            self.problem(s, 'init list for %s' % t.spelling)
            return self.zero(t)
        return self.val(it, t)

    def record_init(self, c, t):
        fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
        items = kids(c)
        if any(canon(f.type).kind == T.CONSTANTARRAY for f in fields) or record_name(t) in self.F.unions:
            self.problem(c, 'record initializer with an array field')
        args = []
        for k, f in enumerate(fields):
            if k < len(items):
                args.append(self.init_value(items[k], f.type))
            else:
                args.append(self.zero(f.type))
        return '%s.c_init(%s)' % (self.rec(t), ', '.join(args))

    def array_init(self, ptr, t, it):
        """statements filling the array at pointer code ptr (C type t) from initializer it"""
        t = canon(t)
        s = strip(it)
        base, n = self.flat(t)
        if s.kind == K.STRING_LITERAL:
            b = self.string_bytes(s)
            return ['rt.init_chars(%s, %s, %d)' % (ptr, self.strlit_ptr(b), min(len(b), n))]
        if s.kind != K.INIT_LIST_EXPR:
            self.problem(s, 'array initializer')
            return []
        out = []
        self.flat_items(s, t, ptr, 0, out)
        return out

    def flat_items(self, c, t, ptr, off, out):
        """assignments for the init list c of the array type t starting at flat offset off"""
        t = canon(t)
        et = canon(t.element_type)
        items = kids(c)
        n = t.element_count
        if (et.kind == T.POINTER and front.is_char(et.get_pointee()) and items
                and strip(items[-1]).kind == K.STRING_LITERAL and len(items) == n):
            self.defects.append('%s:%d string table without NULL sentinel' % (
                os.path.basename(c.location.file.name), c.location.line))
        sub = self.flat(et)[1] if et.kind == T.CONSTANTARRAY else 1
        for k, x in enumerate(items):
            sx = strip(x)
            if et.kind == T.CONSTANTARRAY:
                if sx.kind == K.INIT_LIST_EXPR:
                    self.flat_items(sx, et, ptr, off + k * sub, out)
                elif sx.kind == K.STRING_LITERAL:
                    b = self.string_bytes(sx)
                    out.append('rt.init_chars(%s.unsafe_offset(%d), %s, %d)' % (ptr, off + k * sub, self.strlit_ptr(b), min(len(b), sub)))
                else:
                    self.problem(x, 'array element initializer')
                continue
            v = self.init_value(x, et)
            if info(et)[0] == 'rec' and sx.kind != K.INIT_LIST_EXPR:
                v = '%s.copy()' % self.paren(v)
            out.append('%s[unsafe_offset=%d] = %s' % (ptr, off + k, v))

    # ================================================================== functions
    def scan_addr_taken(self, body, params):
        """locals and parameters whose address is taken (they need a stack slot)"""
        taken = set()

        def walk(x):
            if x.kind == K.UNARY_OPERATOR and unop(x) == '&':
                o = kids(x)[0]
                while o.kind == K.PAREN_EXPR or (o.kind == K.UNEXPOSED_EXPR and len(kids(o)) == 1):
                    o = kids(o)[0]
                if o.kind == K.DECL_REF_EXPR and o.referenced is not None and o.referenced.kind in (K.VAR_DECL, K.PARM_DECL):
                    taken.add(decl_key(o.referenced))
            if x.kind in (K.UNARY_OPERATOR,) and unop(x) in ('pre++', 'pre--', 'post++', 'post--'):
                pass
            for y in x.get_children():
                walk(y)
        walk(body)
        return taken

    def needs_slots(self, body, params, mut):
        """does the function keep any local on the engine's stack (see rt.salloc)?"""
        for prm in params:
            if decl_key(prm) in self.addr_taken or (canon(prm.type).kind == T.RECORD and decl_key(prm) in mut):
                return True
        found = [False]

        def walk(x):
            if found[0]:
                return
            if x.kind == K.VAR_DECL and x.storage_class not in (front.ci.StorageClass.STATIC, front.ci.StorageClass.EXTERN):
                if self.local_kind(x) in ('arr', 'slot'):
                    found[0] = True
                    return
            for y in x.get_children():
                walk(y)
        walk(body)
        return found[0]

    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.lkind = {}
        self.used_names = set()
        self.cur_ret = c.result_type
        self.nlabel = 0
        self.hoisted = []
        self.slots = []
        self.loops = []
        self.switch_continue = []
        self.targets = []
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        self.addr_taken = self.scan_addr_taken(body, params)
        mut, used = self.param_uses(body, params)
        self.has_slots = self.needs_slots(body, params, mut)
        ps = ['G: P[Globals]']
        pre = []
        for prm in params:
            k = decl_key(prm)
            pt = canon(prm.type)
            mty = self.mt(pt)
            if k in self.addr_taken or pt.kind == T.RECORD and k in mut:
                nm = self.declare_local(prm, mty, 'slot')
                ps.append('%s__a: %s' % (nm, mty))
                self.slots.append((nm, mty, 1))
                v = '%s__a' % nm
                pre.append('    %s[] = %s' % (nm, v if pt.kind != T.RECORD else v + '.copy()'))
            else:
                nm = self.declare_local(prm, mty, 'var')
                if k in mut:
                    ps.append('var %s: %s' % (nm, mty))
                else:
                    ps.append('%s: %s' % (nm, mty))
        lines = self.body(body, 1)
        rt_ = self.mt(c.result_type)
        out = ['# %s:%d' % (b, c.location.line),
               'def %s(%s)%s:' % (self.fname[key], ', '.join(ps), '' if rt_ == 'None' else ' -> %s' % rt_)]
        seen = set()
        for nm, mty, z in self.hoisted:
            if nm in seen:
                continue
            seen.add(nm)
            out.append('    var %s: %s = %s' % (nm, mty, z))
        assert bool(self.slots) == self.has_slots, key
        if self.has_slots:
            if rt_ != 'None':
                out.append('    var __rv: %s = %s' % (rt_, self.zero(c.result_type)))
            out.append('    var __sp = G[].R_[].sp')
        for nm, mty, cnt in self.slots:
            out.append('    var %s = rt.salloc[%s](G[].R_, %d)' % (nm, mty, cnt))
        out += pre
        if [l for l in lines if l.strip() not in ('', 'pass')]:
            out += lines
        last = out[-1]
        ends = last.startswith('    return') and not last.startswith('     ')
        if not ends:
            if self.has_slots:
                out.append('    G[].R_[].sp = __sp')
            if rt_ != 'None':
                # C may fall off the end only where it cannot get there; Mojo wants a return at the end anyway
                out.append('    return %s' % self.zero(c.result_type))
        if len(out) == 2:
            out.append('    pass')
        return out

    # ================================================================== records & globals
    def field_type(self, t):
        t = canon(t)
        if t.kind == T.CONSTANTARRAY:
            base, n = self.flat(t)
            return 'StaticTuple[UInt64, (%d * size_of[%s]() + 7) // 8]' % (n, self.mt(base))
        return self.mt(t)

    def field_zero(self, t):
        t = canon(t)
        if t.kind == T.CONSTANTARRAY:
            return '%s(fill=0)' % self.field_type(t)
        return self.zero(t)

    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        rn = self.recname.get(name, name)
        out = ['struct %s(Copyable, Movable):' % rn]
        if name in self.F.unions:
            words = (canon(c.type).get_size() + 7) // 8
            out += ['    var u_: StaticTuple[UInt64, %d]' % words, '',
                    '    def __init__(out self):', '        self.u_ = StaticTuple[UInt64, %d](fill=0)' % words, '']
            return out
        for f in fields:
            out.append('    var %s: %s' % (f.spelling, self.field_type(f.type)))
        out += ['', '    def __init__(out self):']
        for f in fields:
            out.append('        self.%s = %s' % (f.spelling, self.field_zero(f.type)))
        if not fields:
            out.append('        pass')
        out += ['', '    @staticmethod',
                '    def c_init(%s) -> Self:' % ', '.join('%s: %s' % ('a%d' % k, self.field_type(f.type)) for k, f in enumerate(fields)),
                '        var r = Self()']
        for k, f in enumerate(fields):
            if canon(f.type).kind == T.RECORD:
                out.append('        r.%s = a%d.copy()' % (f.spelling, k))
            else:
                out.append('        r.%s = a%d' % (f.spelling, k))
        out += ['        return r^', '']
        return out

    def global_field(self, name, d):
        t = canon(d.type)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            return '    var %s: P[%s]' % (name, self.mt(self.flat(t)[0] if t.kind == T.CONSTANTARRAY else canon(t.element_type)))
        return '    var %s: %s' % (name, self.mt(t))

    def global_init(self, name, d, owner):
        """statements of the start-up function that give the global its C initial value"""
        self.cur_file = owner
        self.locals = {}
        self.lkind = {}
        self.nlabel = 0
        t = canon(d.type)
        it = var_init(d)
        g = 'G[].%s' % name
        out = []
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if t.kind == T.INCOMPLETEARRAY:
                items = kids(strip(it)) if it is not None else []
                base, n = canon(t.element_type), len(items)
                if base.kind == T.POINTER and front.is_char(base.get_pointee()):
                    n += 1      # a string table without its NULL sentinel (EPA defect 1): add one
            else:
                base, n = self.flat(t)
                et = canon(t.element_type)
                if it is not None and strip(it).kind == K.INIT_LIST_EXPR:
                    items = kids(strip(it))
                    if (et.kind == T.POINTER and front.is_char(et.get_pointee()) and items
                            and strip(items[-1]).kind == K.STRING_LITERAL and len(items) == t.element_count):
                        n += 1      # EPA defect 1 (lessons/02): the table gets the NULL the C source forgot
            out.append('%s = rt.calloc(%d, %s).unsafe_bitcast[%s]()' % (g, n, self.sizeof_code(base), self.mt(base)))
            if it is not None:
                if t.kind == T.INCOMPLETEARRAY:
                    for k, x in enumerate(kids(strip(it))):
                        out.append('%s[unsafe_offset=%d] = %s' % (g, k, self.init_value(x, base)))
                else:
                    out += self.array_init(g, t, it)
            return out
        if it is None:
            if t.kind == T.RECORD:
                out.append('%s = %s()' % (g, self.rec(t)))
            return out
        v = self.init_value(it, t)
        if info(t)[0] == 'rec' and strip(it).kind != K.INIT_LIST_EXPR:
            v = '%s.copy()' % self.paren(v)
        out.append('%s = %s' % (g, v))
        return out

    def emit(self, outfile):
        self.int_t = None
        self.double_t = None
        self.float_t = None
        self.cur_decl = None
        self._find_types()
        self.static_locals = []
        self.fkey_by_name = {self.fname[k]: k for k in self.F.funcs}
        funcs = []
        for key, c in self.F.funcs.items():
            try:
                funcs += self.function(key, c) + ['', '']
            except Exception as ex:
                import traceback
                traceback.print_exc()
                self.problems.append('%s:%s CRASH %s' % (key[0], key[1], ex))
        # globals: the Globals struct, and the start-up function that sets their initial values
        gfields = []
        inits = []
        for k, c in self.F.globals.items():
            name = self.gname[k]
            gfields.append(self.global_field(name, c))
            try:
                inits.append((name, self.global_init(name, c, self.F.global_owner[k])))
            except Exception as ex:
                import traceback
                traceback.print_exc()
                self.problems.append('global %s CRASH %s' % (name, ex))
        for d, b in self.static_locals:
            name = self.slname[decl_key(d)]
            gfields.append(self.global_field(name, d))
            inits.append((name, self.global_init(name, d, b)))
        for b_, nm in self.lits.items():
            gfields.append('    var %s: P[Int8]' % nm)
        out = ['# Generated from EPA SWMM 5.2.4 by tools/c2x/emit_mojo.py. Do not edit by hand: fix the',
               '# translator or the runtime (rt.mojo) instead.',
               '', 'from std.memory import stack_allocation', 'from std.math import sqrt, floor, ceil',
               'from std.sys import size_of', 'from std.utils import StaticTuple',
               'from swmm5 import rt', 'from swmm5.rt import P, VP', '']
        out.append('# ---------------------------------------------------------------- constants')
        for n, v in self.F.enum_consts.items():
            out.append('comptime %s: Int32 = %d' % (self.ename[n], v))
        for n, (kind, s) in self.mval.items():
            if kind == 'int':
                v = re.sub(r'[uUlL]+$', '', s)
                if v.lower().startswith('0x'):
                    v = str(int(v, 16))
                elif len(v.lstrip('-')) > 1 and v.lstrip('-').startswith('0'):
                    v = str(int(v, 8))
                out.append('comptime %s = %s' % (self.mname[n], v))
            else:
                txt = s.rstrip('fFlL')
                out.append('comptime %s = %s' % (self.mname[n], flt64_text(float(Fraction(txt)))))
        out += ['', '# ---------------------------------------------------------------- records']
        for name, c in self.F.records.items():
            out += self.record(name, c)
            out.append('')
        out += ['', '# ---------------------------------------------------------------- globals',
                'struct Globals(Movable):', '    var R_: P[rt.RT]'] + gfields + ['']
        out += ['def new_globals() -> P[Globals]:',
                '    """the program\'s globals, zero-filled, with their C initial values"""',
                '    var G = rt.calloc(1, UInt64(size_of[Globals]())).unsafe_bitcast[Globals]()',
                '    G[].R_ = rt.rt_init()']
        nb = 0
        init_funcs = []
        chunk = []
        for name, lines in inits:
            if not lines:
                continue
            chunk += lines
            if len(chunk) > 60:
                init_funcs.append(chunk)
                chunk = []
        if chunk:
            init_funcs.append(chunk)
        for k in range(len(init_funcs)):
            out.append('    __init_globals%d(G)' % k)
        for k, (b_, nm) in enumerate(self.lits.items()):
            out.append('    G[].%s = rt.calloc(%d, 1).unsafe_bitcast[Int8]()' % (nm, len(b_) + 1))
            for q, ch in enumerate(b_):
                out.append('    G[].%s[unsafe_offset=%d] = Int8(%d)' % (nm, q, ch if ch < 128 else ch - 256))
        out += ['    return G', '']
        for k, lines in enumerate(init_funcs):
            out.append('def __init_globals%d(G: P[Globals]):' % k)
            out += ['    ' + l for l in lines]
            out.append('')
        out += ['', '# ---------------------------------------------------------------- functions']
        out += funcs
        # function pointers: one dispatcher per signature over the functions whose address is taken
        out += ['', '# ---------------------------------------------------------------- function pointers']
        byname = {}
        for key, fid in self.fn_ids.items():
            c = self.F.funcs[key]
            ft = canon(c.type)
            sig = (tuple(self.mt(x) for x in ft.argument_types()), self.mt(ft.get_result()))
            byname.setdefault(sig, []).append((fid, self.fname[key]))
        for sig, (dname, ft) in self.fp_sigs.items():
            args, res = sig
            ps = ['G: P[Globals]', '__f: Int32'] + ['a%d: %s' % (k, m) for k, m in enumerate(args)]
            out.append('def %s(%s)%s:' % (dname, ', '.join(ps), '' if res == 'None' else ' -> %s' % res))
            call_args = ', '.join(['G'] + ['a%d' % k for k in range(len(args))])
            for fid, fn in byname.get(sig, []):
                out.append('    if __f == %d:' % fid)
                out.append('        return %s(%s)' % (fn, call_args))
            out.append('    rt.bad_function_pointer(__f)')
            if res != 'None':
                out.append('    return %s' % self.zero(ft.get_result()))
            out.append('')
        open(outfile, 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = MojoEmitter(F)
    out = sys.argv[1] if len(sys.argv) > 1 else 'mojo/swmm5/engine.mojo'
    probs = em.emit(out)
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
