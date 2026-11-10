"""
emit_fsharp.py - EPA SWMM 5.2.4 C  ->  F# (one file, fsharp/gen/Engine.fs: module Swmm5.Engine).

Types follow the C# back end (emit_cs.py), whose analysis this one reuses (pointer modes, names, delegates):
  int/unsigned/long/unsigned long/double/float -> int/uint32/int64/uint64/float/float32; char scalars -> int
  char* / char[]   -> CPtr (a byte array and an offset; p.[i] reads a signed char)
  struct           -> class with `val mutable` fields and Clone() (C's value copy)
  T* indexed       -> T[]       T* used with -> only -> the object reference
  scalar pointer parameters -> byref<T> (passed as &x, &a.[i], &o.f); FILE* -> CFile; void* -> obj
  function pointers -> delegates (FP0...; odesolve's derivative callback is the runtime's OdeDerivs)
  double -> int    -> R.D2I (x86-64's cvttsd2si: NaN or out of range gives INT_MIN)
  exp log log10 pow sin cos tan asin acos atan floor ceil -> Libm.* : the system libm, by P/Invoke

What F# changes, and how the translation keeps C's meaning:
  * no implicit numeric conversion: every conversion clang records is written out (float x, int64 x,
    R.D2I x, ...), so every operation runs at C's types; literals carry their type (1u, 1L, 1UL, 1.0f)
  * assignments are statements: an assignment, ++, -- or op= used as a value becomes
    (let __t = v in x <- __t; __t); a location that would be evaluated twice is first bound to temporaries
    when computing it has side effects
  * no return, break, continue or goto. Each function body is first built as a small tree (blocks, ifs,
    loops, switches, jumps) and restructured, in C's order of evaluation:
      - code after a statement that cannot complete normally is dropped (it is unreachable in C too);
      - `if (c) <jump>; rest` becomes `if c then <jump> else rest` (and the mirror image), so the common
        early return, break and continue need no flag;
      - every other jump sets a flag (__ret for return, __brkN / __cntN for the loop it leaves, __swN for
        a switch it leaves), and the code a jump would skip is wrapped in `if not (flags) then`;
      - a loop tests its flags before its condition (`while not (__brkN || __ret) && cond do`), so C's
        condition is not evaluated after a break; a for loop's increment runs after a continue but not
        after a break or return; do-while evaluates its condition after the body
      - a return in tail position needs no flag: it only stores the value in __rv, which the method returns
    No exception is used for control flow anywhere.
  * switch -> match on integer constants; C's fall-through is written out by appending the next section's
    statements to a section that can complete normally; a final break is dropped, an earlier one is a flag
  * locals are declared once, mutable, at the top of the function (C may jump past a declaration in a
    switch, and F# scopes a let to the rest of its block); parameters the body assigns or whose address
    it takes are copied into mutable locals of the same name
  * functions are static members of one type S (mutually recursive), C globals and static locals are
    module-level mutable values, records one recursive group of classes
  * names that are F# keywords or name F# functions the generated code uses get a trailing _

Written by Claude (Anthropic) for Robert Dickinson; see fsharp/README.md.
"""
import os, re, sys, collections, struct
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import CSEmitter, Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null

FS_RESERVED = set('''abstract and as assert base begin class default delegate do done downcast downto elif else end
exception extern false finally fixed for fun function global if in inherit inline interface internal lazy let match member
module mutable namespace new not null of open or override private public rec return select sig static struct then to true
try type upcast use val void when while with yield atomic break checked component const constraint constructor continue
eager event external functor include method mixin object parallel process protected pure sealed tailcall trait virtual
volatile params
float float32 double single int int8 int16 int32 int64 uint8 uint16 uint32 uint64 byte sbyte char decimal string unit
bool obj nativeint unativeint bigint
ignore isNull abs max min sqrt exp log log10 floor ceil sin cos tan asin acos atan pow sign round truncate box unbox ref id
fst snd hash compare raise failwith printf printfn sprintf failwithf nan infinity nameof typeof sizeof enum defaultof incr
decr
R S O Libm CPtr CFile IBox LBox DBox FBox OdeDerivs Math System Array Object String Int32 Int64 Double Unchecked
Engine Swmm5 Program'''.split())

FT = {'i': 'int', 'u': 'uint32', 'l': 'int64', 'ul': 'uint64', 'd': 'float', 'f': 'float32'}
ZERO = {'i': '0', 'u': '0u', 'l': '0L', 'ul': '0UL', 'd': '0.0', 'f': '0.0f'}
ONE = {'i': '1', 'u': '1u', 'l': '1L', 'ul': '1UL', 'd': '1.0', 'f': '1.0f'}
CONV = {'i': 'int', 'u': 'uint32', 'l': 'int64', 'ul': 'uint64', 'd': 'float', 'f': 'float32'}
BOX = {'i': 'IBox', 'u': 'IBox', 'l': 'LBox', 'ul': 'LBox', 'd': 'DBox', 'f': 'FBox'}
MATH = {'fabs': 'Math.Abs', 'sqrt': 'Math.Sqrt', 'floor': 'Libm.floor', 'ceil': 'Libm.ceil',
        'exp': 'Libm.exp', 'log': 'Libm.log', 'log10': 'Libm.log10', 'sin': 'Libm.sin', 'cos': 'Libm.cos',
        'tan': 'Libm.tan', 'asin': 'Libm.asin', 'acos': 'Libm.acos', 'atan': 'Libm.atan'}
FOPS = {'&': '&&&', '|': '|||', '^': '^^^', '<<': '<<<', '>>': '>>>'}
MEMPOOL = {'AllocInit', 'Alloc', 'AllocSetPool', 'AllocReset', 'AllocFreePool'}
RANK = {'i': 0, 'u': 1, 'l': 2, 'ul': 3}


def nullish(code):
    """is code a null pointer (in any of the spellings the emitter writes)?"""
    code = code.strip()
    while code.startswith('(') and code.endswith(')'):
        code = code[1:-1].strip()
    return is_null(code) or code.startswith('Unchecked.defaultof<')


def fident(n):
    return n + '_' if n in FS_RESERVED else n


def fs_string(b):
    out = []
    for ch in b:
        if ch == 0x5c:
            out.append('\\\\')
        elif ch == 0x22:
            out.append('\\"')
        elif 32 <= ch < 127:
            out.append(chr(ch))
        else:
            out.append('\\u%04x' % ch)
    return '"' + ''.join(out) + '"'


def fs_float(tok, tg):
    """an F# float literal for the C literal token tok (no suffix handling beyond removing C's)"""
    s = tok.rstrip('fFlL')
    if s.startswith('.'):
        s = '0' + s
    s = re.sub(r'\.([eE])', r'.0\1', s)
    if s.endswith('.'):
        s += '0'
    if '.' not in s:
        m = re.match(r'^(\d+)([eE].*)?$', s)
        s = m.group(1) + '.0' + (m.group(2) or '')
    return s + ('f' if tg == 'f' else '')


def float_repr(x, tg):
    if x != x:
        # C's NAN is a NaN with the sign bit clear; .NET's Double.NaN has it set (it is x86's default NaN)
        return 'BitConverter.Int64BitsToDouble(0x7ff8000000000000L)' if tg != 'f' else 'BitConverter.Int32BitsToSingle(0x7fc00000)'
    if x in (float('inf'), float('-inf')):
        n = 'Double' if tg != 'f' else 'Single'
        return '%s.%sInfinity' % (n, 'Positive' if x > 0 else 'Negative')
    if tg == 'f':
        x = struct.unpack('<f', struct.pack('<f', x))[0]
    s = repr(x)
    if 'e' in s and '.' not in s.split('e')[0]:
        a, b = s.split('e')
        s = a + '.0e' + b
    elif '.' not in s and 'e' not in s:
        s += '.0'
    if s.startswith('-'):
        s = '(%s)' % s
        return s[:-1] + ('f)' if tg == 'f' else ')')
    return s + ('f' if tg == 'f' else '')


def int_lit(v, tg):
    suf = {'i': '', 'u': 'u', 'l': 'L', 'ul': 'UL'}.get(tg, '')
    if tg == 'i':
        v = ((v + (1 << 31)) % (1 << 32)) - (1 << 31)
        if v == -(1 << 31):
            return 'Int32.MinValue'
    elif tg == 'u':
        v &= 0xffffffff
    elif tg == 'l':
        v = ((v + (1 << 63)) % (1 << 64)) - (1 << 63)
        if v == -(1 << 63):
            return 'Int64.MinValue'
    elif tg == 'ul':
        v &= 0xffffffffffffffff
    if v < 0:
        return '(%d%s)' % (v, suf)
    return '%d%s' % (v, suf)


# ======================================================================== control-flow tree of one function
class Code:
    def __init__(self, lines):
        self.lines = lines


class Blk:
    def __init__(self, items):
        self.items = items


class If:
    def __init__(self, cond, then, els):
        self.cond, self.then, self.els = cond, then, els


class Loop:
    def __init__(self, lid, kind, cond, body, inc):
        self.id, self.kind, self.cond, self.body, self.inc = lid, kind, cond, body, inc


class Sw:
    def __init__(self, sid, scrut, sections, has_default):
        self.id, self.scrut, self.sections = sid, scrut, sections   # sections: [(patterns or None for default, Blk)]
        self.has_default = has_default


class Jump:
    def __init__(self, kind, target, value=None):
        self.kind, self.target, self.value = kind, target, value   # kind: 'ret' 'brk' 'cnt'
        self.flag = None


def can_complete(n):
    if isinstance(n, Code):
        return True
    if isinstance(n, Jump):
        return False
    if isinstance(n, Blk):
        return all(can_complete(x) for x in n.items)
    if isinstance(n, If):
        return n.els is None or can_complete(n.then) or can_complete(n.els)
    if isinstance(n, Loop):
        if n.cond is None:
            return breaks_to(n.body, n.id)
        return True
    if isinstance(n, Sw):
        # a switch with a default whose every section ends in a jump, none of them a break from the switch
        return not n.has_default or any(can_complete(b) for _, b in n.sections) or breaks_to(n, -n.id)
    return True


def breaks_to(n, lid):
    if isinstance(n, Jump):
        return n.kind == 'brk' and n.target == lid
    if isinstance(n, Blk):
        return any(breaks_to(x, lid) for x in n.items)
    if isinstance(n, If):
        return breaks_to(n.then, lid) or (n.els is not None and breaks_to(n.els, lid))
    if isinstance(n, Loop):
        return breaks_to(n.body, lid)
    if isinstance(n, Sw):
        return any(breaks_to(b, lid) for _, b in n.sections)
    return False


def jumps_in(n):
    if isinstance(n, Jump):
        yield n
    elif isinstance(n, Blk):
        for x in n.items:
            yield from jumps_in(x)
    elif isinstance(n, If):
        yield from jumps_in(n.then)
        if n.els is not None:
            yield from jumps_in(n.els)
    elif isinstance(n, Loop):
        yield from jumps_in(n.body)
    elif isinstance(n, Sw):
        for _, b in n.sections:
            yield from jumps_in(b)


def targets_in(n):
    """ids of the loops and switches inside n"""
    out = set()
    if isinstance(n, Blk):
        for x in n.items:
            out |= targets_in(x)
    elif isinstance(n, If):
        out |= targets_in(n.then)
        if n.els is not None:
            out |= targets_in(n.els)
    elif isinstance(n, Loop):
        out.add(n.id)
        out |= targets_in(n.body)
    elif isinstance(n, Sw):
        out.add(n.id)
        for _, b in n.sections:
            out |= targets_in(b)
    return out


def flag_name(j):
    if j.kind == 'ret':
        return '__ret'
    if j.kind == 'cnt':
        return '__cnt%d' % j.target
    return ('__brk%d' if j.target > 0 else '__sw%d') % abs(j.target)


def escaping_flags(n):
    """flags set by jumps in n that leave n"""
    inside = targets_in(n)
    out = []
    for j in jumps_in(n):
        if j.flag and (j.kind == 'ret' or j.target not in inside):
            f = flag_name(j)
            if f not in out:
                out.append(f)
    return out


def simplify(n):
    """drop unreachable statements and move the rest of a block into the branch of an if that can complete"""
    if isinstance(n, Blk):
        n.items = simplify_items(n.items)
    elif isinstance(n, If):
        simplify(n.then)
        if n.els is not None:
            simplify(n.els)
    elif isinstance(n, Loop):
        simplify(n.body)
    elif isinstance(n, Sw):
        for _, b in n.sections:
            simplify(b)
    return n


def simplify_items(items):
    flat = []
    for x in items:
        if isinstance(x, Blk):
            flat += x.items
        else:
            flat.append(x)
    out = []
    i = 0
    while i < len(flat):
        it = flat[i]
        if isinstance(it, Blk):
            flat[i:i + 1] = it.items
            continue
        simplify(it)
        out.append(it)
        if not can_complete(it):
            break
        rest = flat[i + 1:]
        if isinstance(it, If) and rest:
            tc = can_complete(it.then)
            ec = it.els is None or can_complete(it.els)
            if not tc and ec:
                it.els = Blk((it.els.items if it.els is not None else []) + rest)
                simplify(it.els)
                break
            if tc and not ec:
                it.then = Blk(it.then.items + rest)
                simplify(it.then)
                break
        i += 1
    return out


def mark(n, ctx):
    """decide which jumps need a flag: a jump needs none where nothing would run between it and its target"""
    if isinstance(n, Blk):
        last = len(n.items) - 1
        off = {k: False for k in ctx}
        for i, x in enumerate(n.items):
            mark(x, ctx if i == last else off)
    elif isinstance(n, If):
        mark(n.then, ctx)
        if n.els is not None:
            mark(n.els, ctx)
    elif isinstance(n, Loop):
        c = {k: False for k in ctx}
        c[('cnt', n.id)] = True
        mark(n.body, c)
    elif isinstance(n, Sw):
        c = dict(ctx)
        c[('sw', n.id)] = True
        for _, b in n.sections:
            mark(b, c)
    elif isinstance(n, Jump):
        if n.kind == 'ret':
            n.flag = not ctx.get('ret', False)
        elif n.kind == 'cnt':
            n.flag = not ctx.get(('cnt', n.target), False)
        elif n.target > 0:
            n.flag = True                                   # a break from a loop: the loop tests the flag
        else:
            n.flag = not ctx.get(('sw', -n.target), False)  # a break from a switch: only if code follows


class FSEmitter(CSEmitter):
    def __init__(self, F):
        super().__init__(F)
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        self.fname = {}
        for (b, n), c in F.funcs.items():
            self.fname[(b, n)] = fident(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.gname = {}
        for k, c in F.globals.items():
            n = c.spelling
            b = F.global_owner[k]
            self.gname[k] = fident(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.module_names = set(self.gname.values()) | {fident(n) for n in F.enum_consts}
        self.fallthroughs = []
        self.jump_stats = {}
        self.delegate_params = {}

    # ================================================================== names
    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = 'L%d' % len(self.lits)
        return self.lits[b]

    def global_ref(self, d):
        k = decl_key(d)
        if k in self.gname:
            return self.gname[k]
        for gk, c in self.F.globals.items():
            if c.spelling == d.spelling and c.storage_class != front.ci.StorageClass.STATIC:
                return self.gname[gk]
        if d.spelling in ('stdout', 'stderr'):
            return 'R.stdout_'
        return fident(d.spelling)

    def static_local_name(self, d):
        return fident('%s_%s' % (d.semantic_parent.spelling, d.spelling))

    def local_name(self, d):
        return self.locals.get(decl_key(d), fident(d.spelling))

    def declare_local(self, d):
        n = d.spelling
        nn = n
        if nn in self.used_names or fident(nn) in self.module_names:
            i = 2
            while '%s_%d' % (n, i) in self.used_names or fident('%s_%d' % (n, i)) in self.module_names:
                i += 1
            nn = '%s_%d' % (n, i)
        self.used_names.add(nn)
        nm = fident(nn)
        self.locals[decl_key(d)] = nm
        return nm

    def tmp(self, base='__t'):
        self.ntmp += 1
        return '%s%d' % (base, self.ntmp)

    def callee_prefix(self, key):
        return 'O.' if (key in OVERRIDES or key[0] in SKIP_FILES) else 'S.'

    # ================================================================== types
    def rec(self, t):
        return fident(record_name(t))

    def fs_type(self, t, decl=None, mode=None):
        t = canon(t)
        tg = ctag(t)
        if tg in NUMTAGS:
            return FT[tg]
        if tg == 'v':
            return 'unit'
        if tg == 'rec':
            return self.rec(t)
        if tg == 'c':
            return 'CPtr'
        cat = ptr_category(t)
        if mode is None and decl is not None:
            mode = self.P.mode_of(decl)
        if cat == 'file':
            return 'CFile'
        if cat == 'void':
            return 'obj'
        if cat == 'func':
            return self.delegate(t)
        e = canon(t.element_type if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) else t.get_pointee())
        if cat == 'record':
            if (mode in (None, 'array') and t.kind != T.POINTER) or mode == 'array':
                return self.rec(e) + '[]'
            return self.rec(e)
        if cat == 'scalar':
            base = self.fs_type(e)
            if mode == 'ref':
                return 'byref<%s>' % base
            return base + '[]'
        if cat == 'ptrptr':
            inner = self.fs_type(e, mode='obj' if ptr_category(e) == 'record' else 'array')
            if mode == 'ref':
                return 'byref<%s>' % inner
            return inner + '[]'
        return 'obj'

    def zero(self, t, decl=None):
        tg = ctag(t)
        if tg in ZERO:
            return ZERO[tg]
        return 'Unchecked.defaultof<%s>' % self.value_type(t, decl)

    def value_type(self, t, decl=None):
        """the F# type of a C value of type t (a byref only exists as a parameter)"""
        ty = self.fs_type(t, decl)
        if ty.startswith('byref<'):
            ty = ty[6:-1]
        return ty

    def null_of(self, t, decl=None):
        """a null of C pointer type t; when the F# type depends on a declaration's pointer mode and none is
        known, F# infers it from where the null goes"""
        if decl is None and ptr_category(canon(t)) in ('record', 'scalar', 'ptrptr'):
            return 'Unchecked.defaultof<_>'
        return 'Unchecked.defaultof<%s>' % self.value_type(t, decl)

    def delegate(self, t):
        t = canon(t)
        ft = canon(t.get_pointee()) if t.kind == T.POINTER else t
        sig = (ft.get_result().spelling,) + tuple(a.spelling for a in ft.argument_types())
        if sig == ('void', 'double', 'double *', 'double *'):
            return 'OdeDerivs'           # odesolve.c's callback: the runtime's delegate (odesolve is hand-ported)
        if sig not in self.delegates:
            self.delegates[sig] = ('FP%d' % len(self.delegates), ft)
        return self.delegates[sig][0]

    def delegate_byref(self, name, ft, i):
        """is parameter i of the delegate type a byref? (as the functions bound to that type take it)"""
        key = (name, i)
        if key not in self.delegate_params:
            a = canon(list(ft.argument_types())[i])
            self.delegate_params[key] = ptr_category(a) == 'scalar' and self.bound_param_mode(ft, i) == 'ref'
        return self.delegate_params[key]

    def delegate_decl(self, name, ft):
        ps = []
        for i, a in enumerate(ft.argument_types()):
            a = canon(a)
            cat = ptr_category(a)
            if cat == 'scalar':
                base = self.fs_type(a.get_pointee())
                ps.append('byref<%s>' % base if self.delegate_byref(name, ft, i) else base + '[]')
            else:
                ps.append(self.value_type(a))
        rt = self.fs_type(ft.get_result())
        return '%s = delegate of %s -> %s' % (name, ' * '.join(ps) if ps else 'unit', rt)

    def delegate_value(self, fn_code, key, ft, dname):
        """a function used as a value: a delegate whose lambda calls it"""
        if dname == 'OdeDerivs':
            return 'OdeDerivs(fun __d0 __d1 __d2 -> %s(__d0, __d1, __d2))' % fn_code
        n = len(list(ft.argument_types()))
        names = ['__d%d' % i for i in range(n)]
        args = []
        for i in range(n):
            args.append('&' + names[i] if self.delegate_byref(dname, ft, i) else names[i])
        return '%s(fun %s -> %s(%s))' % (dname, ' '.join(names) if names else '()', fn_code, ', '.join(args))

    # ================================================================== conversions
    def to_ctype(self, e, t):
        if e.tag == 'b' and ctag(t) in NUMTAGS:
            return Ex('(if %s then %s else %s)' % (e.code, ONE[ctag(t)], ZERO[ctag(t)]), ctag(t))
        return e

    def as_bool(self, e):
        if e.tag == 'b':
            return e.code
        if e.tag in ZERO:
            return '(%s <> %s)' % (e.code, ZERO[e.tag])
        return '(not (obj.ReferenceEquals(%s, null)))' % e.code

    def cond(self, c):
        return self.as_bool(self.ex(c))

    def conv(self, e, src_t, dst_t):
        s, d = ctag(src_t), ctag(dst_t)
        if e.tag == 'b':
            if d in NUMTAGS:
                return Ex('(if %s then %s else %s)' % (e.code, ONE[d], ZERO[d]), d)
            e = Ex('(if %s then 1 else 0)' % e.code, 'i'); s = 'i'
        if e.tag in NUMTAGS:
            s = e.tag
        if d in ('c', 'o') and (e.tag == 'n' or nullish(e.code)):
            return Ex(self.null_of(dst_t), d)
        if s == d or d in ('v', '?', 'rec'):
            return Ex(e.code, d if d != '?' else e.tag)
        if d in NUMTAGS and s in NUMTAGS:
            if s in ('d', 'f') and d in ('i', 'l', 'u', 'ul'):
                x = e.code if s == 'd' else 'float (%s)' % e.code
                if d == 'i':
                    return Ex('R.D2I(%s)' % x, 'i')
                if d == 'l':
                    return Ex('R.D2L(%s)' % x, 'l')
                return Ex('%s (R.D2L(%s))' % (CONV[d], x), d)
            return Ex('%s (%s)' % (CONV[d], e.code), d)
        if d in ('c', 'o'):
            if e.tag == 'n' or nullish(e.code) or (e.tag in ('i', 'l', 'ul', 'u') and e.code in ('0', '0L', '0UL', '0u')):
                return Ex(self.null_of(dst_t), d)
            return Ex(e.code, d)
        return e

    # ================================================================== leaves
    def x_INTEGER_LITERAL(self, c):
        tg = ctag(c.type)
        v = evaluate(c)
        if v is None:
            toks = [t.spelling for t in c.get_tokens()]
            s = re.sub(r'[uUlL]+$', '', toks[0]) if toks else '0'
            n = int(s, 0) if not (len(s) > 1 and s.startswith('0') and s.isdigit()) else int(s, 8)
        else:
            n = v[1]
        return Ex(int_lit(n, tg), tg)

    def x_FLOATING_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?[fFlL]?', toks[0]):
            return Ex(fs_float(toks[0], tg), tg)
        v = evaluate(c)
        return Ex(float_repr(v[1] if v else 0.0, tg), tg)

    def x_CHARACTER_LITERAL(self, c):
        v = evaluate(c)
        return Ex(int_lit(v[1] if v else 0, 'i'), 'i')

    def x_STRING_LITERAL(self, c):
        return Ex(self.lit(self.string_bytes(c)), 'c')

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return Ex(fident(c.spelling), '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return Ex(int_lit(d.enum_value, 'i'), 'i')
            return Ex(fident(d.spelling), 'i')
        if d.kind == K.FUNCTION_DECL:
            keys = self.F.func_by_decl.get(d.spelling)
            n = self.func_ref(d, self.cur_file)
            if n is None:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex('null', 'o')
            fdef = self.func_def(d, self.cur_file)
            key = [k for k in keys if self.F.funcs[k] == fdef][0] if fdef is not None else keys[0]
            ft = canon(d.type)
            dname = self.delegate(ft)
            return Ex(self.delegate_value(self.callee_prefix(key) + n, key, ft, dname), 'o')
        if d.kind == K.PARM_DECL or (d.kind == K.VAR_DECL and d.semantic_parent is not None
                                     and d.semantic_parent.kind == K.FUNCTION_DECL
                                     and d.storage_class != front.ci.StorageClass.STATIC):
            return Ex(self.local_name(d), ctag(d.type))
        if d.kind == K.VAR_DECL:
            if d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL:
                return Ex(self.static_local_name(d), ctag(d.type))
            return Ex(self.global_ref(d), ctag(d.type))
        return Ex(fident(c.spelling), ctag(c.type))

    def x_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        return Ex('(%s)' % e.code, e.tag)

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                return Ex(self.zero(c.type), ctag(c.type))
            self.problem(c, 'unexposed with %d children' % len(ch))
            return self.ex(ch[0])
        e = self.ex(ch[0])
        if canon(c.type).kind == T.POINTER and e.tag in ('i', 'l') and e.code in ('0', '0L'):
            return Ex(self.null_of(c.type), ctag(c.type))
        if canon(ch[0].type).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return e
        return self.conv(e, ch[0].type, c.type)

    def x_CSTYLE_CAST_EXPR(self, c):
        ch = kids(c)
        inner = ch[-1]
        if ctag(c.type) == 'v':
            return self.ex(inner)
        s = strip(inner)
        if s.kind == K.CALL_EXPR and s.spelling in ('malloc', 'calloc', 'realloc'):
            return self.alloc(s, c.type)
        e = self.ex(inner)
        if e.tag == 'n' or (e.tag in ('i', 'l') and e.code in ('0', '0L') and canon(c.type).kind == T.POINTER):
            return Ex(self.null_of(c.type), ctag(c.type))
        if ctag(c.type) == 'o' and ctag(inner.type) == 'o' and canon(c.type).kind == T.POINTER:
            if ptr_category(inner.type) == 'void' and ptr_category(c.type) == 'record':
                return Ex('(%s :?> %s)' % (e.code, self.rec(canon(c.type).get_pointee())), 'o')
            if ptr_category(c.type) == 'void':
                return Ex('box (%s)' % e.code, 'o')
            return e
        r = self.conv(self.to_ctype(e, inner.type), inner.type, c.type)
        k = canon(c.type).kind
        if k in (T.UCHAR, T.CHAR_U):
            return Ex('(%s &&& 255)' % r.code, 'i')
        if k in (T.CHAR_S, T.SCHAR) and canon(inner.type).kind not in (T.CHAR_S, T.SCHAR):
            return Ex('((%s <<< 24) >>> 24)' % r.code, 'i')
        if k == T.SHORT:
            return Ex('((%s <<< 16) >>> 16)' % r.code, 'i')
        if k == T.USHORT:
            return Ex('(%s &&& 65535)' % r.code, 'i')
        return r

    def x_CXX_UNARY_EXPR(self, c):
        v = evaluate(c)
        return Ex(int_lit(v[1] if v else 8, 'ul'), 'ul')

    # ================================================================== lvalues
    def pure(self, c):
        """no side effects: evaluating c twice is the same as once"""
        if c.kind == K.CALL_EXPR or c.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            return False
        if c.kind == K.BINARY_OPERATOR and binop(c) in ('=', ','):
            return False
        if c.kind == K.UNARY_OPERATOR and unop(c) in ('pre++', 'pre--', 'post++', 'post--'):
            return False
        return all(self.pure(x) for x in kids(c))

    def lvalue(self, l):
        e = self.ex(l)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        return code

    def lvalue_once(self, l):
        """(binds, code): code names the location of l; binds are let-bindings that must come first so that
        code may be evaluated more than once without repeating l's side effects"""
        sl = strip(l)
        if self.pure(sl):
            return [], self.lvalue(l)
        if sl.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sl)
            b = self.tmp('__b'); i = self.tmp('__i')
            ic = self.val(idx)
            if ic.tag != 'i':
                ic = Ex('int (%s)' % ic.code, 'i')
            return [(b, self.ex(base).code), (i, ic.code)], '%s.[%s]' % (b, i)
        if sl.kind == K.MEMBER_REF_EXPR:
            o = self.tmp('__o')
            return [(o, self.ex(kids(sl)[0]).code)], '%s.%s' % (o, fident(sl.referenced.spelling))
        if sl.kind == K.UNARY_OPERATOR and unop(sl) == '*':
            a = strip(kids(sl)[0])
            if ptr_category(a.type) == 'char':
                p = self.tmp('__p')
                if a.kind == K.BINARY_OPERATOR and binop(a) in ('+', '-'):
                    x, y = kids(a)
                    i = self.tmp('__i')
                    yc = self.val(y).code
                    return [(p, self.ex(x).code), (i, 'int (%s)' % yc if binop(a) == '+' else '-(int (%s))' % yc)], '%s.[%s]' % (p, i)
                return [(p, self.ex(a).code)], '%s.[0]' % p
        self.problem(l, 'side effects in an lvalue used twice')
        return [], self.lvalue(l)

    @staticmethod
    def with_binds(binds, body):
        if not binds:
            return body
        return '(%s %s)' % (' '.join('let %s = %s in' % (n, v) for n, v in binds), body)

    # ================================================================== operators
    def x_UNARY_OPERATOR(self, c):
        op = unop(c)
        a = kids(c)[0]
        if op == '&':
            return self.addr_of(a, c)
        if op == '*':
            return self.deref(a)
        if op == '!':
            return Ex('(not %s)' % self.paren(self.cond(a)), 'b')
        if op in ('pre++', 'pre--', 'post++', 'post--'):
            return self.incdec_value(a, op)
        e = self.val(a)
        if op == '-':
            if e.tag in ('u', 'ul'):
                return Ex('(%s - %s)' % (ZERO[e.tag], e.code), e.tag)
            return Ex('(-(%s))' % e.code, e.tag)
        if op == '+':
            return e
        if op == '~':
            return Ex('(~~~(%s))' % e.code, e.tag)
        self.problem(c, 'unary ' + op)
        return e

    @staticmethod
    def paren(s):
        if re.fullmatch(r'[\w.\[\]]+', s):
            return s
        if s.startswith('(') and s.endswith(')') and CSEmitter._balanced(s[1:-1]):
            return s
        return '(' + s + ')'

    def step(self, lv, tg, d):
        """lv + 1 or lv - 1 at C type tg"""
        if tg == 'c':
            return '%s.Add(%s)' % (self.paren(lv), '1' if d == '+' else '-1')
        return '%s %s %s' % (lv, d, ONE.get(tg, '1'))

    def incdec_value(self, a, op):
        d = '+' if '++' in op else '-'
        tg = ctag(a.type)
        binds, lv = self.lvalue_once(a)
        t = self.tmp()
        if op.startswith('pre'):
            body = '%s <- %s; %s' % (lv, self.step(lv, tg, d), lv)
        else:
            body = 'let %s = %s in %s <- %s; %s' % (t, lv, lv, self.step(t, tg, d), t)
        return Ex(self.with_binds(binds, '(%s)' % body), tg)

    def deref(self, a):
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                x, y = kids(sa)
                if ptr_category(x.type) == 'char':
                    i = self.int_of(self.val(y))
                    return Ex('%s.[%s]' % (self.paren(self.ex(x).code), i if binop(sa) == '+' else '-(%s)' % i), 'i')
            return Ex('%s.[0]' % self.paren(self.ex(a).code), 'i')
        e = self.ex(a)
        if cat == 'record':
            return Ex(e.code, 'rec')
        mode = self.mode_of_expr(sa)
        pt = ctag(canon(a.type).get_pointee())
        if mode == 'ref':
            return Ex(e.code, pt)
        if sa.kind == K.BINARY_OPERATOR:
            l, r = kids(sa)
            return Ex('%s.[%s]' % (self.paren(self.ex(l).code), self.int_of(self.val(r))), pt)
        return Ex('%s.[0]' % self.paren(e.code), pt)

    def int_of(self, e):
        return e.code if e.tag == 'i' else 'int (%s)' % e.code

    def addr_of(self, a, c):
        sa = strip(a)
        if canon(sa.type).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return self.ex(sa)
        if ctag(sa.type) == 'rec':
            return Ex(self.ex(sa).code, 'o')
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sa)
            if ptr_category(base.type) == 'char':
                b = self.ex(base).code; i = self.val(idx)
                return Ex(b if i.code == '0' else '%s.Add(%s)' % (self.paren(b), self.int_of(i)), 'c')
            if ctag(sa.type) == 'rec':
                return Ex(self.ex(sa).code, 'o')
            i = self.val(idx).code
            if i == '0':
                return Ex(self.ex(base).code, 'o')
        if sa.kind == K.UNARY_OPERATOR and unop(sa) == '*':
            return self.ex(kids(sa)[0])
        return Ex('&' + self.lvalue(sa), 'ref')

    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            return self.assign_value(l, r)
        if op in ('&&', '||'):
            return Ex('(%s %s %s)' % (self.cond(l), op, self.cond(r)), 'b')
        if op == ',':
            return Ex('(%s; %s)' % ('; '.join(self.expr_stmt(l)), self.val(r).code), ctag(c.type))
        lt, rt = canon(l.type), canon(r.type)
        le, re_ = self.val(l), self.val(r)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            if le.tag in ('c', 'o', 'n', 'ref') or re_.tag in ('c', 'o', 'n', 'ref'):
                return Ex(self.ptr_compare(le, re_, op, l, r), 'b')
            fop = {'==': '=', '!=': '<>'}.get(op, op)
            return Ex('(%s %s %s)' % (le.code, fop, re_.code), 'b')
        tg = ctag(c.type)
        if tg == 'c':
            if op == '+':
                if ptr_category(l.type) == 'char':
                    return Ex('%s.Add(%s)' % (self.paren(le.code), self.int_of(re_)), 'c')
                return Ex('%s.Add(%s)' % (self.paren(re_.code), self.int_of(le)), 'c')
            return Ex('%s.Add(-(%s))' % (self.paren(le.code), self.int_of(re_)), 'c')
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            return Ex('R.Diff(%s, %s)' % (le.code, re_.code), 'l')
        if op in ('<<', '>>'):
            return Ex('(%s %s %s)' % (le.code, FOPS[op], self.int_of(re_)), tg)
        a = self.conv(le, l.type, c.type).code if le.tag != tg else le.code
        b = self.conv(re_, r.type, c.type).code if re_.tag != tg else re_.code
        return Ex('(%s %s %s)' % (a, FOPS.get(op, op), b), tg)

    def ptr_compare(self, le, re_, op, l, r):
        nl = le.tag == 'n' or nullish(le.code) or (le.tag in ('i', 'l') and le.code in ('0', '0L'))
        nr = re_.tag == 'n' or nullish(re_.code) or (re_.tag in ('i', 'l') and re_.code in ('0', '0L'))
        if op in ('==', '!='):
            if nl or nr:
                x = re_.code if nl else le.code
                e = 'obj.ReferenceEquals(%s, null)' % x
            elif ptr_category(l.type) == 'char' or ptr_category(r.type) == 'char':
                e = 'R.peq(%s, %s)' % (le.code, re_.code)
            else:
                e = 'obj.ReferenceEquals(%s, %s)' % (le.code, re_.code)
            return '(%s)' % e if op == '==' else '(not (%s))' % e
        return '(%s.O %s %s.O)' % (self.paren(le.code), op, self.paren(re_.code))

    def assign_rhs(self, l, r):
        """the value assigned by l = r, converted to l's type"""
        if ctag(l.type) == 'rec':
            return '%s.Clone()' % self.paren(self.ex(r).code)
        e = self.conv(self.val(r), r.type, l.type)
        if ctag(l.type) == 'o' and e.code == 'null':
            return self.null_of(l.type)
        return e.code

    def assign_value(self, l, r):
        """l = r used as a value"""
        rhs = self.assign_rhs(l, r)
        t = self.tmp()
        lv = self.lvalue(l)
        return Ex('(let %s = %s in %s <- %s; %s)' % (t, rhs, lv, t, t), ctag(l.type))

    def compound_new(self, c, lv):
        """the value l op= r stores, computed from the location lv"""
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        re_ = self.val(r)
        if lt == 'c':
            return '%s.Add(%s)' % (self.paren(lv), self.int_of(re_) if op == '+' else '-(%s)' % self.int_of(re_))
        if op in ('<<', '>>'):
            return '(%s %s %s)' % (lv, FOPS[op], self.int_of(re_))
        if 'd' in (lt, rt):
            common = 'd'
        elif 'f' in (lt, rt):
            common = 'f'
        else:
            common = lt if RANK.get(lt, 0) >= RANK.get(re_.tag, 0) else re_.tag
            if common == 'u' and lt == 'l' or common == 'l' and lt == 'u':
                common = 'l'
        a = lv if lt == common else self.conv(Ex(lv, lt), l.type, None if False else l.type).code
        if lt != common:
            a = self.num_conv(lv, lt, common)
        b = re_.code if re_.tag == common else self.num_conv(re_.code, re_.tag, common)
        v = '(%s %s %s)' % (a, FOPS.get(op, op), b)
        if common != lt:
            v = self.num_conv(v, common, lt)
        return v

    def num_conv(self, code, s, d):
        if s == d:
            return code
        if s in ('d', 'f') and d in ('i', 'l', 'u', 'ul'):
            x = code if s == 'd' else 'float (%s)' % code
            if d == 'i':
                return 'R.D2I(%s)' % x
            if d == 'l':
                return 'R.D2L(%s)' % x
            return '%s (R.D2L(%s))' % (CONV[d], x)
        return '%s (%s)' % (CONV[d], code)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        l = kids(c)[0]
        binds, lv = self.lvalue_once(l)
        t = self.tmp()
        return Ex(self.with_binds(binds, '(let %s = %s in %s <- %s; %s)' % (t, self.compound_new(c, lv), lv, t, t)), ctag(l.type))

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        tg = ctag(c.type)
        ea = self.conv(self.val(a), a.type, c.type)
        eb = self.conv(self.val(b), b.type, c.type)
        if tg in ('c', 'o'):
            if nullish(ea.code):
                ea = Ex(self.null_of(c.type), tg)
            if nullish(eb.code):
                eb = Ex(self.null_of(c.type), tg)
        return Ex('(if %s then %s else %s)' % (self.cond(cc), ea.code, eb.code), tg)

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, idx = kids(c)
        b = self.ex(base)
        i = self.val(idx)
        return Ex('%s.[%s]' % (self.paren(b.code), self.int_of(i)), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        b = self.ex(base)
        return Ex('%s.%s' % (self.paren(b.code), fident(c.referenced.spelling)), ctag(c.type))

    # ================================================================== initialisers
    def x_INIT_LIST_EXPR(self, c):
        return self.init_list(c, c.type)

    def init_list(self, c, t):
        t = canon(t)
        items = kids(c)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            et = canon(t.element_type)
            n = t.element_count if t.kind == T.CONSTANTARRAY else len(items)
            if (et.kind == T.POINTER and front.is_char(et.get_pointee()) and items
                    and strip(items[-1]).kind == K.STRING_LITERAL and len(items) == n):
                # a string table with no NULL sentinel (lessons/02): findmatch() reads past its end, and
                # EPA's build finds a zero word there; the table gets the NULL the C source forgot
                self.defects.append('%s:%d string table without NULL sentinel' % (os.path.basename(c.location.file.name), c.location.line))
                n += 1
            if ctag(t) == 'c':
                vals = [self.int_of(self.val(it)) for it in items]
                return Ex('R.BufOf(%d, [| %s |])' % (n, '; '.join(vals)), 'c')
            vals = []
            for it in items:
                if strip(it).kind == K.INIT_LIST_EXPR:
                    vals.append(self.init_list(strip(it), et).code)
                elif ctag(et) == 'c' and strip(it).kind == K.STRING_LITERAL and et.kind == T.CONSTANTARRAY:
                    vals.append('R.BufFrom(%s, %d)' % (self.lit(self.string_bytes(strip(it))), et.element_count))
                else:
                    v = self.conv(self.val(it), it.type, et).code
                    if ctag(et) in ('c', 'o') and nullish(v):
                        v = self.null_of(et)
                    vals.append(v)
            while len(vals) < n:
                if ctag(et) == 'rec':
                    vals.append('%s()' % self.rec(et))
                elif et.kind == T.CONSTANTARRAY:
                    vals.append(self.new_array(et))
                else:
                    vals.append(self.zero(et))
            return Ex('[| %s |]' % '; '.join(vals), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            o = self.tmp('__r')
            sets = []
            for f, it in zip(fields, items):
                if strip(it).kind == K.INIT_LIST_EXPR:
                    v = self.init_list(strip(it), f.type).code
                else:
                    v = self.conv(self.val(it), it.type, f.type).code
                sets.append('%s.%s <- %s' % (o, fident(f.spelling), v))
            return Ex('(let %s = %s() in %s; %s)' % (o, self.rec(t), '; '.join(sets), o), 'rec')
        if len(items) == 1:
            return self.val(items[0])
        self.problem(c, 'init list for %s' % t.spelling)
        return Ex(self.zero(t), ctag(t))

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return 'Array.init %d (fun _ -> %s())' % (n, self.rec(et))
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return 'R.NewBufs(%d, %d)' % (n, et.element_count)
        if et.kind == T.CONSTANTARRAY:
            return 'R.Jagged<%s>(%d, %d)' % (self.fs_type(canon(et.element_type)), n, et.element_count)
        return 'Array.zeroCreate<%s> %d' % (self.value_type(et), n)

    # ================================================================== calls
    def x_CALL_EXPR(self, c):
        name = c.spelling
        args = list(c.get_arguments())
        d = c.referenced
        callee = kids(c)[0] if kids(c) else None
        if d is not None and d.kind == K.FUNCTION_DECL:
            fdef = self.func_def(d, self.cur_file)
            if fdef is None:
                return self.libc(c, name, args)
            keys = self.F.func_by_decl.get(d.spelling)
            key = [k for k in keys if self.F.funcs[k] == fdef][0]
            n = self.callee_prefix(key) + self.func_ref(d, self.cur_file)
            params = list(fdef.get_arguments())
            for i, (a, p) in enumerate(zip(args, params)):
                sa = strip(a)
                if (ptr_category(p.type) == 'scalar' and self.P.mode_of(p) == 'array' and sa.kind == K.UNARY_OPERATOR
                        and unop(sa) == '&' and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    # &x where the callee indexes an array: a one-element array, copied back after the call
                    o = kids(sa)[0]
                    binds, lv = self.lvalue_once(o)
                    arr, res = self.tmp('__a'), self.tmp('__r')
                    codes = [self.arg(x, q) if j != i else arr for j, (x, q) in enumerate(zip(args, params))]
                    body = '(let %s = [| %s |] in let %s = %s(%s) in %s <- %s.[0]; %s)' % (arr, lv, res, n, ', '.join(codes), lv, arr, res)
                    return Ex(self.with_binds(binds, body), ctag(c.type))
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    o = kids(sa)[0]
                    binds, lv = self.lvalue_once(o)
                    buf, res = self.tmp('__c'), self.tmp('__r')
                    codes = [self.arg(x, q) if j != i else buf for j, (x, q) in enumerate(zip(args, params))]
                    body = '(let %s = R.Buf(2) in %s.[0] <- %s; let %s = %s(%s) in %s <- %s.[0]; %s)' % (buf, buf, lv, res, n, ', '.join(codes), lv, buf, res)
                    return Ex(self.with_binds(binds, body), ctag(c.type))
            return Ex('%s(%s)' % (n, ', '.join(self.arg(a, p) for a, p in zip(args, params))), ctag(c.type))
        # a call through a function pointer: the delegate's Invoke
        fe = self.ex(callee)
        ct = canon(strip(callee).type)
        ft = canon(ct.get_pointee()) if ct.kind == T.POINTER else ct
        dname = self.delegate(ft)
        codes = []
        for i, a in enumerate(args):
            sa = strip(a)
            if dname != 'OdeDerivs' and self.delegate_byref(dname, ft, i):
                if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                    codes.append('&' + self.lvalue(kids(sa)[0]))
                else:
                    codes.append('&' + self.lvalue(sa))
            else:
                codes.append(self.conv(self.val(a), a.type, list(ft.argument_types())[i]).code)
        return Ex('%s.Invoke(%s)' % (self.paren(fe.code), ', '.join(codes)), ctag(c.type))

    def arg(self, a, p):
        """argument a passed to parameter p (of the callee's definition)"""
        pmode = self.P.mode_of(p)
        cat = ptr_category(p.type)
        sa = strip(a)
        if (cat == 'scalar' and pmode == 'ref') or (cat == 'ptrptr' and pmode == 'ref'):
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return '&' + self.lvalue(kids(sa)[0])
            if self.mode_of_expr(sa) == 'ref':
                return '&' + self.ex(sa).code
            e = self.ex(sa)
            if e.tag == 'n' or nullish(e.code) or (sa.kind == K.INTEGER_LITERAL):
                # NULL for a pointer the callee may write through: a scratch local nobody reads
                dn = self.tmp('__dummy')
                self.dummies.append((dn, self.value_type(canon(p.type).get_pointee())))
                return '&' + dn
            return '&%s.[0]' % self.paren(e.code)
        if cat == 'scalar' and pmode == 'array':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = strip(kids(sa)[0])
                if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                    base, idx = kids(o)
                    i = self.val(idx).code
                    if i != '0':
                        self.problem(a, 'array offset &x[%s] passed to array param %s' % (i, p.spelling))
                    return self.ex(base).code
        e = self.conv(self.val(a), a.type, p.type)
        if cat in ('char', 'record', 'scalar', 'ptrptr', 'file', 'void', 'func') and nullish(e.code):
            return self.null_of(p.type)
        if cat == 'void' and e.tag != 'n' and not e.code.startswith('Unchecked'):
            return 'box (%s)' % e.code
        return e.code

    # ================================================================== C library
    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name in MATH:
            return Ex('%s(%s)' % (MATH[name], A(0)), 'd')
        if name == 'pow':
            return Ex('Libm.pow(%s, %s)' % (A(0), A(1)), 'd')
        if name in ('fprintf', 'snprintf'):
            fixed = {'fprintf': 2, 'snprintf': 3}[name]
            head = [A(i) for i in range(fixed)]
            if name == 'snprintf':
                head[1] = self.num_conv(head[1], self.val(args[1]).tag, 'ul')
            rest = []
            for a in args[fixed:]:
                e = self.val(a)
                rest.append('box (%s)' % e.code)
            return Ex('R.%s(%s, [| %s |])' % (name, ', '.join(head), '; '.join(rest)), 'i')
        if name == 'sscanf':
            return self.sscanf(args)
        if name == 'free':
            return Ex('()', 'v')
        if name in ('calloc', 'malloc', 'realloc'):
            return self.alloc(c, c.type)
        if name in ('fwrite', 'fread'):
            return self.freadwrite(c, name, args)
        if name == 'memset':
            dst = strip(args[0])
            if dst.kind == K.UNARY_OPERATOR and unop(dst) == '&' and ctag(strip(kids(dst)[0]).type) == 'rec':
                o = strip(kids(dst)[0])
                return Ex('%s <- %s()' % (self.lvalue(o), self.rec(o.type)), 'v')
            return Ex('R.memset(%s, %s, %s)' % (A(0), A(1), self.num_conv(A(2), self.val(args[2]).tag, 'ul')), 'v')
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return Ex('R.strtod(%s, &%s)' % (A(0), self.lvalue(kids(ep)[0])), 'd')
            return Ex('R.strtod(%s)' % A(0), 'd')
        if name == 'time':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                t = self.tmp()
                lv = self.lvalue(kids(a0)[0])
                return Ex('(let %s = R.time() in %s <- %s; %s)' % (t, lv, t, t), 'l')
            return Ex('R.time()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('R.ctime(%s)' % (self.ex(kids(a0)[0]).code if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('float (%s - %s)' % (A(0), A(1)), 'd')
        if name in ('fseek', 'fseeko'):
            return Ex('R.fseek(%s, %s, %s)' % (A(0), self.num_conv(A(1), self.val(args[1]).tag, 'l'), A(2)), 'i')
        rt = {'strlen': 'ul', 'atoi': 'i', 'strcmp': 'i', 'feof': 'i', 'fclose': 'i', 'atof': 'd', 'ftell': 'l',
              'strcspn': 'ul', 'toupper': 'i', 'remove': 'i', 'fflush': 'i', 'rewind': 'v', 'mkstemp': 'i'}.get(name, tg)
        return Ex('R.%s(%s)' % (name, ', '.join(A(i) for i in range(len(args)))), rt)

    def sscanf(self, args):
        s, fmt = self.val(args[0]).code, self.val(args[1]).code
        binds, items, back = [], [], []
        for a in args[2:]:
            sa = strip(a)
            target = None
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = kids(sa)[0]
                if ctag(strip(o).type) in NUMTAGS:
                    target = (self.lvalue(o), ctag(strip(o).type))
            elif ptr_category(sa.type) == 'scalar' and self.mode_of_expr(sa) == 'ref':
                target = (self.ex(sa).code, ctag(canon(sa.type).get_pointee()))
            if target is None:
                items.append('box (%s)' % self.val(a).code)
                continue
            lv, t = target
            bx = self.tmp('__s')
            init = lv if t not in ('u', 'ul') else '%s (%s)' % ('int' if t == 'u' else 'int64', lv)
            binds.append('let %s = %s(%s) in' % (bx, BOX[t], init))
            items.append('box %s' % bx)
            back.append('%s <- %s' % (lv, '%s.v' % bx if t not in ('u', 'ul') else '%s (%s.v)' % (CONV[t], bx)))
        n = self.tmp('__n')
        call = 'R.sscanf(%s, %s, [| %s |])' % (s, fmt, '; '.join(items))
        if not back:
            return Ex(call, 'i')
        return Ex('(%s let %s = %s in %s; %s)' % (' '.join(binds), n, call, '; '.join(back), n), 'i')

    def alloc(self, call, t):
        args = list(call.get_arguments())
        t = canon(t)
        if t.kind != T.POINTER:
            self.problem(call, 'alloc into non-pointer')
            return Ex('null', 'o')
        et = canon(t.get_pointee())
        name = call.spelling
        if name == 'calloc':
            n = self.count_expr(args[0], args[1], et, mul=True)
        elif name == 'malloc':
            n = self.count_expr(args[0], None, et, mul=False)
        else:
            n = self.count_expr(args[1], None, et, mul=False)
            old = self.val(args[0]).code
            if ctag(t) == 'c':
                return Ex('R.ReallocBuf(%s, %s)' % (old, n), 'c')
            if et.kind == T.RECORD:
                return Ex('R.Realloc(%s, %s, (fun () -> %s()))' % (old, n, self.rec(et)), 'o')
            return Ex('R.Realloc(%s, %s)' % (old, n), 'o')
        if ctag(t) == 'c':
            return Ex('R.Buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('%s()' % self.rec(et), 'o')
            return Ex('R.NewArray(%s, (fun () -> %s()))' % (n, self.rec(et)), 'o')
        if et.kind == T.POINTER:
            inner = self.fs_type(et, mode='array') if ptr_category(et) != 'record' else self.rec(canon(et.get_pointee()))
            if ptr_category(et) == 'char':
                inner = 'CPtr'
            return Ex('Array.zeroCreate<%s> (%s)' % (inner, n), 'o')
        return Ex('Array.zeroCreate<%s> (%s)' % (self.fs_type(et), n), 'o')

    def int_code(self, x):
        return self.int_of(self.val(x))

    def freadwrite(self, c, name, args):
        buf, size, cnt, f = args
        sb = strip(buf)
        fc = self.val(f).code
        if sb.kind == K.UNARY_OPERATOR and unop(sb) == '&':
            o = strip(kids(sb)[0])
            if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                base, idx = kids(o)
                et = canon(o.type)
                target = '%s, %s' % (self.ex(base).code, self.int_of(self.val(idx)))
                kind = 'Arr'
            else:
                et = canon(o.type)
                kind = 'Ref'
                target = ('&' if name == 'fread' else '') + self.lvalue(o)
        elif self.mode_of_expr(sb) == 'ref':
            et = canon(canon(sb.type).get_pointee())
            kind = 'Ref'
            target = ('&' if name == 'fread' else '') + self.ex(sb).code
        else:
            bt = canon(sb.type)
            et = canon(bt.get_pointee()) if bt.kind == T.POINTER else canon(bt.element_type)
            kind = 'Arr'
            target = '%s, 0' % self.ex(sb).code
        sz = evaluate(strip(size))
        if sz and sz[0] == 'int' and kind == 'Ref' and sz[1] != self.sizeof_type(et) and et.kind in (T.LONG, T.INT, T.ULONG, T.UINT):
            # an 8-byte off_t written with sizeof(INT4): its low bytes (lessons/02, defect 4)
            if name == 'fwrite':
                return Ex('R.fwriteN1(int64 (%s), %d, %s)' % (target, sz[1], fc), 'ul')
            return Ex('R.freadN1(%s, %d, %s)' % (target, sz[1], fc), 'ul')
        tn = {T.DOUBLE: 'D', T.FLOAT: 'F', T.INT: 'I', T.LONG: 'L', T.CHAR_S: 'C', T.SCHAR: 'C', T.UINT: 'I', T.ENUM: 'I'}.get(et.kind)
        if tn is None:
            self.problem(c, '%s of %s' % (name, et.spelling))
            tn = 'X'
        if kind == 'Ref':
            return Ex('R.%s%s1(%s, %s)' % (name, tn, target, fc), 'ul')
        return Ex('R.%s%s(%s, %s, %s)' % (name, tn, target, self.int_code(cnt), fc), 'ul')

    # ================================================================== statements as expressions
    def expr_stmt(self, c):
        """C expression statement c as F# statement lines (each of type unit)"""
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) == 'v':
            return self.expr_stmt(kids(s)[-1])
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            rhs = self.assign_rhs(l, r)
            return ['%s <- %s' % (self.lvalue(l), rhs)]
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmt(l) + self.expr_stmt(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            binds, lv = self.lvalue_once(kids(s)[0])
            return [self.with_binds(binds, '%s <- %s' % (lv, self.compound_new(s, lv)))]
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            d = '+' if '++' in unop(s) else '-'
            binds, lv = self.lvalue_once(a)
            return [self.with_binds(binds, '%s <- %s' % (lv, self.step(lv, ctag(a.type), d)))]
        if s.kind == K.CALL_EXPR and s.spelling in ('free',):
            return []
        e = self.ex(s)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        if e.tag == 'v' and s.kind == K.CALL_EXPR:
            return [code] if code != '()' else []
        if code.startswith('R.memset') or (e.tag == 'v' and ' <- ' in code and not code.startswith('(')):
            return [code]
        return ['ignore (%s)' % code]

    # ================================================================== building the control-flow tree
    def build(self, c):
        """IR for statement c"""
        k = c.kind
        if k == K.COMPOUND_STMT:
            return Blk([self.build(x) for x in kids(c)])
        if k == K.DECL_STMT:
            lines = []
            for d in kids(c):
                lines += self.local_init(d)
            return Code(lines)
        if k == K.IF_STMT:
            ch = kids(c)
            then = self.build(ch[1])
            els = self.build(ch[2]) if len(ch) > 2 else None
            return If(self.cond(ch[0]), then if isinstance(then, Blk) else Blk([then]),
                      None if els is None else (els if isinstance(els, Blk) else Blk([els])))
        if k in (K.WHILE_STMT, K.DO_STMT, K.FOR_STMT):
            return self.build_loop(c)
        if k == K.SWITCH_STMT:
            return self.build_switch(c)
        if k == K.BREAK_STMT:
            return Jump('brk', self.breakable[-1])
        if k == K.CONTINUE_STMT:
            return Jump('cnt', [x for x in self.breakable if x > 0][-1])
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return Jump('ret', None)
            if ctag(self.cur_ret) == 'rec':
                return Jump('ret', None, '%s.Clone()' % self.paren(self.ex(ch[0]).code))
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            code = e.code
            if ctag(self.cur_ret) in ('c', 'o') and nullish(code):
                code = self.null_of(self.cur_ret)
            return Jump('ret', None, code)
        if k == K.NULL_STMT:
            return Code([])
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unhandled statement %s' % k.name)
            return Code([])
        return Code(self.expr_stmt(c))

    def const_true(self, c):
        if c is None:
            return True
        v = evaluate(strip(c))
        return v is not None and v[0] == 'int' and v[1] != 0 and strip(c).kind in (K.INTEGER_LITERAL, K.CHARACTER_LITERAL)

    def build_loop(self, c):
        self.nloop += 1
        lid = self.nloop
        ch = kids(c)
        pre = []
        inc = None
        if c.kind == K.WHILE_STMT:
            condc, body, kind = ch[0], ch[1], 'while'
        elif c.kind == K.DO_STMT:
            body, condc, kind = ch[0], ch[1], 'do'
        else:
            kind = 'for'
            body = ch[-1]
            parts = ch[:-1]
            toks = list(c.get_tokens())
            depth = 0; semis = []
            for t in toks[1:]:
                if t.spelling == '(':
                    depth += 1
                elif t.spelling == ')':
                    depth -= 1
                    if depth == 0:
                        break
                elif t.spelling == ';' and depth == 1:
                    semis.append(t.extent.start.offset)
            init = condc = incc = None
            for x in parts:
                o = x.extent.start.offset
                if len(semis) >= 2 and o < semis[0]:
                    init = x
                elif len(semis) >= 2 and o < semis[1]:
                    condc = x
                else:
                    incc = x
            if init is not None:
                if init.kind == K.DECL_STMT:
                    for d in kids(init):
                        pre += self.local_init(d)
                else:
                    pre += self.expr_stmt(init)
            if incc is not None:
                inc = self.expr_stmt(incc)
        cond = None if self.const_true(condc) else self.cond(condc)
        self.breakable.append(lid)
        b = self.build(body)
        self.breakable.pop()
        loop = Loop(lid, kind, cond, b if isinstance(b, Blk) else Blk([b]), inc)
        if pre:
            return Blk([Code(pre), loop])
        return loop

    def build_switch(self, c):
        self.nsw += 1
        sid = self.nsw
        ch = kids(c)
        e = self.val(ch[0])
        tg = e.tag if e.tag in ('i', 'u', 'l', 'ul') else 'i'
        scrut = e.code if e.tag != 'b' else '(if %s then 1 else 0)' % e.code
        body = ch[-1]
        items = kids(body) if body.kind == K.COMPOUND_STMT else [body]
        sections = []   # [labels (ints or 'default'), C statements]
        for it in items:
            if it.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                labels = []
                x = it
                while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                    xc = kids(x)
                    if x.kind == K.CASE_STMT:
                        v = evaluate(xc[0])
                        labels.append(v[1] if v else 0)
                        x = xc[1]
                    else:
                        labels.append('default')
                        x = xc[0]
                if sections and not sections[-1][1]:
                    sections[-1][0].extend(labels)
                else:
                    sections.append([labels, []])
                sections[-1][1].append(x)
            elif sections:
                sections[-1][1].append(it)
        self.breakable.append(-sid)
        built = [Blk([self.build(s) for s in stmts]) for _, stmts in sections]
        # C's fall-through: a section that can complete normally continues with the next one
        eff = [None] * len(sections)
        for i in range(len(sections) - 1, -1, -1):
            items_i = list(built[i].items)
            if can_complete(Blk(items_i)) and i + 1 < len(sections):
                self.fallthroughs.append('%s:%d' % (os.path.basename(c.location.file.name), sections[i][1][0].location.line))
                nxt = [self.build(s) for s in sections[i + 1][1]]     # built again: the copy is separate code
                items_i = items_i + [Blk(nxt)] + ([Blk(eff[i + 1].items[len(nxt):])] if eff[i + 1] is not None else [])
            eff[i] = Blk(items_i)
        self.breakable.pop()
        out = []
        default = None
        for (labels, _), b in zip(sections, eff):
            if 'default' in labels:
                default = b
            else:
                out.append((' | '.join(int_lit(v, tg) for v in labels), b))
        out.append((None, default if default is not None else Blk([])))
        return Sw(sid, scrut, out, default is not None)

    def local_init(self, d):
        """lines run where C declares local d (its storage was declared at the top of the function)"""
        if d.kind != K.VAR_DECL or d.storage_class in (front.ci.StorageClass.EXTERN, front.ci.StorageClass.STATIC):
            if d.kind == K.VAR_DECL and d.storage_class == front.ci.StorageClass.STATIC and (d, self.cur_file) not in self.static_locals:
                self.static_locals.append((d, self.cur_file))
            return []
        name = self.local_name(d)
        init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        t = canon(d.type)
        if t.kind == T.CONSTANTARRAY:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return ['%s <- %s' % (name, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return ['%s <- R.BufFrom(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return ['%s <- R.Buf(%d)' % (name, t.element_count)]
            return ['%s <- %s' % (name, self.new_array(t))]
        if ctag(t) == 'rec':
            if init:
                return ['%s <- %s.Clone()' % (name, self.paren(self.ex(init[-1]).code))]
            return ['%s <- %s()' % (name, self.rec(t))]
        if init:
            v = self.conv(self.val(init[-1]), init[-1].type, d.type).code
            if ctag(t) in ('c', 'o') and nullish(v):
                v = self.null_of(d.type, d)
            return ['%s <- %s' % (name, v)]
        return []

    # ================================================================== emitting the tree
    def emit_items(self, items, ind):
        p = '    ' * ind
        out = []
        for i, it in enumerate(items):
            out += self.emit_node(it, ind)
            rest = items[i + 1:]
            if rest and not isinstance(it, Code):
                fl = escaping_flags(it)
                if fl:
                    out.append(p + 'if not (%s) then' % ' || '.join(fl))
                    out += self.emit_block(Blk(rest), ind + 1)
                    return out
        return out

    def emit_block(self, b, ind):
        lines = self.emit_items(b.items, ind)
        if not lines:
            return ['    ' * ind + '()']
        return lines

    def emit_node(self, n, ind):
        p = '    ' * ind
        if isinstance(n, Code):
            return [p + l for l in n.lines]
        if isinstance(n, Blk):
            return self.emit_items(n.items, ind)
        if isinstance(n, Jump):
            out = []
            if n.kind == 'ret':
                if n.value is not None:
                    out.append(p + '__rv <- %s' % n.value)
                if n.flag:
                    out.append(p + '__ret <- true')
            elif n.flag:
                out.append(p + '%s <- true' % flag_name(n))
            return out
        if isinstance(n, If):
            out = [p + 'if %s then' % n.cond]
            out += self.emit_block(n.then, ind + 1)
            e = n.els
            while e is not None:
                if len(e.items) == 1 and isinstance(e.items[0], If):
                    out.append(p + 'elif %s then' % e.items[0].cond)
                    out += self.emit_block(e.items[0].then, ind + 1)
                    e = e.items[0].els
                else:
                    if self.emit_items(e.items, ind + 1):
                        out.append(p + 'else')
                        out += self.emit_block(e, ind + 1)
                    e = None
            return out
        if isinstance(n, Loop):
            return self.emit_loop(n, ind)
        if isinstance(n, Sw):
            out = []
            sflag = '__sw%d' % n.id
            if any(j.kind == 'brk' and j.target == -n.id and j.flag for j in jumps_in(n)):
                self.flags.add(sflag)
                out.append(p + '%s <- false' % sflag)
            out.append(p + 'match %s with' % n.scrut)
            for pat, b in n.sections:
                out.append(p + '| %s ->' % (pat if pat is not None else '_'))
                out += self.emit_block(b, ind + 1)
            return out
        raise ValueError(n)

    def emit_loop(self, n, ind):
        p = '    ' * ind
        q = '    ' * (ind + 1)
        js = list(jumps_in(n.body))
        brk = any(j.kind == 'brk' and j.target == n.id for j in js)
        cnt = any(j.kind == 'cnt' and j.target == n.id and j.flag for j in js)
        ret = any(j.kind == 'ret' and j.flag for j in js)
        stop = (['__brk%d' % n.id] if brk else []) + (['__ret'] if ret else [])
        guard = 'not (%s)' % ' || '.join(stop) if stop else None
        out = []
        if brk:
            self.flags.add('__brk%d' % n.id)
            out.append(p + '__brk%d <- false' % n.id)
        if cnt:
            self.flags.add('__cnt%d' % n.id)
        body = []
        if cnt:
            body.append(q + '__cnt%d <- false' % n.id)
        body += self.emit_items(n.body.items, ind + 1)
        if n.kind == 'for' and n.inc:
            if guard:
                body.append(q + 'if %s then' % guard)
                body += ['    ' * (ind + 2) + l for l in n.inc]
            else:
                body += [q + l for l in n.inc]
        if n.kind == 'do':
            go = '__go%d' % n.id
            self.flags.add(go)
            out.append(p + '%s <- true' % go)
            out.append(p + 'while %s do' % go)
            c = ' && '.join(x for x in (guard, n.cond) if x)
            if c:
                body.append(q + '%s <- %s' % (go, c))
        else:
            c = ' && '.join(x for x in (guard, n.cond) if x) or 'true'
            out.append(p + 'while %s do' % c)
        if not body:
            body = [q + '()']
        return out + body

    # ================================================================== functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.cur_ret = c.result_type
        self.ntmp = 0
        self.nloop = 0
        self.nsw = 0
        self.breakable = []
        self.flags = set()
        self.dummies = []
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        # parameters the body assigns, increments or takes the address of become mutable locals
        assigned = set()

        def scan(x):
            if x.kind == K.BINARY_OPERATOR and binop(x) == '=' or x.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
                t = strip(kids(x)[0])
                if t.kind == K.DECL_REF_EXPR and t.referenced is not None:
                    assigned.add(decl_key(t.referenced))
            if x.kind == K.UNARY_OPERATOR and unop(x) in ('pre++', 'pre--', 'post++', 'post--', '&'):
                t = strip(kids(x)[0])
                if t.kind == K.DECL_REF_EXPR and t.referenced is not None:
                    assigned.add(decl_key(t.referenced))
            for y in x.get_children():
                scan(y)
        scan(body)
        ps, pre = [], []
        for prm in params:
            nm = self.declare_local(prm)
            if nm[0].isupper():
                # F# reads an upper-case parameter name as a pattern: a byref parameter so named cannot be
                # assigned (FS0027), so upper-case parameters get a lower-case prefix
                q = 'p_' + nm
                while q in self.used_names:
                    q += '_'
                self.used_names.add(q)
                self.locals[decl_key(prm)] = q
                nm = q
            ty = self.fs_type(prm.type, prm)
            ps.append('%s: %s' % (nm, ty))
            if decl_key(prm) in assigned and not ty.startswith('byref<'):
                pre.append('let mutable %s = %s' % (nm, nm))
        # every local, declared once at the top
        hoisted = []

        def collect(x):
            for y in x.get_children():
                if y.kind == K.VAR_DECL and y.storage_class not in (front.ci.StorageClass.EXTERN, front.ci.StorageClass.STATIC):
                    nm = self.declare_local(y)
                    ty = self.value_type(y.type, y)
                    if self.P.mode_of(y) == 'ref' and ptr_category(y.type) in ('scalar', 'ptrptr'):
                        self.problem(y, 'pointer-to-scalar local %s' % y.spelling)
                    hoisted.append('let mutable %s : %s = %s' % (nm, ty, self.zero(y.type, y) if ctag(y.type) != 'rec' else 'Unchecked.defaultof<%s>' % ty))
                collect(y)
        collect(body)
        tree = self.build(body)
        simplify(tree)
        mark(tree, {'ret': True})
        for j in jumps_in(tree):
            k = (j.kind if j.kind != 'brk' or j.target > 0 else 'brk-switch', bool(j.flag))
            self.jump_stats[k] = self.jump_stats.get(k, 0) + 1
        lines = self.emit_block(tree, 2)
        if any(j.kind == 'ret' and j.flag for j in jumps_in(tree)):
            self.flags.add('__ret')
        rt = self.fs_type(c.result_type)
        out = ['    // %s:%d' % (b, c.location.line),
               '    static member %s (%s) : %s =' % (self.fname[key], ', '.join(ps), rt)]
        out += ['        ' + l for l in pre]
        if rt != 'unit':
            out.append('        let mutable __rv : %s = %s' % (rt, self.zero(c.result_type)))
        out += ['        ' + l for l in hoisted]
        for dn, dt in self.dummies:
            out.append('        let mutable %s : %s = Unchecked.defaultof<%s>' % (dn, dt, dt))
        for f in sorted(self.flags):
            out.append('        let mutable %s = false' % f)
        if lines == ['        ()'] and rt != 'unit':
            lines = []
        out += lines
        if rt != 'unit':
            out.append('        __rv')
        return out

    # ================================================================== records & globals
    def record(self, name, c, first):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = fident(name)
        out = ['%s %s =' % ('[<AllowNullLiteral>]\ntype' if first else 'and [<AllowNullLiteral>]', nm)]
        inits, clone = [], []
        for f in fields:
            t = canon(f.type)
            fn = fident(f.spelling)
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    ty, init = 'CPtr', 'R.Buf(%d)' % t.element_count
                    clone.append('c.%s <- R.CopyBuf(this.%s)' % (fn, fn))
                else:
                    ty, init = self.value_type(f.type, f), self.new_array(t)
                    if et.kind == T.RECORD:
                        clone.append('c.%s <- Array.map (fun (x: %s) -> x.Clone()) this.%s' % (fn, self.rec(et), fn))
                    elif ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
                        clone.append('c.%s <- R.CloneBufs(this.%s)' % (fn, fn))
                    elif et.kind == T.CONSTANTARRAY:
                        clone.append('c.%s <- R.CloneJagged(this.%s)' % (fn, fn))
                    else:
                        clone.append('c.%s <- Array.copy this.%s' % (fn, fn))
            elif t.kind == T.RECORD:
                ty, init = self.rec(t), '%s()' % self.rec(t)
                clone.append('c.%s <- this.%s.Clone()' % (fn, fn))
            else:
                ty = self.value_type(f.type, f)
                init = self.zero(f.type, f)
            out.append('    val mutable %s : %s' % (fn, ty))
            inits.append('%s = %s' % (fn, init))
        out.append('    new() = { %s }' % '; '.join(inits) if inits else '    new() = { }')
        out.append('    member this.Clone() : %s =' % nm)
        out.append('        let c = this.MemberwiseClone() :?> %s' % nm)
        out += ['        ' + l for l in clone]
        out.append('        c')
        return out

    def global_init(self, c, t, d=None):
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return self.init_list(strip(init[-1]), t).code
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return 'R.BufFrom(%s, %d)' % (self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return 'R.Buf(%d)' % t.element_count
            return self.new_array(t)
        if t.kind == T.RECORD:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return self.init_list(strip(init[-1]), t).code
            return '%s()' % self.rec(t)
        if init:
            v = self.conv(self.val(init[-1]), init[-1].type, c.type).code
            if ctag(t) in ('c', 'o') and nullish(v):
                v = self.null_of(c.type, c)
            return v
        return self.zero(c.type, c)

    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        self.locals = {}
        self.ntmp = 0
        t = canon(c.type)
        return 'let mutable %s : %s = %s' % (name, self.value_type(c.type, c), self.global_init(c, t))

    # ================================================================== driver
    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        self.static_locals = []
        self.cur_file = None
        self.locals = {}
        self.ntmp = 0
        funcs = []
        for key, c in self.F.funcs.items():
            if key[0] in SKIP_FILES or key in OVERRIDES:
                continue
            try:
                funcs += self.function(key, c) + ['']
            except Exception as ex:
                import traceback; traceback.print_exc()
                self.problems.append('%s:%s CRASH %s' % (key[0], key[1], ex))
        glob = []
        for k, c in self.F.globals.items():
            if self.F.global_owner[k] in SKIP_FILES:
                continue
            glob.append(self.global_decl(k, c))
        for d, b in self.static_locals:
            self.cur_file = b
            self.ntmp = 0
            t = canon(d.type)
            glob.append('let mutable %s : %s = %s' % (self.static_local_name(d), self.value_type(d.type, d), self.global_init(d, t)))
        out = ['// Generated from EPA SWMM 5.2.4 by tools/c2x/emit_fsharp.py. Do not edit by hand;',
               '// fix the translator, Crt.fs or Overrides.fs instead.',
               'module Swmm5.Engine',
               '#nowarn "25" "26" "64" "1182" "3370" "0020" "40"',
               '',
               'open System',
               'open Swmm5',
               '']
        for n, v in self.F.enum_consts.items():
            out.append('[<Literal>]')
            out.append('let %s = %s' % (fident(n), int_lit(v, 'i')))
        out.append('')
        for bts, name in self.lits.items():
            out.append('let %s = R.Lit(%s)' % (name, fs_string(bts)))
        out.append('')
        first = True
        for sig, (name, ft) in self.delegates.items():
            out.append(('type ' if first else 'and ') + self.delegate_decl(name, ft))
            first = False
        for name, c in self.F.records.items():
            lines = self.record(name, c, first)
            if not first:
                lines[0] = lines[0]
            out += lines
            first = False
        out.append('')
        out += glob + ['']
        out.append('[<AbstractClass; Sealed>]')
        out.append('type S private () =')
        out += funcs
        open(os.path.join(outdir, 'Engine.fs'), 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = FSEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_fs')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
    print('%d switch sections fall through into the next (written out): %s' % (len(em.fallthroughs), ', '.join(em.fallthroughs)))
    print('jumps after restructuring (kind, needs a flag): %s' % ', '.join('%s %s: %d' % (k[0], 'flag' if k[1] else 'no flag', v)
                                                                       for k, v in sorted(em.jump_stats.items())))
