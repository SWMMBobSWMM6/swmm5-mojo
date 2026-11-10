"""
emit_pascal.py - EPA SWMM 5.2.4 C  ->  Free Pascal 3.2 (one generated unit, pascal/src/swmm5eng.pas; the C runtime
is the unit swmmcrt, pascal/src/swmmcrt.pas; the command line is pascal/src/runswmm.pas).

Free Pascal has typed pointers with arithmetic ({$POINTERMATH ON}), records with C's layout ({$PACKRECORDS C}),
goto and nested functions, so the translation keeps C's data layout and pointers, as the Zig back end does
(this back end reuses its analysis):
  int/unsigned/long/unsigned long/short  -> Int32/UInt32/Int64/UInt64/SmallInt ; char -> AnsiChar (C's char
                                            is signed: a char becomes an int through ShortInt)
  double/float                           -> Double/Single
  every integer + - * / % << >>          -> wrapped in a cast to the C type (FPC may evaluate 32-bit operands
                                            in 64 bits; {$Q-}{$R-}: wrap-around), div/mod, SarLongint for >>
  every float literal                    -> a typed constant (an untyped Pascal real constant is Extended:
                                            x * 0.1 would be computed on the x87 in 80 bits, lessons/23);
                                            its value is written exactly (bit pattern when the decimal could
                                            round twice on the way in)
  double -> int                          -> D2I (x86-64 cvttsd2si: NaN or out of range -> INT_MIN)
  struct/union                           -> record / variant record ; T* -> named pointer type (PTNode ...)
  T[N]                                   -> array[0..N-1] of T ; function pointer -> procedural type
  && || !                                -> and or not on Booleans with {$B-} (short-circuit, as C)
  assignment / ++ used as a value        -> generic var-parameter helpers (Asg, PostInc)
  ?:                                     -> if/else when it is a whole assignment or return; a Tern* helper
                                            when both arms are safe to evaluate eagerly; else a nested
                                            function (evaluated lazily, in place, like C)
  for (;;) with continue                 -> while ... with `goto` to the increment
  switch                                 -> case ... of, C's break -> goto past the case; fall-through copies
                                            the next section's code
  locals                                 -> hoisted, unique case-insensitive names, zeroed at entry
  libm                                   -> c_exp ... : glibc's libm through `external 'm'` (cdecl)
Written by Claude (Anthropic) for Robert Dickinson; see pascal/README.md.
"""
import os, re, sys, math, collections, struct
from fractions import Fraction
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_zig import (ZigEmitter, E, info, wrap_int, f32_round, _round_bits, var_init, INT_KINDS, LIBC,
                      VARIADIC)

PAS_KEYWORDS = set('''absolute and array asm begin case const constructor destructor div do downto else end file for
function goto if implementation in inherited inline interface label mod nil not object of operator or packed procedure
program record reintroduce repeat self set shl shr string then to type unit until uses var while with xor as class
dispinterface except exports finalization finally initialization library on out property raise resourcestring
threadvar try is generic specialize abstract alias assembler cdecl cppdecl default export external far forward index
name near override overload private protected public published read register safecall softfloat stdcall virtual
write result exit break continue true false'''.split())
# System unit and runtime identifiers the generated code uses or must not hide
PAS_SYSTEM = set('''inc dec ord chr abs sqr sqrt trunc round int frac length high low sizeof new dispose assigned exp ln sin
cos pi writeln readln halt move fillchar str val copy pos insert delete concat random odd swap lo hi ptr addr
integer longint cardinal word byte shortint smallint int64 qword uint64 int32 uint32 int16 uint16 int8 uint8 double
single extended real char ansichar pansichar ppansichar pointer boolean text sarlongint sarint64 ptruint ptrint
nativeint nativeuint system objpas swmmcrt swmm5eng runswmm d2i d2l d2u d2ul u2d i2f tern asg postinc predec preinc
postdec ternp terni32 ternu32 terni64 ternu64 ternd ternf ternc pcfile tcfile'''.split())
RESERVED = PAS_KEYWORDS | PAS_SYSTEM

INT_PAS = {T.CHAR_S: 'AnsiChar', T.SCHAR: 'ShortInt', T.CHAR_U: 'Byte', T.UCHAR: 'Byte', T.SHORT: 'SmallInt',
           T.USHORT: 'Word', T.INT: 'Int32', T.UINT: 'UInt32', T.LONG: 'Int64', T.ULONG: 'UInt64',
           T.LONGLONG: 'Int64', T.ULONGLONG: 'UInt64', T.BOOL: 'Byte', T.ENUM: 'Int32'}
TERN = {'Int32': 'TernI32', 'UInt32': 'TernU32', 'Int64': 'TernI64', 'UInt64': 'TernU64', 'Double': 'TernD',
        'Single': 'TernF', 'AnsiChar': 'TernC'}
MATH_EXT = {'exp', 'log', 'log10', 'pow', 'sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'sqrt', 'fabs', 'floor', 'ceil'}


def pstr(b):
    """a Pascal string constant for the bytes b ('' for none)"""
    out = []
    run = []
    for ch in b:
        if 32 <= ch < 127:
            run.append("''" if ch == 39 else chr(ch))
        else:
            if run:
                out.append("'" + ''.join(run) + "'")
                run = []
            out.append('#%d' % ch)
    if run:
        out.append("'" + ''.join(run) + "'")
    return ''.join(out) if out else "''"


def pchar_code(b):
    """PAnsiChar code for a C string literal"""
    if not b:
        return "PAnsiChar('')"
    s = pstr(b)
    return "PAnsiChar(%s)" % s


def is_char_t(t):
    return canon(t).kind == T.CHAR_S


class PascalEmitter(ZigEmitter):
    # ================================================================== naming (Pascal is case-insensitive)
    def _names(self):
        F = self.F
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        taken = set(RESERVED)

        def fresh(n, suffix='_'):
            nn = n
            while nn.lower() in taken:
                nn += suffix
            taken.add(nn.lower())
            return nn
        self.recname = {}
        for name in F.records:
            self.recname[name] = fresh(name)
        self.fname = {}
        for (b, n), c in F.funcs.items():
            self.fname[(b, n)] = fresh(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.gname = {}
        for k, c in F.globals.items():
            n = c.spelling
            b = F.global_owner[k]
            self.gname[k] = fresh(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.slname = {}
        for (b, n), c in F.funcs.items():
            def walk(x):
                for y in x.get_children():
                    if y.kind == K.VAR_DECL and y.storage_class == front.ci.StorageClass.STATIC:
                        self.slname[decl_key(y)] = fresh('%s_%s' % (self.fname[(b, n)], y.spelling))
                    walk(y)
            walk(c)
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
            if kind not in ('int', 'float') or n in F.enum_consts or n in cnt or n in self.recname:
                continue
            self.mname[n] = fresh(n)
            self.mval[n] = (kind, s)
        # record fields: unique within their record, case-insensitively; keywords get a suffix
        self.fieldname = {}
        for name, c in F.records.items():
            used = set()
            for f in kids(c):
                if f.kind != K.FIELD_DECL:
                    continue
                nn = f.spelling
                while nn.lower() in used or nn.lower() in PAS_KEYWORDS:
                    nn += '_'
                used.add(nn.lower())
                self.fieldname[(name, f.spelling)] = nn
        self.top = taken
        self.ptypes = collections.OrderedDict()      # pointer type name -> pointee type text
        self.atypes = collections.OrderedDict()      # array type name -> array type text
        self.proctypes = collections.OrderedDict()   # signature -> (name, decl text)
        self.flits = collections.OrderedDict()       # (bits, value bits) -> (name, decl lines)

    def pfield(self, f):
        p = f.semantic_parent
        rn = record_name(p.type) if p is not None else None
        return self.fieldname.get((rn, f.spelling), f.spelling)

    # ================================================================== types
    def zt(self, t):
        t = canon(t)
        i = info(t)
        k = i[0]
        if k == 'int':
            return INT_PAS[t.kind]
        if k == 'flt':
            return 'Double' if i[2] == 64 else 'Single'
        if k == 'void':
            return ''
        if k == 'rec':
            return self.rec(t)
        if k == 'arr':
            return 'array[0..%d] of %s' % (i[2] - 1, self.zt(i[1]))
        if k == 'fn':
            return self.proc_type(t)
        return self.ptr_type(i[1])

    def ptr_type(self, p):
        """name of the pointer type to C type p (declared in the generated type section)"""
        p = canon(p)
        if p.kind == T.VOID:
            return 'Pointer'
        if p.kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return self.proc_type(p)
        if p.kind == T.CHAR_S:
            return 'PAnsiChar'
        if p.kind == T.RECORD and p.spelling.replace('struct ', '') in ('_IO_FILE', 'FILE'):
            return 'PCFile'
        if p.kind == T.POINTER and canon(p.get_pointee()).kind == T.CHAR_S:
            return 'PPAnsiChar'
        if p.kind == T.CONSTANTARRAY:
            an = 'TA%d_%s' % (p.element_count, re.sub(r'\W', '', self.zt(p.element_type)))
            self.atypes[an] = self.zt(p)
            inner = an
            name = 'P' + an[1:]
        else:
            inner = self.zt(p)
            name = 'P' + re.sub(r'\W', '', inner)
        if name not in self.ptypes:
            self.ptypes[name] = inner
        return name

    def proc_type(self, ft):
        ft = canon(ft)
        args = [self.zt(a) for a in ft.argument_types()]
        res = self.zt(ft.get_result())
        sig = (tuple(args), res)
        if sig not in self.proctypes:
            name = 'TProc%d' % len(self.proctypes)
            ps = '; '.join('a%d: %s' % (k, a) for k, a in enumerate(args))
            if res:
                d = 'function(%s): %s' % (ps, res)
            else:
                d = 'procedure(%s)' % ps
            self.proctypes[sig] = (name, d)
        return self.proctypes[sig][0]

    def zero_stmt(self, name, t):
        t = canon(t)
        i = info(t)
        if i[0] == 'int':
            return '%s := %s;' % (name, '#0' if t.kind == T.CHAR_S else '0')
        if i[0] == 'flt':
            return '%s := %s;' % (name, self.flit(0.0, i[2]))
        if i[0] == 'ptr':
            return '%s := nil;' % name
        return 'FillChar(%s, SizeOf(%s), 0);' % (name, name)

    # ================================================================== literals
    def int_text(self, v):
        if v > 2 ** 63 - 1:
            return 'UInt64($%X)' % v
        return '(%d)' % v if v < 0 else '%d' % v

    def flit(self, v, bits):
        """name of the typed constant holding the float value v (f64 or f32)"""
        pack = struct.pack('<d', v) if bits == 64 else struct.pack('<f', v)
        key = (bits, pack)
        if key in self.flits:
            return self.flits[key][0]
        ty = 'Double' if bits == 64 else 'Single'
        if v != v:
            name = 'FNaN' if bits == 64 else 'FsNaN'
        elif v in (float('inf'), float('-inf')):
            name = ('FInf' if v > 0 else 'FmInf') + ('' if bits == 64 else 's')
        else:
            txt = repr(v) if bits == 64 else ('%.9g' % v)
            nm = txt.replace('-', 'm').replace('+', '').replace('.', 'p').replace('e', 'e')
            name = ('F' if bits == 64 else 'Fs') + nm
            if math.copysign(1.0, v) < 0 and v == 0:
                name = 'Fm0p0' if bits == 64 else 'Fsm0p0'
        while name.lower() in self.top:
            name += '_'
        self.top.add(name.lower())
        txt = self.exact_decimal(v, bits)
        bitsv = struct.unpack('<Q', pack)[0] if bits == 64 else struct.unpack('<I', pack)[0]
        if txt is None:
            qt = 'Int64' if bits == 64 else 'LongWord'
            hx = '$%016X' % bitsv if bits == 64 else '$%08X' % bitsv
            decl = ['  %s_bits: %s = %s; { %r }' % (name, qt, hx, v)], ['  %s: %s absolute %s_bits;' % (name, ty, name)]
        else:
            decl = ['  %s: %s = %s;' % (name, ty, txt)], []
        self.flits[key] = (name, decl)
        return name

    @staticmethod
    def exact_decimal(v, bits):
        """decimal text for v that Free Pascal's reader (decimal -> 80-bit Extended -> f(bits)) cannot round to
        anything else, or None (the caller writes the bit pattern instead)"""
        if v != v or v in (float('inf'), float('-inf')):
            return None
        if math.copysign(1.0, v) < 0:
            return None
        if v == 0:
            return '0.0'
        if v == int(v) and v < 2 ** 53:
            return '%d.0' % int(v)
        mbits = 53 if bits == 64 else 24
        exact = Fraction(v)
        e = exact.numerator.bit_length() - exact.denominator.bit_length()
        if Fraction(2) ** e > exact:
            e -= 1
        if e < (-1022 if bits == 64 else -126):
            return None
        ulp = Fraction(2) ** (e - mbits + 1)
        below = ulp / 2 if exact == Fraction(2) ** e else ulp
        lo, hi = exact - below / 2, exact + ulp / 2
        cands = [repr(v)] if bits == 64 else ['%.*g' % (p, v) for p in range(1, 10)]
        for cand in cands:
            d = Fraction(cand)
            if _round_bits(d, mbits) != exact:
                continue
            margin = d / (2 ** 58)
            if d - lo > margin and hi - d > margin:
                if 'e' not in cand and '.' not in cand:
                    cand += '.0'
                return cand
        return None

    def flt_text(self, v, bits):
        return self.flit(v, bits)

    # ================================================================== conversions
    def conv(self, e, dst):
        d = canon(dst)
        di = info(d)
        if di[0] == 'void':
            return e.code
        if e.isbool:
            if di[0] == 'int':
                if d.kind == T.CHAR_S:
                    return 'AnsiChar(Ord(%s))' % e.code
                return '%s(Ord(%s))' % (INT_PAS[d.kind], e.code)
            if di[0] == 'flt':
                return 'I2F%s(Ord(%s))' % ('D' if di[2] == 64 else 'S', e.code)
            return e.code
        si = info(e.t)
        st = canon(e.t)
        if di[0] == 'int':
            dn = INT_PAS[d.kind]
            if si[0] == 'int':
                sn = INT_PAS[st.kind]
                if e.lit is not None:
                    v = wrap_int(e.lit, di[2], di[3])
                    if d.kind == T.CHAR_S:
                        return '#%d' % (v & 255) if v >= 0 else 'AnsiChar(%d)' % (v & 255)
                    return self.int_text(v)
                if sn == dn:
                    return e.code
                src = e.code
                if st.kind == T.CHAR_S:
                    src = 'ShortInt(%s)' % e.code
                    sn = 'ShortInt'
                    if dn == 'ShortInt':
                        return src
                if d.kind == T.CHAR_S:
                    return 'AnsiChar(%s)' % src
                if si[3] and not di[3] and di[2] > si[2]:
                    return '%s(Int64(%s))' % (dn, src)
                return '%s(%s)' % (dn, src)
            if si[0] == 'flt':
                if e.lit is not None:
                    v = e.lit
                    if v == v and -2 ** 31 <= v < 2 ** 31:
                        return self.conv(E(str(int(v)), self.int_t, lit=int(v)), d)
                fn = {'Int32': 'D2I', 'Int64': 'D2L', 'UInt32': 'D2U', 'UInt64': 'D2UL'}.get(dn)
                if fn:
                    return '%s(%s)' % (fn, e.code)
                if d.kind == T.CHAR_S:
                    return 'AnsiChar(D2I(%s))' % e.code
                return '%s(D2I(%s))' % (dn, e.code)
            if si[0] == 'ptr':
                self.problem(None, 'pointer to integer')
                return '%s(PtrUInt(%s))' % (dn, e.code)
        if di[0] == 'flt':
            if si[0] == 'int':
                if e.lit is not None:
                    v = float(e.lit) if di[2] == 64 else f32_round(float(e.lit))
                    return self.flit(v, di[2])
                src = e.code
                if st.kind == T.CHAR_S:
                    src = 'ShortInt(%s)' % src
                if INT_PAS[st.kind] == 'UInt64':
                    return 'U2%s(%s)' % ('D' if di[2] == 64 else 'S', src)
                return 'I2F%s(%s)' % ('D' if di[2] == 64 else 'S', src)
            if si[0] == 'flt':
                if si[2] == di[2]:
                    return e.code
                if e.lit is not None:
                    v = e.lit if di[2] == 64 else f32_round(e.lit)
                    return self.flit(v, di[2])
                if di[2] > si[2]:
                    return 'Double(%s)' % e.code
                return 'D2F(%s)' % e.code
        if di[0] == 'ptr':
            pt = self.zt(d)
            if (e.lit == 0 and si[0] == 'int') or e.code == 'nil':
                return 'nil'
            if si[0] == 'arr' or (si[0] == 'ptr' and st.kind == T.INCOMPLETEARRAY):
                if e.strlit is not None:
                    return self.strlit_ptr(e.strlit)
                code = '@%s[0]' % self.paren(e.code)
                if canon(si[1]) == canon(di[1]):
                    return code
                return '%s(%s)' % (pt, code)
            if si[0] == 'fn':
                return '@' + e.code
            if si[0] == 'ptr':
                if self.zt(st) == pt:
                    return e.code
                return '%s(%s)' % (pt, e.code)
            if si[0] == 'int':
                self.problem(None, 'integer to pointer')
                return '%s(PtrUInt(%s))' % (pt, e.code)
        if di[0] in ('rec', 'arr'):
            return e.code
        self.problem(None, 'conversion %s -> %s' % (st.spelling, d.spelling))
        return e.code

    def as_bool(self, e):
        if e.isbool:
            return e.code
        i = info(e.t)
        if i[0] in ('int', 'flt'):
            if e.lit is not None:
                return 'True' if e.lit != 0 else 'False'
            if canon(e.t).kind == T.CHAR_S:
                return '(%s <> #0)' % e.code
            if i[0] == 'flt':
                return '(%s <> 0)' % e.code
            return '(%s <> 0)' % e.code
        if i[0] == 'ptr':
            if canon(i[1]).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
                return 'Assigned(%s)' % e.code
            return '(%s <> nil)' % e.code
        if i[0] in ('arr', 'fn'):
            return 'True'
        self.problem(None, 'condition of type %s' % canon(e.t).spelling)
        return e.code

    @staticmethod
    def paren(s):
        if re.fullmatch(r'[\w.\[\]^#]+', s):
            return s
        if s.startswith('(') and s.endswith(')') and ZigEmitter._balanced(s[1:-1]):
            return s
        return '(' + s + ')'

    # ================================================================== expressions
    def x_STRING_LITERAL(self, c):
        b = self.string_bytes(c)
        return E(pchar_code(b), canon(c.type), strlit=b)

    def strlit_ptr(self, b):
        return pchar_code(b)

    def x_CHARACTER_LITERAL(self, c):
        r = evaluate(c)
        v = r[1] if r else 0
        return E(str(v), canon(c.type), lit=v)

    def x_GNU_NULL_EXPR(self, c):
        return E('nil', canon(c.type))

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is not None and d.kind == K.VAR_DECL and d.spelling in ('stdout', 'stderr') and \
                not (d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL):
            return E('c_' + d.spelling, canon(c.type))
        return super().x_DECL_REF_EXPR(c)

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) == 1:
            inner = ch[0]
            it, ct = canon(inner.type), canon(c.type)
            if ct.kind == T.POINTER and it.kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
                return E('@' + self.ex(inner).code, ct)
        return super().x_UNEXPOSED_EXPR(c)

    def x_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        return E(self.paren(e.code), e.t, e.isbool, e.lit, e.strlit)

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, ixe = kids(c)
        if info(base.type)[0] == 'int':
            base, ixe = ixe, base
        t = canon(c.type)
        b = self.array_base(base)
        return E('%s[%s]' % (self.paren(b), self.index(ixe)), t)

    def index(self, ixe):
        e = self.ex(ixe)
        if e.isbool:
            return 'Ord(%s)' % e.code
        if e.lit is not None:
            return str(e.lit)
        if canon(e.t).kind == T.CHAR_S:
            return 'ShortInt(%s)' % e.code
        return e.code

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        f = c.referenced
        fn = self.pfield(f)
        bt = canon(base.type)
        b = self.ex(base).code
        if bt.kind == T.POINTER:
            code = '%s^.%s' % (self.paren(b), fn)
        else:
            code = '%s.%s' % (self.paren(b), fn)
        return E(code, canon(c.type))

    def x_UNARY_OPERATOR(self, c):
        op = unop(c)
        a = kids(c)[0]
        t = canon(c.type)
        if op == '&':
            sa = strip(a)
            if canon(sa.type).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
                return E('@' + self.ex(sa).code, t)
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '*':
                return E(self.val(kids(sa)[0]), t)
            return E('@' + self.paren(self.lv(a)), t)
        if op == '*':
            ai = info(a.type)
            if ai[0] == 'ptr' and ai[1].kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
                return self.ex(a)
            return E('%s^' % self.paren(self.val(a)), t)
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
                    return E(self.int_text(v), t, lit=v)
                return E('%s(-%s)' % (INT_PAS[t.kind], self.paren(self.conv(e, t))), t)
            return E('(-%s)' % self.paren(self.conv(e, t)), t)
        if op == '~':
            if e.lit is not None:
                v = wrap_int(~e.lit, i[2], i[3])
                return E(self.int_text(v), t, lit=v)
            return E('%s(not %s)' % (INT_PAS[t.kind], self.paren(self.conv(e, t))), t)
        self.problem(c, 'unary ' + op)
        return e

    def incdec_expr(self, a, op, t):
        i = info(a.type)
        tn = self.zt(a.type)
        if i[0] != 'int' or tn not in ('Int32', 'Int64', 'UInt32', 'UInt64'):
            self.problem(a, '++/-- used as a value on %s' % tn)
        fn = {'pre++': 'PreInc', 'pre--': 'PreDec', 'post++': 'PostInc', 'post--': 'PostDec'}[op]
        return E('specialize %s<%s>(%s)' % (fn, tn, self.lv(a)), t)

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
        pop = {'==': '=', '!=': '<>'}.get(op, op)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            le, re_ = self.ex(l), self.ex(r)
            if li[0] in ('ptr', 'arr', 'fn') or ri[0] in ('ptr', 'arr', 'fn'):
                return self.ptr_compare(op, l, r, le, re_, t)
            a, b = self.conv(le, l.type), self.conv(re_, r.type)
            if le.lit is not None and re_.lit is not None:
                v = {'==': le.lit == re_.lit, '!=': le.lit != re_.lit, '<': le.lit < re_.lit, '>': le.lit > re_.lit,
                     '<=': le.lit <= re_.lit, '>=': le.lit >= re_.lit}[op]
                return E('True' if v else 'False', t, isbool=True)
            return E('(%s %s %s)' % (a, pop, b), t, isbool=True)
        if li[0] in ('ptr', 'arr') or ri[0] in ('ptr', 'arr'):
            return self.ptr_arith(op, l, r, t)
        le, re_ = self.ex(l), self.ex(r)
        return self.arith(op, le, re_, t, l.type, r.type)

    def arith(self, op, le, re_, t, lt, rt):
        i = info(t)
        tn = self.zt(t)
        if op in ('<<', '>>'):
            a = self.conv(le, t)
            b = self.conv(re_, rt)
            if le.lit is not None and re_.lit is not None:
                v = wrap_int(le.lit << re_.lit if op == '<<' else le.lit >> re_.lit, i[2], i[3])
                return E(self.int_text(v), t, lit=v)
            if op == '<<':
                return E('%s(%s shl %s)' % (tn, self.paren(a), self.paren(b)), t)
            if i[3]:
                return E('%s(%s, %s)' % ('SarLongint' if i[2] == 32 else 'SarInt64', a, b), t)
            return E('%s(%s shr %s)' % (tn, self.paren(a), self.paren(b)), t)
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
                    return E(self.int_text(v), t, lit=v)
            pop = {'+': '+', '-': '-', '*': '*', '/': 'div', '%': 'mod', '&': 'and', '|': 'or', '^': 'xor'}[op]
            return E('%s(%s %s %s)' % (tn, self.paren(a), pop, self.paren(b)), t)
        if i[0] == 'flt' and op in ('+', '-', '*', '/'):
            return E('(%s %s %s)' % (a, op, b), t)
        self.problem(None, 'arithmetic %s on %s' % (op, t.spelling))
        return E('(%s %s %s)' % (a, op, b), t)

    def ptr_compare(self, op, l, r, le, re_, t):
        li, ri = info(l.type), info(r.type)
        pop = {'==': '=', '!=': '<>'}.get(op, op)
        fnp = lambda x: info(x.type)[0] == 'ptr' and canon(info(x.type)[1]).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO)
        if (li[0] == 'int' and le.lit == 0) or le.code == 'nil':
            x, xe = r, re_
        elif (ri[0] == 'int' and re_.lit == 0) or re_.code == 'nil':
            x, xe = l, le
        else:
            x = None
        if x is not None:
            code = self.conv(xe, x.type)
            if fnp(x):
                return E(('(not Assigned(%s))' if op == '==' else 'Assigned(%s)') % code, t, isbool=True)
            return E('(%s %s nil)' % (code, pop), t, isbool=True)
        a, b = self.conv(le, l.type), self.conv(re_, r.type)
        return E('(%s %s %s)' % (a, pop, b), t, isbool=True)

    def ptr_arith(self, op, l, r, t):
        li, ri = info(l.type), info(r.type)
        if op == '-' and li[0] in ('ptr', 'arr') and ri[0] in ('ptr', 'arr'):
            return E('Int64(%s - %s)' % (self.val(l), self.val(r)), t)
        if li[0] in ('ptr', 'arr'):
            p, n, neg = l, r, op == '-'
        else:
            p, n, neg = r, l, False
        pc = self.val(p) if info(p.type)[0] == 'ptr' else self.conv(self.ex(p), t)
        ne = self.ex(n)
        nc = self.conv(ne, n.type) if not (ne.lit is not None) else str(ne.lit)
        return E('(%s %s %s)' % (pc, '-' if neg else '+', self.paren(nc)), t)

    # ---------------------------------------------------------------- assignment
    def assign_expr(self, l, r):
        t = canon(l.type)
        return E('specialize Asg<%s>(%s, %s)' % (self.zt(t), self.lv(l), self.val(r, t)), t)

    def compound_value(self, c, cur):
        l, r = kids(c)
        common, op = self.compound_parts(c)
        lt = canon(l.type)
        li = info(lt)
        if li[0] == 'ptr':
            ne = self.ex(r)
            return '(%s %s %s)' % (cur, op, self.paren(self.conv(ne, r.type)))
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
        tn = self.zt(t)
        # a compound assignment used as a value: a nested function does it in place
        body = ['%s := %s;' % (self.lv(l), self.compound_value(c, self.lv(l))), 'Result := %s;' % self.lv(l)]
        if not self.simple_lv(l):
            self.problem(c, 'compound assignment used as a value on a complex lvalue')
        return E(self.nested_fn(tn, body), t)

    def nested_fn(self, tn, body):
        self.nlabel += 1
        name = 'expr_%d' % self.nlabel
        while name.lower() in self.top or name.lower() in self.used_names:
            name += '_'
        self.used_names.add(name.lower())
        self.nested.append(['  function %s: %s;' % (name, tn), '  begin'] + ['    ' + x for x in body] + ['  end;'])
        return '%s()' % name

    # ---------------------------------------------------------------- ?:
    def safe(self, c):
        """True if evaluating C expression c eagerly can neither fault nor have side effects"""
        k = c.kind
        if k in (K.INTEGER_LITERAL, K.FLOATING_LITERAL, K.CHARACTER_LITERAL, K.CXX_UNARY_EXPR):
            return True
        if k in (K.PAREN_EXPR, K.UNEXPOSED_EXPR, K.CSTYLE_CAST_EXPR):
            ch = kids(c)
            if not ch:
                return False
            x = ch[-1]
            if canon(x.type).kind == T.CONSTANTARRAY:
                return False
            return self.safe(x)
        if k == K.DECL_REF_EXPR:
            d = c.referenced
            return d is not None and (d.kind == K.ENUM_CONSTANT_DECL or
                                      (d.kind in (K.VAR_DECL, K.PARM_DECL) and info(d.type)[0] in ('int', 'flt', 'ptr')))
        if k == K.MEMBER_REF_EXPR:
            return canon(kids(c)[0].type).kind != T.POINTER and self.safe(kids(c)[0])
        if k == K.UNARY_OPERATOR:
            return unop(c) in ('-', '+', '!', '~') and self.safe(kids(c)[0])
        if k == K.BINARY_OPERATOR:
            op = binop(c)
            l, r = kids(c)
            if op in ('/', '%') and info(c.type)[0] != 'flt':
                return False
            if op in ('=', ','):
                return False
            if info(l.type)[0] not in ('int', 'flt') or info(r.type)[0] not in ('int', 'flt'):
                return op in ('==', '!=') and self.safe(l) and self.safe(r)
            return self.safe(l) and self.safe(r)
        if k == K.CONDITIONAL_OPERATOR:
            return all(self.safe(x) for x in kids(c))
        if k == K.CALL_EXPR and c.spelling in ('fabs', 'sqrt') and c.referenced is not None and \
                self.func_def(c.referenced) is None:
            return all(self.safe(a) for a in c.get_arguments())
        return False

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        t = canon(c.type)
        tn = self.zt(t)
        ea, eb = self.ex(a), self.ex(b)
        va, vb = self.conv(ea, t), self.conv(eb, t)
        cond = self.cond(cc)
        if self.safe(a) and self.safe(b):
            if tn in TERN:
                return E('%s(%s, %s, %s)' % (TERN[tn], cond, va, vb), t)
            if info(t)[0] == 'ptr':
                return E('%s(TernP(%s, %s, %s))' % (tn, cond, va, vb), t)
        return E(self.nested_fn(tn, ['if %s then Result := %s else Result := %s;' % (cond, va, vb)]), t)

    # ---------------------------------------------------------------- init lists (constant initializers)
    def cinit(self, it, t):
        """a typed-constant initializer for item it of C type t"""
        t = canon(t)
        s = strip(it)
        i = info(t)
        if s.kind == K.INIT_LIST_EXPR:
            return self.cinit_list(s, t)
        if i[0] == 'arr' and s.kind == K.STRING_LITERAL:
            b = self.string_bytes(s)
            b = b[:i[2]] + b'\0' * (i[2] - min(len(b), i[2]))
            return '(%s)' % ', '.join('#%d' % x for x in b)
        if i[0] == 'ptr' and s.kind == K.STRING_LITERAL:
            b = self.string_bytes(s)
            return pstr(b) if b else "''"
        e = self.ex(it)
        if i[0] == 'flt':
            v = e.lit
            if v is None:
                self.problem(it, 'non-constant float initializer')
                return '0'
            v = float(v) if i[2] == 64 else f32_round(float(v))
            if self.bits_mode:
                if i[2] == 64:
                    return '$%016X' % struct.unpack('<Q', struct.pack('<d', v))[0]
                return '$%08X' % struct.unpack('<I', struct.pack('<f', v))[0]
            txt = self.exact_decimal(v, i[2])
            if txt is None:
                self.inexact_init = True
                return repr(v)
            return txt
        if i[0] == 'ptr' and e.strlit is not None:
            return pstr(e.strlit) if e.strlit else "''"
        if i[0] == 'ptr' and (e.code == 'nil' or e.lit == 0):
            return 'nil'
        if i[0] == 'ptr' and canon(e.t).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return '@' + e.code
        return self.conv(e, t)

    def cinit_list(self, c, t):
        t = canon(t)
        items = kids(c)
        i = info(t)
        if i[0] == 'arr' or t.kind == T.INCOMPLETEARRAY:
            et = canon(t.element_type)
            n = t.element_count if t.kind == T.CONSTANTARRAY else len(items)
            if (et.kind == T.POINTER and front.is_char(et.get_pointee()) and items
                    and strip(items[-1]).kind == K.STRING_LITERAL and len(items) == n):
                self.defects.append('%s:%d string table without NULL sentinel' % (
                    os.path.basename(c.location.file.name), c.location.line))
                n += 1
            vals = [self.cinit(x, et) for x in items]
            while len(vals) < n:
                vals.append(self.czero(et))
            self.last_count = n
            return '(%s)' % ', '.join(vals)
        if i[0] == 'rec':
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for k, f in enumerate(fields):
                v = self.cinit(items[k], f.type) if k < len(items) else self.czero(f.type)
                parts.append('%s: %s' % (self.pfield(f), v))
                if record_name(t) in self.F.unions:
                    break
            return '(%s)' % '; '.join(parts)
        if len(items) == 1:
            return self.cinit(items[0], t)
        return self.czero(t)

    def czero(self, t):
        t = canon(t)
        i = info(t)
        if i[0] == 'int':
            return '#0' if t.kind == T.CHAR_S else '0'
        if i[0] == 'flt':
            return '0' if self.bits_mode else '0.0'
        if i[0] == 'ptr':
            return 'nil'
        if i[0] == 'arr':
            return '(%s)' % ', '.join([self.czero(i[1])] * i[2])
        if i[0] == 'rec':
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            if record_name(t) in self.F.unions:
                fields = fields[:1]
            return '(%s)' % '; '.join('%s: %s' % (self.pfield(f), self.czero(f.type)) for f in fields)
        return '0'

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
            codes = [self.val(a, pt) for a, pt in zip(args, ptypes)]
            return E('%s(%s)' % (self.fname[self.def_key(fdef)], ', '.join(codes)), t)
        callee = kids(c)[0]
        ct = canon(strip(callee).type)
        ft = canon(ct.get_pointee()) if ct.kind == T.POINTER else ct
        ptypes = list(ft.argument_types())
        codes = [self.val(a, pt) for a, pt in zip(args, ptypes)]
        fe = self.ex(callee)
        code = fe.code
        if code.startswith('@'):
            code = code[1:]
        return E('%s(%s)' % (self.paren(code), ', '.join(codes)), t)

    def libc(self, c, name, args, d):
        t = canon(c.type)
        ptypes = list(canon(d.type).argument_types())
        if name in VARIADIC:
            nfix = VARIADIC[name]
            fixed = [self.val(a, pt) for a, pt in zip(args[:nfix], ptypes)]
            rest = []
            for a in args[nfix:]:
                e = self.ex(a)
                at = canon(a.type)
                if name == 'sscanf':
                    rest.append(self.conv(e, at))
                    continue
                ai = info(at)
                code = self.conv(e, at)
                if ai[0] == 'int':
                    code = '%s(%s)' % (INT_PAS[at.kind], code) if not re.fullmatch(r'\(?-?\d+\)?', code) else '%s(%s)' % (INT_PAS[at.kind], code)
                elif ai[0] == 'ptr' and e.strlit is None:
                    code = 'PAnsiChar(%s)' % code if canon(ai[1]).kind == T.CHAR_S else 'Pointer(%s)' % code
                rest.append(code)
            return E('c_%s(%s, [%s])' % (name, ', '.join(fixed), ', '.join(rest)), t)
        if name not in LIBC and name not in MATH_EXT:
            self.problem(c, 'library function ' + name)
        codes = [self.val(a, pt) for a, pt in zip(args, ptypes)]
        return E('c_%s(%s)' % (name, ', '.join(codes)), t)

    # ================================================================== statements
    def stmt(self, c, ind):
        k = c.kind
        p = '  ' * ind
        if k == K.COMPOUND_STMT:
            return [p + 'begin'] + self.block_items(kids(c), ind + 1) + [p + 'end;']
        if k == K.DECL_STMT:
            out = []
            for d in kids(c):
                out += self.local_decl(d, ind)
            return out
        if k == K.IF_STMT:
            return self.if_stmt(c, ind)
        if k == K.WHILE_STMT:
            ch = kids(c)
            cond = self.loop_cond(ch[0])
            self.targets.append(['loop', None, False])
            body = self.body(ch[1], ind + 1)
            self.targets.pop()
            return [p + 'while %s do' % cond, p + 'begin'] + body + [p + 'end;']
        if k == K.DO_STMT:
            ch = kids(c)
            self.targets.append(['loop', None, False])
            body = self.body(ch[0], ind + 1)
            self.targets.pop()
            cond = self.loop_cond(ch[1])
            return [p + 'repeat'] + body + [p + 'until not %s;' % self.paren(cond)]
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            tg = self.targets[-1]
            if tg[0] == 'switch':
                tg[2] = True
                return [p + 'goto %s;' % tg[1]]
            return [p + 'Break;']
        if k == K.CONTINUE_STMT:
            for tg in reversed(self.targets):
                if tg[0] == 'loop':
                    if tg[1] is not None:
                        tg[2] = True
                        return [p + 'goto %s;' % tg[1]]
                    return [p + 'Continue;']
            return [p + 'Continue;']
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'Exit;']
            if canon(self.cur_ret).kind == T.VOID:
                return [p + x for x in self.expr_stmt(ch[0])] + [p + 'Exit;']
            return self.return_stmt(ch[0], ind)
        if k == K.NULL_STMT:
            return []
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unhandled statement %s' % k.name)
            return []
        return [p + x for x in self.expr_stmt(c)]

    def block_items(self, items, ind):
        out = []
        for ch in items:
            out += self.stmt(ch, ind)
        return out

    def loop_cond(self, c):
        if c is None:
            return 'True'
        v = evaluate(strip(c)) if strip(c).kind in (K.INTEGER_LITERAL, K.FLOATING_LITERAL) else None
        if v is not None and v[1] != 0:
            return 'True'
        return self.cond(c)

    def if_stmt(self, c, ind):
        p = '  ' * ind
        ch = kids(c)
        out = [p + 'if %s then' % self.cond(ch[0]), p + 'begin']
        out += self.body(ch[1], ind + 1)
        if len(ch) > 2:
            if ch[2].kind == K.IF_STMT:
                sub = self.if_stmt(ch[2], ind)
                out.append(p + 'end')
                out.append(p + 'else ' + sub[0].lstrip())
                out += sub[1:]
                return out
            out.append(p + 'end')
            out.append(p + 'else')
            out.append(p + 'begin')
            out += self.body(ch[2], ind + 1)
        out.append(p + 'end;')
        return out

    def new_label(self, prefix):
        self.nlabel += 1
        name = '%s%d' % (prefix, self.nlabel)
        self.labels.append(name)
        return name

    def for_stmt(self, c, ind):
        p = '  ' * ind
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
        lab = self.new_label('cont') if incs and self.has_continue(body) else None
        tg = ['loop', lab, False]
        self.targets.append(tg)
        b = self.body(body, ind + 1)
        self.targets.pop()
        tail = []
        if incs:
            if lab is not None and tg[2]:
                tail.append(p + '  %s:' % lab)
            elif lab is not None:
                self.labels.remove(lab)
            tail += [p + '  ' + x for x in incs]
        return out + [p + 'while %s do' % cs, p + 'begin'] + b + tail + [p + 'end;']

    def switch(self, c, ind):
        p = '  ' * ind
        ch = kids(c)
        e = self.ex(ch[0])
        sel = self.conv(e, self.promoted(ch[0].type)) if not e.isbool else 'Int32(Ord(%s))' % e.code
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
                        labels.append(self.case_value(xc[0], ch[0].type))
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
        lab = self.new_label('swend')
        tg = ['switch', lab, False]
        self.targets.append(tg)
        prongs = []
        default = None
        for si, (labels, stmts) in enumerate(sections):
            run = []
            j = si
            while True:
                run += sections[j][1]
                if not self.completes_list(sections[j][1]) or j + 1 >= len(sections):
                    break
                j += 1
            lines = self.block_items(run, ind + 2)
            if None in labels:
                default = lines
            else:
                prongs.append((labels, lines))
        self.targets.pop()
        out = [p + 'case %s of' % sel]
        for labels, lines in prongs:
            out.append(p + '  %s:' % ', '.join(labels))
            out.append(p + '  begin')
            out += lines
            out.append(p + '  end;')
        if default is not None:
            out.append(p + '  else')
            out.append(p + '  begin')
            out += default
            out.append(p + '  end;')
        out.append(p + 'end;')
        if not prongs:
            out = [p + 'begin'] + (default or []) + [p + 'end;']
        if tg[2]:
            out.append(p + '%s: ;' % lab)
        else:
            self.labels.remove(lab)
        return out

    def case_value(self, x, st):
        e = self.ex(x)
        if e.lit is not None:
            pt = self.promoted(st)
            i = info(pt)
            v = wrap_int(e.lit, i[2], i[3])
            if re.fullmatch(r"[A-Za-z_]\w*", e.code) and v == e.lit:
                return e.code
            return self.int_text(v)
        return e.code

    def return_stmt(self, e, ind):
        p = '  ' * ind
        rt = self.cur_ret
        cnode, types = self.cond_chain(e)
        if cnode is not None and not (info(rt)[0] == 'ptr' and self.is_null_c(e)):
            cc, a, b = kids(cnode)
            return [p + 'if %s then' % self.cond(cc), p + 'begin',
                    p + '  Exit(%s);' % self.branch_value(a, cnode, types, rt), p + 'end;',
                    p + 'Exit(%s);' % self.branch_value(b, cnode, types, rt)]
        return [p + 'Exit(%s);' % self.val(e, rt)]

    def is_null_c(self, c):
        s = strip(c)
        if s.kind == K.CSTYLE_CAST_EXPR:
            s = strip(kids(s)[-1])
        if s.kind == K.INTEGER_LITERAL:
            v = evaluate(s)
            return v is not None and v[1] == 0
        return s.kind == K.GNU_NULL_EXPR

    def cond_chain(self, r):
        """(?: cursor, [C types it is converted through]) if r is a ?: under casts, else (None, None)"""
        s = r
        types = []
        while True:
            if s.kind == K.PAREN_EXPR:
                s = kids(s)[0]
                continue
            if s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1:
                types.append(s.type)
                s = kids(s)[0]
                continue
            if s.kind == K.CSTYLE_CAST_EXPR and info(s.type)[0] in ('int', 'flt'):
                types.append(s.type)
                s = kids(s)[-1]
                continue
            break
        if s.kind == K.CONDITIONAL_OPERATOR:
            return s, list(reversed(types))
        return None, None

    def branch_value(self, b, cnode, types, lt):
        e = self.converted(self.ex(b), cnode.type)
        prev = cnode.type
        for t in types:
            e = self.converted(e, t)
            prev = t
        return self.conv(e, lt)

    def assign_stmts(self, lvcode, l_t, r):
        """statements for lvalue := r, splitting a ?: on the right into if/else"""
        cnode, types = self.cond_chain(r)
        if cnode is not None and not (info(l_t)[0] == 'ptr' and self.is_null_c(r)):
            cc, a, b = kids(cnode)
            sa = self.branch_assign(lvcode, l_t, a, cnode, types)
            sb = self.branch_assign(lvcode, l_t, b, cnode, types)
            return ['if %s then' % self.cond(cc), 'begin'] + ['  ' + x for x in sa] + ['end', 'else', 'begin'] + \
                   ['  ' + x for x in sb] + ['end;']
        return ['%s := %s;' % (lvcode, self.val(r, l_t))]

    def branch_assign(self, lvcode, l_t, b, cnode, types):
        c2, t2 = self.cond_chain(b)
        if c2 is not None and not types:
            return self.assign_stmts(lvcode, l_t, b)
        return ['%s := %s;' % (lvcode, self.branch_value(b, cnode, types, l_t))]

    def expr_stmt(self, c):
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1 and canon(kids(s)[0].type) == canon(s.type)):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and canon(s.type).kind == T.VOID:
            inner = kids(s)[-1]
            if strip(inner).kind == K.DECL_REF_EXPR:
                return []
            return self.expr_stmt(inner)
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            sr = r
            while sr.kind == K.PAREN_EXPR:
                sr = kids(sr)[0]
            if sr.kind == K.BINARY_OPERATOR and binop(sr) == '=' and canon(sr.type) == canon(l.type):
                # a = b = v
                return self.expr_stmt(sr) + ['%s := %s;' % (self.lv(l), self.lv(kids(sr)[0]))]
            return self.assign_stmts(self.lv(l), canon(l.type), r)
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmt(l) + self.expr_stmt(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            l, r = kids(s)
            if not self.simple_lv(l):
                self.problem(s, 'compound assignment to a complex lvalue')
            cur = self.lv(l)
            return ['%s := %s;' % (cur, self.compound_value(s, cur))]
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            i = info(a.type)
            fn = 'Inc' if '++' in unop(s) else 'Dec'
            if i[0] == 'flt':
                return ['%s := %s %s %s;' % (self.lv(a), self.lv(a), '+' if fn == 'Inc' else '-', self.flit(1.0, i[2]))]
            return ['%s(%s);' % (fn, self.lv(a))]
        if s.kind == K.CONDITIONAL_OPERATOR:
            cc, a, b = kids(s)
            return ['if %s then' % self.cond(cc), 'begin'] + ['  ' + x for x in self.expr_stmt(a)] + \
                   ['end', 'else', 'begin'] + ['  ' + x for x in self.expr_stmt(b)] + ['end;']
        if s.kind == K.DECL_REF_EXPR:
            return []
        e = self.ex(s)
        if s.kind == K.CALL_EXPR:
            return ['%s;' % e.code]
        if e.code.startswith('specialize '):
            return ['%s;' % e.code]
        return []

    # ---------------------------------------------------------------- declarations
    def declare_local(self, d, zty, init='zero'):
        n = d.spelling
        nn, i = n, 2
        while nn.lower() in self.used_names or nn.lower() in self.top:
            nn = '%s_%d' % (n, i)
            i += 1
        self.used_names.add(nn.lower())
        self.locals[decl_key(d)] = nn
        return nn

    def local_decl(self, d, ind):
        p = '  ' * ind
        if d.kind != K.VAR_DECL:
            return []
        if d.storage_class == front.ci.StorageClass.EXTERN:
            return []
        if d.storage_class == front.ci.StorageClass.STATIC:
            self.static_locals.append((d, self.cur_file))
            return []
        t = canon(d.type)
        it = var_init(d)
        name = self.declare_local(d, None)
        self.hoisted.append((name, t))
        if it is None:
            return []
        s = strip(it)
        i = info(t)
        if i[0] == 'arr':
            if s.kind == K.STRING_LITERAL:
                return [p + 'c_strinit(@%s[0], %s, %d);' % (name, pchar_code(self.string_bytes(s)), i[2])]
            if s.kind == K.INIT_LIST_EXPR:
                out = []
                for k, x in enumerate(kids(s)):
                    out += [p + y for y in self.assign_stmts('%s[%d]' % (name, k), canon(i[1]), x)]
                return out
        if i[0] == 'rec' and s.kind == K.INIT_LIST_EXPR:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            out = [p + 'FillChar(%s, SizeOf(%s), 0);' % (name, name)]
            for f, x in zip(fields, kids(s)):
                out += [p + y for y in self.assign_stmts('%s.%s' % (name, self.pfield(f)), canon(f.type), x)]
            return out
        return [p + y for y in self.assign_stmts(name, t, it)]

    # ================================================================== functions
    def fn_header(self, key, c, forward=False):
        params = list(c.get_arguments())
        ps = []
        for prm in params:
            nm = self.locals.get(decl_key(prm), prm.spelling)
            ps.append('%s: %s' % (nm, self.zt(prm.type)))
        rt = self.zt(c.result_type)
        if rt:
            return 'function %s(%s): %s;' % (self.fname[key], '; '.join(ps), rt)
        return 'procedure %s(%s);' % (self.fname[key], '; '.join(ps))

    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.cur_ret = c.result_type
        self.nlabel = 0
        self.hoisted = []
        self.targets = []
        self.labels = []
        self.nested = []
        params = list(c.get_arguments())
        for prm in params:
            self.declare_local(prm, None)
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        lines = self.block_items(kids(body), 1)
        head = self.fn_header(key, c)
        out = ['{ %s:%d }' % (b, c.location.line), head]
        if self.labels:
            out.append('label %s;' % ', '.join(self.labels))
        if self.hoisted:
            out.append('var')
            seen = set()
            for nm, t in self.hoisted:
                if nm in seen:
                    continue
                seen.add(nm)
                out.append('  %s: %s;' % (nm, self.zt(t)))
        for nf in self.nested:
            out += nf
        out.append('begin')
        seen = set()
        for nm, t in self.hoisted:
            if nm in seen:
                continue
            seen.add(nm)
            out.append('  ' + self.zero_stmt(nm, t))
        out += lines
        out.append('end;')
        self.headers[key] = head
        return out

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        rn = self.recname.get(name, name)
        if name in self.F.unions:
            out = ['  %s = record' % rn, '    case Int32 of']
            for k, f in enumerate(fields):
                out.append('      %d: (%s: %s);' % (k, self.fieldname[(name, f.spelling)], self.zt(f.type)))
            out.append('  end;')
            return out
        out = ['  %s = record' % rn]
        for f in fields:
            out.append('    %s: %s;' % (self.fieldname[(name, f.spelling)], self.zt(f.type)))
        out.append('  end;')
        return out

    def record_order(self):
        """records in an order where every record a field embeds by value comes first"""
        deps = {}
        for name, c in self.F.records.items():
            ds = set()
            for f in kids(c):
                if f.kind != K.FIELD_DECL:
                    continue
                t = canon(f.type)
                while t.kind == T.CONSTANTARRAY:
                    t = canon(t.element_type)
                if t.kind == T.RECORD:
                    ds.add(record_name(t))
            deps[name] = ds
        done, order = set(), []

        def visit(n):
            if n in done or n not in deps:
                return
            done.add(n)
            for x in sorted(deps[n]):
                visit(x)
            order.append(n)
        for n in self.F.records:
            visit(n)
        return order

    def global_decl(self, name, d, owner):
        self.cur_file = owner
        self.locals = {}
        self.used_names = set()
        self.nlabel = 0
        t = canon(d.type)
        it = var_init(d)
        if it is None:
            return ['  %s: %s;' % (name, self.zt(t))]
        s = strip(it)
        self.inexact_init = False
        self.last_count = None
        if s.kind == K.INIT_LIST_EXPR:
            v = self.cinit_list(s, t)
            if t.kind == T.INCOMPLETEARRAY or (info(t)[0] == 'arr' and self.last_count != t.element_count):
                ty = 'array[0..%d] of %s' % (self.last_count - 1, self.zt(t.element_type))
            else:
                ty = self.zt(t)
        else:
            v = self.cinit(it, t)
            ty = self.zt(t)
        if self.inexact_init:
            return self.bits_global(name, d, t, s, ty)
        return ['  %s: %s = %s;' % (name, ty, v)]

    def bits_global(self, name, d, t, s, ty):
        """a global of doubles whose decimal values could round twice: stored as bit patterns, seen as doubles"""
        if not re.fullmatch(r'(array\[0\.\.\d+\] of )*(Double|Single)', ty):
            self.problem(d, 'inexact float initializer in a compound global %s' % name)
            return ['  %s: %s;' % (name, ty)]
        self.bits_mode = True
        v = self.cinit_list(s, t) if s.kind == K.INIT_LIST_EXPR else self.cinit(s, t)
        self.bits_mode = False
        qt = ty.replace('Double', 'Int64').replace('Single', 'LongWord')
        return ['  %s_bits: %s = %s;' % (name, qt, v), '  %s: %s absolute %s_bits;' % (name, ty, name)]

    def emit(self, outfile):
        self.int_t = None
        self.double_t = None
        self.float_t = None
        self.cur_decl = None
        self._find_types()
        self.static_locals = []
        self.bits_mode = False
        self.headers = collections.OrderedDict()
        funcs = []
        for key, c in self.F.funcs.items():
            try:
                funcs += self.function(key, c) + ['']
            except Exception as ex:
                import traceback
                traceback.print_exc()
                self.problems.append('%s:%s CRASH %s' % (key[0], key[1], ex))
        gl = []
        for k, c in self.F.globals.items():
            gl += self.global_decl(self.gname[k], c, self.F.global_owner[k])
        for d, b in self.static_locals:
            gl += self.global_decl(self.slname[decl_key(d)], d, b)
        recs = []
        for name in self.record_order():
            recs += self.record(name, self.F.records[name])
        # force the pointer and procedural types every record field needs
        out = ['{ Generated from EPA SWMM 5.2.4 by tools/c2x/emit_pascal.py. Do not edit by hand: fix the',
               '  translator or the runtime (swmmcrt.pas) instead. }',
               '{$mode objfpc}{$H+}{$POINTERMATH ON}{$GOTO ON}{$B-}{$Q-}{$PACKRECORDS C}{$J-}{$INLINE ON}',
               '{ -dRANGECHECK builds a checked engine: every fixed-array index is range-checked }',
               '{$IFDEF RANGECHECK}{$R+}{$ELSE}{$R-}{$ENDIF}',
               'unit swmm5eng;', '', 'interface', '', 'uses swmmcrt;', '']
        api = [k for k in self.F.funcs if k[1] in ('swmm_run', 'swmm_getVersion', 'swmm_getError', 'swmm_getWarnings')]
        out += [self.headers[k] for k in api]
        out += ['', 'implementation', '', 'type']
        for name, a in self.atypes.items():
            out.append('  %s = %s;' % (name, a))
        for name, inner in self.ptypes.items():
            out.append('  %s = ^%s;' % (name, inner))
        for sig, (name, decl) in self.proctypes.items():
            out.append('  %s = %s;' % (name, decl))
        out += recs
        out += ['', '{ C layout check: every record has the size EPA\'s C compiler gives it }']
        for name, c in self.F.records.items():
            sz = canon(c.type).get_size()
            out.append('{$if sizeof(%s) <> %d}{$error %s has the wrong size}{$endif}' % (self.recname.get(name, name), sz, name))
        out += ['', 'const']
        for n, v in self.F.enum_consts.items():
            out.append('  %s = %d;' % (self.ename[n], v))
        for n, (kind, s) in self.mval.items():
            if kind == 'int':
                v = re.sub(r'[uUlL]+$', '', s)
                if len(v.lstrip('-')) > 1 and v.lstrip('-').startswith('0'):
                    v = str(int(v, 8))
                out.append('  %s = %s;' % (self.mname[n], v))
        out += ['', '{ every float literal is a typed constant: Free Pascal computes with an untyped real constant in',
                '  80-bit Extended precision on the x87, C computes in double (lessons/23) }']
        mfl = []
        for n, (kind, s) in self.mval.items():
            if kind == 'float':
                v = float(Fraction(s.rstrip('fFlL')))
                mfl.append((self.mname[n], v))
        for name, (nm, (cdecl, vdecl)) in self.flits.items():
            out += cdecl
        for mn, v in mfl:
            txt = self.exact_decimal(v, 64)
            if txt is None:
                out.append('  %s_bits: Int64 = $%016X;' % (mn, struct.unpack('<Q', struct.pack('<d', v))[0]))
            else:
                out.append('  %s: Double = %s;' % (mn, txt))
        out += ['', 'var']
        for name, (nm, (cdecl, vdecl)) in self.flits.items():
            out += vdecl
        for mn, v in mfl:
            if self.exact_decimal(v, 64) is None:
                out.append('  %s: Double absolute %s_bits;' % (mn, mn))
        out += gl
        out += ['', '{ forward declarations }']
        for key, h in self.headers.items():
            if key not in api:
                out.append(h + ' forward;')
        out += [''] + funcs + ['end.']
        open(outfile, 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = PascalEmitter(F)
    out = sys.argv[1] if len(sys.argv) > 1 else 'pascal/src/swmm5eng.pas'
    probs = em.emit(out)
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
