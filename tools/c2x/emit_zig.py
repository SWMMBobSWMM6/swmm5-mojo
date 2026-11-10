"""
emit_zig.py - EPA SWMM 5.2.4 C  ->  Zig 0.15 (one generated file, zig/src/swmm5.zig; the C runtime is
zig/src/rt.zig, imported as R; the command line is zig/src/main.zig).

Zig has C's memory model, so the translation keeps C's data layout and pointers instead of re-shaping
them the way the managed-language back ends do:
  int/unsigned/long/unsigned long/short/char -> i32/u32/i64/u64/i16/i8 (char is signed on x86-64)
  double/float                               -> f64/f32
  struct/union                               -> extern struct/extern union (C's layout: sizeof agrees,
                                                and a comptime check in the generated file proves it)
  T*                                         -> [*c]T  (Zig's C pointer: nullable, indexable, arithmetic)
  T[N]                                       -> [N]T ; void* -> ?*anyopaque ; FILE* -> [*c]R.FILE
  function pointer                           -> ?*const fn (...) T
  + - * on integers                          -> +% -% *% (C's wrap-around on x86-64; Zig traps or
                                                assumes no overflow otherwise); / and % on signed ->
                                                @divTrunc/@rem; << >> -> R.shl/R.shr
  double -> int                              -> R.d2i (x86-64 cvttsd2si: NaN or out of range -> INT_MIN)
  int -> double, double -> float, ...        -> @floatFromInt, @floatCast ... written out (Zig converts
                                                nothing implicitly that could lose information)
  a[i] with a signed i                       -> a[ix(i)] (sign-extended, so a C negative index works)
  assignment, ++, ?:, comma as values        -> labelled blocks (`b1: { ...; break :b1 v; }`) and
                                                if-expressions, evaluated in C's order
  float literals                             -> decimal when the f128 -> f64 path cannot double-round,
                                                else hexadecimal; a literal next to another constant is
                                                typed @as(f64, ..) so Zig rounds each step as C does
  locals                                     -> hoisted to the top of the function with unique names,
                                                zero-initialised (Zig forbids shadowing)
  switch                                     -> a Zig switch inside a labelled block (C's break leaves
                                                the block); fall-through copies the next section's code
  libm (exp, log, pow, sin, ...)             -> R.exp ... : the system libm, reached through pointers
                                                LLVM cannot see into (no pow(x,2) -> x*x rewriting);
                                                fabs/sqrt/floor/ceil -> @abs/@sqrt/@floor/@ceil (exact)
Written by Claude (Anthropic) for Robert Dickinson; see zig/README.md.
"""
import os, re, sys, math, collections, struct
from fractions import Fraction
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key

ZIG_KEYWORDS = set('''addrspace align allowzero and anyframe anytype asm break callconv catch comptime const continue
defer else enum errdefer error export extern fn for if inline linksection noalias noinline nosuspend opaque or orelse
packed pub resume return struct suspend switch test threadlocal try union unreachable usingnamespace var volatile
while'''.split())
ZIG_PRIMS = set('''isize usize c_char c_short c_ushort c_int c_uint c_long c_ulong c_longlong c_ulonglong c_longdouble
f16 f32 f64 f80 f128 bool anyopaque void noreturn type anyerror comptime_int comptime_float true false null undefined
'''.split())
# names the generated file defines or imports itself
OWN = {'std', 'R', 'ix', 'main'}


def is_prim(n):
    return n in ZIG_PRIMS or re.fullmatch(r'[iu]\d+', n) is not None


def zfield(n):
    """a struct field name (fields may be spelled like primitives; keywords need @"")"""
    return '@"%s"' % n if n in ZIG_KEYWORDS or n in ('true', 'false', 'null', 'undefined') else n


def zstr(b):
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


INT_KINDS = {T.CHAR_S: ('i8', 8, True), T.SCHAR: ('i8', 8, True), T.CHAR_U: ('u8', 8, False),
             T.UCHAR: ('u8', 8, False), T.SHORT: ('i16', 16, True), T.USHORT: ('u16', 16, False),
             T.INT: ('i32', 32, True), T.UINT: ('u32', 32, False), T.LONG: ('i64', 64, True),
             T.ULONG: ('u64', 64, False), T.LONGLONG: ('i64', 64, True), T.ULONGLONG: ('u64', 64, False),
             T.BOOL: ('u8', 8, False), T.ENUM: ('i32', 32, True)}


def info(t):
    """('int', zig, bits, signed) | ('flt', zig, bits) | ('ptr', pointee) | ('arr', elem, n) | ('rec', t)
    | ('fn', t) | ('void',)"""
    t = canon(t)
    k = t.kind
    if k in INT_KINDS:
        return ('int',) + INT_KINDS[k]
    if k == T.DOUBLE:
        return ('flt', 'f64', 64)
    if k == T.FLOAT:
        return ('flt', 'f32', 32)
    if k == T.POINTER:
        return ('ptr', canon(t.get_pointee()))
    if k == T.CONSTANTARRAY:
        return ('arr', canon(t.element_type), t.element_count)
    if k == T.INCOMPLETEARRAY:
        return ('ptr', canon(t.element_type))
    if k == T.RECORD:
        return ('rec', t)
    if k in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
        return ('fn', t)
    if k == T.VOID:
        return ('void',)
    raise ValueError('type %s' % t.spelling)


def wrap_int(v, bits, signed):
    v &= (1 << bits) - 1
    if signed and v >= 1 << (bits - 1):
        v -= 1 << bits
    return v


def f32_round(x):
    return struct.unpack('<f', struct.pack('<f', x))[0]


def float_text(v, bits):
    """Zig literal text for the f(bits) value v: Zig parses a decimal literal to f128 and then rounds it to
    f(bits), so the shortest decimal is used only when that second rounding cannot move it off v (it is far
    from a rounding midpoint); otherwise the exact hexadecimal form"""
    if v != v or v in (float('inf'), float('-inf')):
        raise ValueError('special float literal')
    neg = math.copysign(1.0, v) < 0
    a = -v if neg else v
    if a == 0:
        s = '0.0'
    elif a == int(a) and a < 2 ** 53:
        s = '%d.0' % int(a)
    else:
        mbits = 53 if bits == 64 else 24
        exact = Fraction(a)
        e = exact.numerator.bit_length() - exact.denominator.bit_length()
        if Fraction(2) ** e > exact:
            e -= 1
        ulp = Fraction(2) ** (e - mbits + 1)
        below = ulp / 2 if exact == Fraction(2) ** e else ulp
        lo, hi = exact - below / 2, exact + ulp / 2
        cands = [repr(a)] if bits == 64 else ['%.*g' % (p, a) for p in range(1, 10)]
        s = None
        for cand in cands:
            d = Fraction(cand)
            if _round_bits(d, mbits) != exact:
                continue
            margin = d / (2 ** 112)
            if d - lo > margin and hi - d > margin:
                s = cand
                break
        if s is None:
            s = float(a).hex()
        elif 'e' not in s and '.' not in s:
            s += '.0'
    return ('-' if neg else '') + s


def _round_bits(x, mbits):
    """x (positive Fraction) rounded to mbits significant bits, ties to even (no exponent range limits)"""
    if x == 0:
        return x
    e = x.numerator.bit_length() - x.denominator.bit_length()
    if Fraction(2) ** e > x:
        e -= 1
    scale = Fraction(2) ** (mbits - 1 - e)
    y = x * scale
    n = y.numerator // y.denominator
    r = y - n
    if r > Fraction(1, 2) or (r == Fraction(1, 2) and n % 2 == 1):
        n += 1
    return Fraction(n) / scale


class E:
    """a translated expression: Zig code for a value of C type t (canonical). isbool: the code is a Zig bool
    standing for C's int 0/1. lit: the value, when the expression is a numeric constant. strlit: bytes of a
    string literal (t is its char array type)."""
    __slots__ = ('code', 't', 'isbool', 'lit', 'strlit')

    def __init__(self, code, t, isbool=False, lit=None, strlit=None):
        self.code, self.t, self.isbool, self.lit, self.strlit = code, t, isbool, lit, strlit


# C library functions the runtime provides (rt.zig), called with arguments converted to their C prototypes
LIBC = {'strcpy', 'strlen', 'strcmp', 'atoi', 'fopen', 'feof', 'fclose', 'strtok', 'atof', 'ftell', 'strstr',
        'rewind', 'strchr', 'strcat', 'fseek', 'fseeko', 'remove', 'strcspn', 'toupper', 'strrchr', 'fflush',
        'fgets', 'realpath', 'mkstemp', 'free', 'calloc', 'malloc', 'realloc', 'fwrite', 'fread', 'memset',
        'strtod', 'time', 'ctime', 'difftime', 'exp', 'log', 'log10', 'pow', 'sin', 'cos', 'tan', 'asin',
        'acos', 'atan'}
VARIADIC = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}
BUILTIN_MATH = {'fabs': '@abs', 'sqrt': '@sqrt', 'floor': '@floor', 'ceil': '@ceil'}

# C functions the runtime replaces by hand (rt.zig): getAbsolutePath calls realpath into a fixed buffer
# (EPA defect 3 in lessons/02) and project_createMatrix zeroes only an eighth of what it allocates (defect 5).
# The translation of the rest of EPA, including odesolve.c and mempool.c, is mechanical.
SKIP_FUNCS = set()


def var_init(d):
    """the initializer of a variable declaration, or None (the children also hold array size expressions)"""
    toks = list(d.get_tokens())
    depth = 0
    eq = None
    for tk in toks:
        sp = tk.spelling
        if sp in ('[', '('):
            depth += 1
        elif sp in (']', ')'):
            depth -= 1
        elif sp == '=' and depth == 0:
            eq = tk.extent.start.offset
            break
    if eq is None:
        return None
    for x in reversed(kids(d)):
        if x.kind not in (K.TYPE_REF, K.PARM_DECL) and x.extent.start.offset > eq:
            return x
    return None


class ZigEmitter:
    def __init__(self, F):
        self.F = F
        self.problems = []
        self.defects = []
        self.fn_types = collections.OrderedDict()
        self._names()

    # ================================================================== naming
    def _names(self):
        F = self.F
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        taken = set(OWN)

        def fresh(n, suffix='_'):
            nn = n
            while nn in taken or nn in ZIG_KEYWORDS or is_prim(nn):
                nn += suffix
            taken.add(nn)
            return nn
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
        self.recname = {}
        for name in F.records:
            self.recname[name] = fresh(name)
        self.ename = {}
        for n in F.enum_consts:
            self.ename[n] = fresh(n)
        # object-like numeric macros with one value everywhere become named constants
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

    def zt(self, t):
        i = info(t)
        k = i[0]
        if k in ('int', 'flt'):
            return i[1]
        if k == 'void':
            return 'void'
        if k == 'rec':
            return self.rec(t)
        if k == 'arr':
            return '[%d]%s' % (i[2], self.zt(i[1]))
        if k == 'fn':
            return self.fn_sig(t)
        p = i[1]
        if p.kind == T.VOID:
            return '?*anyopaque'
        if p.kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return '?*const ' + self.fn_sig(p)
        if front.is_file_ptr(t):
            return '[*c]R.FILE'
        return '[*c]' + self.zt(p)

    def fn_sig(self, ft):
        ft = canon(ft)
        args = [self.zt(a) for a in ft.argument_types()]
        return 'fn (%s) %s' % (', '.join(args), self.zt(ft.get_result()))

    def zero(self, t):
        i = info(t)
        if i[0] == 'int':
            return '0'
        if i[0] == 'flt':
            return '0.0'
        if i[0] == 'ptr':
            return 'null'
        return 'std.mem.zeroes(%s)' % self.zt(t)

    # ================================================================== literals
    def int_text(self, v):
        return '(%d)' % v if v < 0 else '%d' % v

    def flt_text(self, v, bits):
        if v != v:
            return 'R.nan%d' % bits
        if v in (float('inf'), float('-inf')):
            return '(-R.inf%d)' % bits if v < 0 else 'R.inf%d' % bits
        s = float_text(v, bits)
        return '(%s)' % s if s.startswith('-') else s

    def typed_lit(self, e):
        """a literal operand typed, so that Zig evaluates an all-constant operation in the C type"""
        i = info(e.t)
        if e.lit is not None and i[0] in ('int', 'flt') and not e.code.startswith('@as('):
            return '@as(%s, %s)' % (i[1], e.code)
        return e.code

    # ================================================================== conversions
    def conv(self, e, dst):
        """Zig code for e converted to C type dst"""
        d = canon(dst)
        di = info(d)
        if di[0] == 'void':
            return e.code
        if e.isbool:
            if di[0] == 'int':
                return '@as(%s, @intFromBool(%s))' % (di[1], e.code)
            if di[0] == 'flt':
                return '@as(%s, @floatFromInt(@intFromBool(%s)))' % (di[1], e.code)
            self.problem(None, 'bool to %s' % d.spelling)
            return e.code
        si = info(e.t)
        if di[0] == 'int':
            if si[0] == 'int':
                if e.lit is not None:
                    return self.int_text(wrap_int(e.lit, di[2], di[3]))
                if si[1] == di[1]:
                    return e.code
                if di[2] > si[2]:
                    if si[3] and not di[3]:     # sign-extend, then reinterpret
                        return '@as(%s, @bitCast(@as(i%d, %s)))' % (di[1], di[2], e.code)
                    return '@as(%s, %s)' % (di[1], e.code)
                if di[2] == si[2]:
                    return '@as(%s, @bitCast(%s))' % (di[1], e.code)
                if si[3] == di[3]:
                    return '@as(%s, @truncate(%s))' % (di[1], e.code)
                return '@as(%s, @bitCast(@as(%s%d, @truncate(%s))))' % (di[1], 'i' if si[3] else 'u', di[2], e.code)
            if si[0] == 'flt':
                if e.lit is not None:
                    v = e.lit
                    if v == v and -2 ** 63 <= v < 2 ** 63:
                        n = int(v)
                        if di[2] == 64 or (di[3] and -2 ** 31 <= n < 2 ** 31):
                            return self.int_text(wrap_int(n, di[2], di[3]))
                return 'R.d2i(%s, %s)' % (di[1], e.code)
            if si[0] == 'ptr':
                self.problem(None, 'pointer to integer')
                return '@as(%s, @intCast(@intFromPtr(%s)))' % (di[1], e.code)
        if di[0] == 'flt':
            if si[0] == 'int':
                if e.lit is not None:
                    v = float(e.lit) if di[2] == 64 else f32_round(float(e.lit))
                    return self.flt_text(v, di[2])
                return '@as(%s, @floatFromInt(%s))' % (di[1], e.code)
            if si[0] == 'flt':
                if si[2] == di[2]:
                    return e.code
                if e.lit is not None:
                    v = e.lit if di[2] == 64 else f32_round(e.lit)
                    return self.flt_text(v, di[2])
                if di[2] > si[2]:
                    return '@as(f64, %s)' % e.code
                return '@as(f32, @floatCast(%s))' % e.code
        if di[0] == 'ptr':
            if e.lit == 0 and si[0] == 'int':
                return 'null'
            if e.code == 'null':
                return 'null'
            if si[0] == 'arr' or (si[0] == 'ptr' and e.t.kind == T.INCOMPLETEARRAY):
                if e.strlit is not None:
                    return self.strlit_ptr(e.strlit)
                code = '&%s[0]' % self.paren(e.code)       # array decay: a pointer to the first element
                if canon(si[1]) == canon(di[1]):
                    return code
                return '@as(%s, @ptrCast(@alignCast(%s)))' % (self.zt(d), code)
            if si[0] == 'fn':
                return '&%s' % e.code
            if si[0] == 'ptr':
                if self.zt(e.t) == self.zt(d):
                    return e.code
                if di[1].kind == T.VOID:
                    return '@as(?*anyopaque, @ptrCast(%s))' % e.code
                return '@as(%s, @ptrCast(@alignCast(%s)))' % (self.zt(d), e.code)
            if si[0] == 'int':
                self.problem(None, 'integer to pointer')
                return '@as(%s, @ptrFromInt(@as(usize, @intCast(%s))))' % (self.zt(d), e.code)
        if di[0] == 'rec' or di[0] == 'arr':
            return e.code
        self.problem(None, 'conversion %s -> %s' % (e.t.spelling, d.spelling))
        return e.code

    def as_bool(self, e):
        if e.isbool:
            return e.code
        i = info(e.t)
        if i[0] in ('int', 'flt'):
            if e.lit is not None:
                return 'true' if e.lit != 0 else 'false'
            return '(%s != 0)' % e.code
        if i[0] == 'ptr':
            return '(%s != null)' % e.code
        if i[0] in ('arr', 'fn'):
            return 'true'
        self.problem(None, 'condition of type %s' % e.t.spelling)
        return e.code

    def cond(self, c):
        return self.as_bool(self.ex(c))

    def val(self, c, t=None):
        """code of expression c converted to type t (default: c's own type)"""
        return self.conv(self.ex(c), c.type if t is None else t)

    @staticmethod
    def paren(s):
        if re.fullmatch(r'[\w.\[\]@"]+', s) and not s.startswith('-'):
            return s
        if s.startswith('(') and s.endswith(')') and ZigEmitter._balanced(s[1:-1]):
            return s
        return '(' + s + ')'

    @staticmethod
    def _balanced(s):
        d = 0
        q = False
        i = 0
        while i < len(s):
            ch = s[i]
            if q:
                if ch == '\\':
                    i += 2
                    continue
                if ch == '"':
                    q = False
            elif ch == '"':
                q = True
            elif ch in '([{':
                d += 1
            elif ch in ')]}':
                d -= 1
                if d < 0:
                    return False
            i += 1
        return d == 0

    def problem(self, c, msg):
        where = ''
        if c is not None and c.location.file is not None:
            where = '%s:%d: ' % (os.path.basename(c.location.file.name), c.location.line)
        self.problems.append(where + msg)

    # ================================================================== expressions
    def ex(self, c):
        m = getattr(self, 'x_' + c.kind.name, None)
        if m is None:
            self.problem(c, 'unhandled expression ' + c.kind.name)
            return E('@compileError("%s")' % c.kind.name, canon(c.type))
        return m(c)

    def x_INTEGER_LITERAL(self, c):
        t = canon(c.type)
        toks = [x.spelling for x in c.get_tokens()]
        v = None
        if len(toks) == 1 and re.fullmatch(r'(0[xX][0-9a-fA-F]+|\d+)[uUlL]*', toks[0]):
            s = re.sub(r'[uUlL]+$', '', toks[0])
            v = int(s, 16) if s[:2].lower() == '0x' else (int(s, 8) if len(s) > 1 and s[0] == '0' else int(s))
        else:
            r = evaluate(c)
            v = r[1] if r else 0
        i = info(t)
        v = wrap_int(v, i[2], i[3])
        if len(toks) == 1 and toks[0] in self.mname and self.mval[toks[0]][0] == 'int':
            return E(self.mname[toks[0]], t, lit=v)
        return E(self.int_text(v), t, lit=v)

    def x_FLOATING_LITERAL(self, c):
        t = canon(c.type)
        i = info(t)
        toks = [x.spelling for x in c.get_tokens()]
        if len(toks) == 1 and re.fullmatch(r'(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?[fFlL]?', toks[0]):
            txt = toks[0].rstrip('fFlL')
            v = float(Fraction(txt)) if i[2] == 64 else float(_round_bits(Fraction(txt), 24))
            return E(self.flt_text(v, i[2]), t, lit=v)
        if len(toks) == 1 and toks[0] in self.mname and self.mval[toks[0]][0] == 'float' and i[2] == 64:
            txt = self.mval[toks[0]][1].rstrip('fFlL')
            return E(self.mname[toks[0]], t, lit=float(Fraction(txt)))
        r = evaluate(c)
        v = r[1] if r else 0.0
        if i[2] == 32:
            v = f32_round(v)
        return E(self.flt_text(v, i[2]), t, lit=v)

    def x_CHARACTER_LITERAL(self, c):
        r = evaluate(c)
        v = r[1] if r else 0
        t = canon(c.type)
        if 32 <= v < 127 and chr(v) not in '\\\'':
            return E("'%s'" % chr(v), t, lit=v)
        return E(str(v), t, lit=v)

    def x_STRING_LITERAL(self, c):
        b = self.string_bytes(c)
        return E('R.s(%s)' % zstr(b), canon(c.type), strlit=b)

    def strlit_ptr(self, b):
        return 'R.s(%s)' % zstr(b)

    def string_bytes(self, c):
        sp = c.spelling
        if sp.startswith('"'):
            segs = re.findall(r'"((?:[^"\\]|\\.)*)"', sp)
            return b''.join(self.decode_c_string(x) for x in segs)
        toks = [t.spelling for t in c.get_tokens()]
        parts = [t for t in toks if t.startswith('"')]
        if parts and all(p.startswith('"') for p in toks if p.strip()):
            return b''.join(self.decode_c_string(p[1:-1]) for p in parts)
        v = evaluate(c)
        if v and v[0] == 'str':
            return v[1]
        if len(toks) == 1:
            for b, m in self.F.macros.items():
                if toks[0] in m and m[toks[0]][0] == 'str':
                    return self.decode_c_string(m[toks[0]][1][1:-1])
        if parts:
            return b''.join(self.decode_c_string(p[1:-1]) for p in parts)
        raise ValueError('cannot read string literal at %s' % c.location)

    @staticmethod
    def decode_c_string(s):
        out = bytearray()
        i = 0
        esc = {'n': 10, 't': 9, 'r': 13, '\\': 92, '"': 34, "'": 39, 'a': 7, 'b': 8, 'f': 12, 'v': 11, '?': 63}
        while i < len(s):
            ch = s[i]
            if ch == '\\':
                n = s[i + 1]
                if n == 'x':
                    m = re.match(r'[0-9a-fA-F]+', s[i + 2:])
                    out.append(int(m.group(0), 16) & 255)
                    i += 2 + len(m.group(0))
                    continue
                if n in '01234567':
                    m = re.match(r'[0-7]{1,3}', s[i + 1:])
                    out.append(int(m.group(0), 8) & 255)
                    i += 1 + len(m.group(0))
                    continue
                out.append(esc[n])
                i += 2
                continue
            out += ch.encode('latin-1')
            i += 1
        return bytes(out)

    def x_GNU_NULL_EXPR(self, c):
        return E('null', canon(c.type))

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        t = canon(c.type)
        if d is None:
            self.problem(c, 'unresolved name %s' % c.spelling)
            return E(c.spelling, t)
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return E(self.int_text(d.enum_value), t, lit=d.enum_value)
            return E(self.ename[d.spelling], t, lit=d.enum_value)
        if d.kind == K.FUNCTION_DECL:
            return E(self.func_name(d), canon(d.type))
        if d.kind == K.PARM_DECL:
            return E(self.local_name(d), t)
        if d.kind == K.VAR_DECL:
            if d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL:
                if d.storage_class == front.ci.StorageClass.STATIC:
                    return E(self.slname[decl_key(d)], t)
                if d.storage_class != front.ci.StorageClass.EXTERN:
                    return E(self.local_name(d), t)
            if d.spelling in ('stdout', 'stderr'):
                return E('R.' + d.spelling, t)
            return E(self.global_name(d), t)
        self.problem(c, 'reference to %s' % d.kind)
        return E(d.spelling, t)

    def func_name(self, d):
        keys = self.F.func_by_decl.get(d.spelling) or []
        cand = [k for k in keys if k[0] == self.cur_file] or \
               [k for k in keys if self.F.funcs[k].storage_class != front.ci.StorageClass.STATIC]
        if not cand:
            self.problem(d, 'no definition for function %s' % d.spelling)
            return d.spelling
        return self.fname[cand[0]]

    def func_def(self, d):
        keys = self.F.func_by_decl.get(d.spelling) or []
        cand = [k for k in keys if k[0] == self.cur_file] or \
               [k for k in keys if self.F.funcs[k].storage_class != front.ci.StorageClass.STATIC]
        return self.F.funcs[cand[0]] if cand else None

    def global_name(self, d):
        k = decl_key(d)
        if k in self.gname:
            return self.gname[k]
        for gk, c in self.F.globals.items():
            if c.spelling == d.spelling and not front.is_static(c):
                return self.gname[gk]
        self.problem(d, 'no definition for global %s' % d.spelling)
        return d.spelling

    def local_name(self, d):
        k = decl_key(d)
        if k not in self.locals:
            self.problem(d, 'local %s used before its declaration' % d.spelling)
            return d.spelling
        return self.locals[k]

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
            return E(self.conv(E(e.code, it), ct), ct)
        if ct.kind == T.POINTER and it.kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return E('&' + e.code, ct)
        return self.converted(e, ct)

    def converted(self, e, t):
        """E for e converted to C type t (keeps literal values for folding)"""
        t = canon(t)
        code = self.conv(e, t)
        lit = None
        ti = info(t)
        if e.lit is not None and not e.isbool:
            si = info(e.t)
            if ti[0] == 'int' and si[0] == 'int':
                lit = wrap_int(e.lit, ti[2], ti[3])
            elif ti[0] == 'flt' and si[0] in ('int', 'flt'):
                lit = float(e.lit) if ti[2] == 64 else f32_round(float(e.lit))
            elif ti[0] == 'int' and si[0] == 'flt' and re.fullmatch(r'\(?-?\d+\)?', code):
                lit = int(code.strip('()'))
        return E(code, t, lit=lit)

    def x_CSTYLE_CAST_EXPR(self, c):
        inner = kids(c)[-1]
        t = canon(c.type)
        if t.kind == T.VOID:
            e = self.ex(inner)
            return E(e.code, t)
        e = self.ex(inner)
        it = canon(inner.type)
        if t.kind == T.POINTER and it.kind in (T.CONSTANTARRAY,):
            return E(self.conv(e, t), t)
        return self.converted(e, t)

    def x_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        return E(self.paren(e.code), e.t, e.isbool, e.lit, e.strlit)

    def x_CXX_UNARY_EXPR(self, c):
        v = evaluate(c)
        t = canon(c.type)
        if v is None:
            self.problem(c, 'sizeof without a value')
            return E('0', t, lit=0)
        return E(str(v[1]), t, lit=v[1])

    # ---------------------------------------------------------------- lvalues
    def lv(self, c):
        """Zig place expression for the C lvalue c"""
        s = c
        while s.kind == K.PAREN_EXPR:
            s = kids(s)[0]
        if s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1 and canon(kids(s)[0].type) == canon(s.type):
            return self.lv(kids(s)[0])
        return self.ex(s).code

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, ixe = kids(c)
        if info(base.type)[0] == 'int':
            base, ixe = ixe, base
        t = canon(c.type)
        b = self.array_base(base)
        return E('%s[%s]' % (self.paren(b), self.index(ixe)), t)

    def array_base(self, base):
        s = base
        while s.kind == K.PAREN_EXPR:
            s = kids(s)[0]
        if s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1:
            ch = kids(s)[0]
            if canon(ch.type).kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) and canon(s.type).kind == T.POINTER:
                e = self.ex(ch)
                if e.strlit is not None:
                    return self.strlit_ptr(e.strlit)
                return e.code
        return self.ex(base).code

    def index(self, ixe):
        e = self.ex(ixe)
        i = info(e.t) if not e.isbool else ('int', 'i32', 32, True)
        if e.isbool:
            return '@intFromBool(%s)' % e.code
        if e.lit is not None:
            if e.lit >= 0:
                return str(e.lit)
            return 'ix(@as(i64, %d))' % e.lit
        if i[0] != 'int':
            self.problem(ixe, 'non-integer index')
            return e.code
        if i[3]:
            return 'ix(%s)' % e.code
        return e.code

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        f = c.referenced
        fn = zfield(f.spelling)
        bt = canon(base.type)
        b = self.ex(base).code
        if bt.kind == T.POINTER:
            code = '%s.*.%s' % (self.paren(b), fn)
        else:
            code = '%s.%s' % (self.paren(b), fn)
        return E(code, canon(c.type))

    # ---------------------------------------------------------------- unary
    def x_UNARY_OPERATOR(self, c):
        op = unop(c)
        a = kids(c)[0]
        t = canon(c.type)
        if op == '&':
            sa = strip(a)
            if canon(sa.type).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
                return E('&' + self.ex(sa).code, t)
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '*':
                return E(self.val(kids(sa)[0]), t)
            return E('&' + self.paren(self.lv(a)), t)
        if op == '*':
            ai = info(a.type)
            if ai[0] == 'ptr' and ai[1].kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
                return self.ex(a)
            return E('%s.*' % self.paren(self.val(a)), t)
        if op == '!':
            return E('!%s' % self.paren(self.cond(a)), t, isbool=True)
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
                return E('(-%%%s)' % self.paren(self.conv(e, t)), t)
            if e.lit is not None:
                v = -e.lit
                return E(self.flt_text(v, i[2]), t, lit=v)
            return E('(-%s)' % self.paren(self.conv(e, t)), t)
        if op == '~':
            if e.lit is not None:
                v = wrap_int(~e.lit, i[2], i[3])
                return E(self.int_text(v), t, lit=v)
            return E('(~%s)' % self.paren(self.conv(e, t)), t)
        self.problem(c, 'unary ' + op)
        return e

    def step(self, t):
        """(+= code for one step, -= code) for an lvalue of C type t"""
        i = info(t)
        if i[0] == 'int':
            return '+%= 1', '-%= 1'
        if i[0] == 'flt':
            return '+= 1.0', '-= 1.0'
        return '+= 1', '-= 1'

    def incdec_expr(self, a, op, t):
        inc, dec = self.step(a.type)
        st = inc if '++' in op else dec
        n = self.fresh_label()
        p = '__p%d' % n
        if op.startswith('pre'):
            code = '__b%d: { const %s = &%s; %s.* %s; break :__b%d %s.*; }' % (n, p, self.paren(self.lv(a)), p, st, n, p)
        else:
            code = '__b%d: { const %s = &%s; const __v%d = %s.*; %s.* %s; break :__b%d __v%d; }' % (
                n, p, self.paren(self.lv(a)), n, p, p, st, n, n)
        return E(code, t)

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
            n = self.fresh_label()
            stm = self.expr_stmt(l)
            rv = self.ex(r)
            body = ' '.join(stm)
            return E('__b%d: { %s break :__b%d %s; }' % (n, body, n, self.conv(rv, r.type)), canon(r.type))
        li, ri = info(l.type), info(r.type)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            le, re_ = self.ex(l), self.ex(r)
            if li[0] in ('ptr', 'arr', 'fn') or ri[0] in ('ptr', 'arr', 'fn'):
                return self.ptr_compare(op, l, r, le, re_, t)
            a, b = self.conv(le, l.type), self.conv(re_, r.type)
            if le.lit is not None and re_.lit is not None:
                a = self.typed_lit(E(a, canon(l.type), lit=le.lit))
            return E('(%s %s %s)' % (a, op, b), t, isbool=True)
        if li[0] in ('ptr', 'arr') or ri[0] in ('ptr', 'arr'):
            return self.ptr_arith(op, l, r, t)
        le, re_ = self.ex(l), self.ex(r)
        return self.arith(op, le, re_, t, l.type, r.type)

    def arith(self, op, le, re_, t, lt, rt):
        """C arithmetic op on operands already converted (by the AST) to the operation's type"""
        i = info(t)
        if op in ('<<', '>>'):
            a = self.conv(le, t)
            b = self.conv(re_, rt)
            if le.lit is not None and re_.lit is not None:
                v = wrap_int(le.lit << re_.lit if op == '<<' else le.lit >> re_.lit, i[2], i[3])
                return E(self.int_text(v), t, lit=v)
            if le.lit is not None:
                a = '@as(%s, %s)' % (i[1], a)
            return E('R.%s(%s, %s)' % ('shl' if op == '<<' else 'shr', a, b), t)
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
            if op in ('+', '-', '*'):
                return E('(%s %s%% %s)' % (a, op, b), t)
            if op == '/':
                return E(('@divTrunc(%s, %s)' if i[3] else '(%s / %s)') % (a, b), t)
            if op == '%':
                return E(('@rem(%s, %s)' if i[3] else '(%s %% %s)') % (a, b), t)
            if op in ('&', '|', '^'):
                return E('(%s %s %s)' % (a, op, b), t)
        if i[0] == 'flt':
            if op in ('+', '-', '*', '/'):
                lc = self.conv_lit(le, t)
                rc = self.conv_lit(re_, t)
                if lc[1] and rc[1]:
                    return E('(@as(%s, %s) %s %s)' % (i[1], lc[0], op, rc[0]), t)
                return E('(%s %s %s)' % (lc[0], op, rc[0]), t)
        self.problem(None, 'arithmetic %s on %s' % (op, t.spelling))
        return E('(%s %s %s)' % (a, op, b), t)

    def conv_lit(self, e, t):
        """(code converted to t, whether it is a compile-time constant)"""
        code = self.conv(e, t)
        return code, (e.lit is not None and not e.isbool)

    def ptr_compare(self, op, l, r, le, re_, t):
        li, ri = info(l.type), info(r.type)
        if li[0] == 'int' and le.lit == 0:
            return E('(%s %s null)' % (self.conv(re_, r.type), op), t, isbool=True)
        if ri[0] == 'int' and re_.lit == 0:
            return E('(%s %s null)' % (self.conv(le, l.type), op), t, isbool=True)
        a, b = self.conv(le, l.type), self.conv(re_, r.type)
        if op in ('==', '!='):
            return E('(%s %s %s)' % (a, op, b), t, isbool=True)
        return E('(@intFromPtr(%s) %s @intFromPtr(%s))' % (a, op, b), t, isbool=True)

    def ptr_arith(self, op, l, r, t):
        li, ri = info(l.type), info(r.type)
        if op == '-' and li[0] in ('ptr', 'arr') and ri[0] in ('ptr', 'arr'):
            return E('R.pdiff(%s, %s)' % (self.val(l), self.val(r)), t)
        if li[0] in ('ptr', 'arr'):
            p, n, neg = l, r, op == '-'
        else:
            p, n, neg = r, l, False
        pc = self.val(p) if info(p.type)[0] == 'ptr' else self.conv(self.ex(p), t)
        ne = self.ex(n)
        if ne.lit is not None and not ne.isbool:
            v = -ne.lit if neg else ne.lit
            if v >= 0:
                return E('(%s + %d)' % (pc, v), t)
            return E('(%s - %d)' % (pc, -v), t)
        nc = self.conv(ne, n.type)
        if neg:
            return E('R.psub(%s, %s)' % (pc, nc), t)
        return E('R.padd(%s, %s)' % (pc, nc), t)

    # ---------------------------------------------------------------- assignment
    def fresh_label(self):
        self.nlabel += 1
        return self.nlabel

    def assign_expr(self, l, r):
        t = canon(l.type)
        n = self.fresh_label()
        v = self.val(r, t)
        return E('__b%d: { const __v%d: %s = %s; %s = __v%d; break :__b%d __v%d; }' % (
            n, n, self.zt(t), v, self.lv(l), n, n, n), t)

    def compound_parts(self, c):
        """(common C type of the computation, operator) for l op= r"""
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = canon(l.type), canon(r.type)
        li, ri = info(lt), info(rt)
        if op in ('<<', '>>'):
            return self.promoted(lt), op
        if li[0] == 'ptr':
            return lt, op
        if li[0] == 'flt' or ri[0] == 'flt':
            if (li[0] == 'flt' and li[2] == 64) or (ri[0] == 'flt' and ri[2] == 64):
                return self.double_t, op
            return self.float_t, op
        a, b = self.promoted(lt), self.promoted(rt)
        return self.usual(a, b), op

    def promoted(self, t):
        i = info(t)
        if i[0] == 'int' and i[2] < 32:
            return self.int_t
        return canon(t)

    def usual(self, a, b):
        ia, ib = info(a), info(b)
        if ia[1] == ib[1]:
            return a
        if ia[3] == ib[3]:
            return a if ia[2] >= ib[2] else b
        u, s = (a, b) if not ia[3] else (b, a)
        iu, is_ = info(u), info(s)
        if iu[2] >= is_[2]:
            return u
        return s   # the signed type is wider and holds every value of the unsigned one (long vs unsigned int)

    def compound_value(self, c, cur):
        """Zig code for the new value of l in l op= r, where cur is code reading l"""
        l, r = kids(c)
        common, op = self.compound_parts(c)
        lt = canon(l.type)
        li = info(lt)
        if li[0] == 'ptr':
            ne = self.ex(r)
            if ne.lit is not None and ne.lit >= 0:
                return '(%s %s %d)' % (cur, op, ne.lit)
            return 'R.%s(%s, %s)' % ('padd' if op == '+' else 'psub', cur, self.conv(ne, r.type))
        le = E(cur, lt)
        re_ = self.ex(r)
        v = self.arith(op, E(self.conv(le, common), common), E(self.conv(re_, common if op not in ('<<', '>>') else r.type), common if op not in ('<<', '>>') else canon(r.type)), common, common, common if op not in ('<<', '>>') else r.type)
        return self.conv(v, lt)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        l, r = kids(c)
        t = canon(l.type)
        n = self.fresh_label()
        p = '__p%d' % n
        v = self.compound_value(c, '%s.*' % p)
        return E('__b%d: { const %s = &%s; %s.* = %s; break :__b%d %s.*; }' % (n, p, self.paren(self.lv(l)), p, v, n, p), t)

    # ---------------------------------------------------------------- ?:
    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        t = canon(c.type)
        if t.kind == T.VOID:
            return E('if (%s) %s else %s' % (self.cond(cc), self.ex(a).code, self.ex(b).code), t)
        ea, eb = self.ex(a), self.ex(b)
        return E('@as(%s, if (%s) %s else %s)' % (self.zt(t), self.cond(cc), self.conv(ea, t), self.conv(eb, t)), t)

    # ---------------------------------------------------------------- init lists
    def x_INIT_LIST_EXPR(self, c):
        return E(self.init_list(c, c.type), canon(c.type))

    def init_value(self, it, t):
        """initializer item it for an object of C type t"""
        t = canon(t)
        s = strip(it)
        i = info(t)
        if s.kind == K.INIT_LIST_EXPR:
            return self.init_list(s, t)
        if i[0] == 'arr' and s.kind == K.STRING_LITERAL:
            return 'R.arr(%d, %s)' % (i[2], zstr(self.string_bytes(s)))
        return self.val(it, t)

    def init_list(self, c, t):
        t = canon(t)
        items = kids(c)
        i = info(t)
        if i[0] == 'arr' or t.kind == T.INCOMPLETEARRAY:
            et = canon(t.element_type)
            n = t.element_count if t.kind == T.CONSTANTARRAY else len(items)
            if (et.kind == T.POINTER and front.is_char(et.get_pointee()) and items
                    and strip(items[-1]).kind == K.STRING_LITERAL and len(items) == n):
                # a string table with no NULL sentinel (EPA defect 1, lessons/02): add one
                self.defects.append('%s:%d string table without NULL sentinel' % (
                    os.path.basename(c.location.file.name), c.location.line))
                n += 1
            vals = [self.init_value(x, et) for x in items]
            if len(vals) < n:
                vals += [self.zero(et)] * (n - len(vals))
            return '[%d]%s{ %s }' % (n, self.zt(et), ', '.join(vals))
        if i[0] == 'rec':
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for k, f in enumerate(fields):
                if k < len(items):
                    parts.append('.%s = %s' % (zfield(f.spelling), self.init_value(items[k], f.type)))
                else:
                    parts.append('.%s = %s' % (zfield(f.spelling), self.zero(f.type)))
            if record_name(t) in self.F.unions:
                parts = parts[:1]
            return '%s{ %s }' % (self.rec(t), ', '.join(parts))
        if len(items) == 1:
            return self.val(items[0], t)
        self.problem(c, 'init list for %s' % t.spelling)
        return self.zero(t)

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
        if ct.kind == T.POINTER:
            ft = canon(ct.get_pointee())
        else:
            ft = ct
        ptypes = list(ft.argument_types())
        codes = [self.val(a, pt) for a, pt in zip(args, ptypes)]
        fe = self.ex(callee)
        code = fe.code
        if code.startswith('&'):
            code = code[1:]
        elif info(fe.t)[0] == 'ptr':
            code = '%s.?' % self.paren(code)
        return E('%s(%s)' % (code, ', '.join(codes)), t)

    def def_key(self, fdef):
        b = os.path.basename(fdef.location.file.name)
        return (b, fdef.spelling)

    def libc(self, c, name, args, d):
        t = canon(c.type)
        if name in BUILTIN_MATH:
            a = self.val(args[0], list(canon(d.type).argument_types())[0])
            return E('%s(%s)' % (BUILTIN_MATH[name], a), t)
        ptypes = list(canon(d.type).argument_types())
        if name in VARIADIC:
            nfix = VARIADIC[name]
            fixed = [self.val(a, pt) for a, pt in zip(args[:nfix], ptypes)]
            rest = []
            for a in args[nfix:]:
                e = self.ex(a)
                at = canon(a.type)
                rest.append('@as(%s, %s)' % (self.zt(at), self.conv(e, at)))
            return E('R.%s(%s, .{ %s })' % (name, ', '.join(fixed), ', '.join(rest)), t)
        if name not in LIBC:
            self.problem(c, 'library function ' + name)
        codes = [self.val(a, pt) for a, pt in zip(args, ptypes)]
        return E('R.%s(%s)' % (name, ', '.join(codes)), t)

    # ================================================================== statements
    def stmt(self, c, ind):
        k = c.kind
        p = '    ' * ind
        if k == K.COMPOUND_STMT:
            return [p + '{'] + self.block_items(kids(c), ind + 1) + [p + '}']
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
            return [p + 'while (%s) {' % cond] + body + [p + '}']
        if k == K.DO_STMT:
            return self.do_stmt(c, ind)
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            tg = self.targets[-1]
            if tg[0] == 'switch':
                tg[2] = True
                return [p + 'break :%s;' % tg[1]]
            return [p + 'break;']
        if k == K.CONTINUE_STMT:
            return [p + 'continue;']
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'return;']
            if canon(self.cur_ret).kind == T.VOID:
                return [p + x for x in self.expr_stmt(ch[0])] + [p + 'return;']
            return [p + 'return %s;' % self.val(ch[0], self.cur_ret)]
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
            if not self.completes(ch):
                break
        return out

    def body(self, c, ind):
        if c.kind == K.COMPOUND_STMT:
            return self.block_items(kids(c), ind)
        return self.stmt(c, ind)

    def loop_cond(self, c):
        if c is None:
            return 'true'
        v = evaluate(strip(c)) if strip(c).kind in (K.INTEGER_LITERAL, K.FLOATING_LITERAL) else None
        if v is not None and v[1] != 0:
            return 'true'
        return self.cond(c)

    def if_stmt(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        out = [p + 'if (%s) {' % self.cond(ch[0])]
        out += self.body(ch[1], ind + 1)
        if len(ch) > 2:
            if ch[2].kind == K.IF_STMT:
                sub = self.if_stmt(ch[2], ind)
                out.append(p + '} else ' + sub[0].lstrip())
                out += sub[1:]
                return out
            out.append(p + '} else {')
            out += self.body(ch[2], ind + 1)
        out.append(p + '}')
        return out

    def do_stmt(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        self.targets.append(['loop', None, False])
        body = self.body(ch[0], ind + 1)
        self.targets.pop()
        cond = self.loop_cond(ch[1])
        if not self.has_continue(ch[0]):
            if cond == 'true':
                return [p + 'while (true) {'] + body + [p + '}']
            if self.completes(ch[0]):
                body = body + [p + '    if (!%s) break;' % self.paren(cond)]
            return [p + 'while (true) {'] + body + [p + '}']
        n = self.fresh_label()
        v = '__dw%d' % n
        self.hoisted.append((v, 'bool', 'false'))
        return [p + '%s = true;' % v, p + 'while (%s or %s) : (%s = false) {' % (v, self.paren(cond), v)] + body + [p + '}']

    def has_continue(self, c):
        if c.kind == K.CONTINUE_STMT:
            return True
        if c.kind in (K.FOR_STMT, K.WHILE_STMT, K.DO_STMT):
            return False
        return any(self.has_continue(x) for x in kids(c))

    def for_parts(self, c):
        ch = kids(c)
        body = ch[-1]
        parts = ch[:-1]
        toks = list(c.get_tokens())
        depth = 0
        semis = []
        for tk in toks[1:]:
            if tk.spelling == '(':
                depth += 1
            elif tk.spelling == ')':
                depth -= 1
                if depth == 0:
                    break
            elif tk.spelling == ';' and depth == 1:
                semis.append(tk.extent.start.offset)
        init = cond = inc = None
        for x in parts:
            o = x.extent.start.offset
            if o < semis[0]:
                init = x
            elif o < semis[1]:
                cond = x
            else:
                inc = x
        return init, cond, inc, body

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
        self.targets.append(['loop', None, False])
        b = self.body(body, ind + 1)
        self.targets.pop()
        if not incs:
            head = 'while (%s) {' % cs
        elif len(incs) == 1 and not incs[0].startswith('_ =') and incs[0].endswith(';') and incs[0].count(';') == 1:
            head = 'while (%s) : (%s) {' % (cs, incs[0][:-1])
        else:
            head = 'while (%s) : ({ %s }) {' % (cs, ' '.join(incs))
        return out + [p + head] + b + [p + '}']

    def switch(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        e = self.ex(ch[0])
        sel = self.conv(e, self.promoted(ch[0].type)) if not e.isbool else '@as(i32, @intFromBool(%s))' % e.code
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
        n = self.fresh_label()
        lab = '__sw%d' % n
        tg = ['switch', lab, False]
        self.targets.append(tg)
        prongs = []
        has_default = False
        for si, (labels, stmts) in enumerate(sections):
            # the code a section runs: its own, then (C fall-through) the next sections' until one ends
            run = []
            j = si
            while True:
                run += sections[j][1]
                if not self.completes_list(sections[j][1]) or j + 1 >= len(sections):
                    break
                j += 1
            lines = self.block_items(run, ind + 3)
            if None in labels:
                has_default = True
                prongs.append((None, lines))
            else:
                prongs.append((labels, lines))
        self.targets.pop()
        out = [p + 'switch (%s) {' % sel]
        for labels, lines in prongs:
            head = 'else' if labels is None else ', '.join(labels)
            if not lines:
                out.append(p + '    %s => {},' % head)
            else:
                out.append(p + '    %s => {' % head)
                out += [('    ' + x) for x in lines]
                out.append(p + '    },')
        if not has_default:
            out.append(p + '    else => {},')
        out.append(p + '}')
        if tg[2]:
            return [p + '%s: {' % lab] + ['    ' + x for x in out] + [p + '}']
        return out

    def case_value(self, x, st):
        e = self.ex(x)
        if e.lit is not None:
            pt = self.promoted(st)
            i = info(pt)
            v = wrap_int(e.lit, i[2], i[3])
            if re.fullmatch(r"[A-Za-z_]\w*|'.'", e.code) and v == e.lit:
                return e.code
            return self.int_text(v)
        return e.code

    # --- does control reach the end of statement c? (Zig rejects code after a statement that cannot)
    def completes(self, c):
        k = c.kind
        if k in (K.RETURN_STMT, K.BREAK_STMT, K.CONTINUE_STMT, K.GOTO_STMT):
            return False
        if k == K.COMPOUND_STMT:
            return self.completes_list(kids(c))
        if k == K.IF_STMT:
            ch = kids(c)
            if len(ch) < 3:
                return True
            return self.completes(ch[1]) or self.completes(ch[2])
        if k in (K.WHILE_STMT, K.FOR_STMT, K.DO_STMT):
            ch = kids(c)
            if k == K.WHILE_STMT:
                cond = ch[0]
            elif k == K.DO_STMT:
                cond = ch[1]
            else:
                cond = self.for_parts(c)[1]
            if cond is not None and self.loop_cond_const(cond) is not True:
                return True
            return self.has_break(ch[-1] if k != K.DO_STMT else ch[0])
        if k == K.SWITCH_STMT:
            body = kids(c)[-1]
            items = kids(body) if body.kind == K.COMPOUND_STMT else [body]
            if not any(self.has_default(it) for it in items):
                return True
            if self.has_break(body):
                return True
            # every path leaves by return/continue: the last section decides
            sec = []
            for it in items:
                x = it
                while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                    x = kids(x)[-1]
                sec.append(x)
            return self.completes_list(sec[-1:]) if sec else True
        if k in (K.CASE_STMT, K.DEFAULT_STMT):
            return self.completes(kids(c)[-1])
        return True

    def completes_list(self, stmts):
        for s in stmts:
            if not self.completes(s):
                return False
        return True

    def loop_cond_const(self, cond):
        s = strip(cond)
        if s.kind in (K.INTEGER_LITERAL, K.FLOATING_LITERAL):
            v = evaluate(s)
            return v is not None and v[1] != 0
        return None

    def has_default(self, it):
        x = it
        while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
            if x.kind == K.DEFAULT_STMT:
                return True
            x = kids(x)[-1]
        return False

    def has_break(self, c):
        if c.kind == K.BREAK_STMT:
            return True
        if c.kind in (K.FOR_STMT, K.WHILE_STMT, K.DO_STMT, K.SWITCH_STMT):
            return False
        return any(self.has_break(x) for x in kids(c))

    # ---------------------------------------------------------------- expression statements
    def simple_lv(self, c):
        """True if the lvalue c can be evaluated twice with no difference (no calls, no side effects)"""
        s = c
        while s.kind in (K.PAREN_EXPR,) or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1):
            s = kids(s)[0]
        k = s.kind
        if k == K.DECL_REF_EXPR:
            return True
        if k in (K.INTEGER_LITERAL, K.CHARACTER_LITERAL):
            return True
        if k == K.MEMBER_REF_EXPR:
            return self.simple_lv(kids(s)[0])
        if k == K.ARRAY_SUBSCRIPT_EXPR:
            return all(self.simple_lv(x) for x in kids(s))
        if k == K.UNARY_OPERATOR and unop(s) in ('*', '-', '+'):
            return self.simple_lv(kids(s)[0])
        if k == K.BINARY_OPERATOR and binop(s) in ('+', '-', '*'):
            return all(self.simple_lv(x) for x in kids(s))
        return False

    def expr_stmt(self, c):
        """Zig statements (without indentation) for the C expression statement c"""
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
            return ['%s = %s;' % (self.lv(l), self.val(r, l.type))]
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmt(l) + self.expr_stmt(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            l, r = kids(s)
            if self.simple_lv(l):
                cur = self.lv(l)
                op = binop(s)[:-1]
                lt = canon(l.type)
                li, ri = info(lt), info(r.type)
                common, _ = self.compound_parts(s)
                if li[0] == 'int' and canon(common) == lt and op in ('+', '-', '*'):
                    return ['%s %s%%= %s;' % (cur, op, self.val(r, lt))]
                if li[0] == 'flt' and canon(common) == lt and op in ('+', '-', '*', '/'):
                    return ['%s %s= %s;' % (cur, op, self.val(r, lt))]
                return ['%s = %s;' % (cur, self.compound_value(s, cur))]
            n = self.fresh_label()
            p = '__p%d' % n
            return ['{ const %s = &%s; %s.* = %s; }' % (p, self.paren(self.lv(l)), p, self.compound_value(s, p + '.*'))]
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            inc, dec = self.step(a.type)
            st = inc if '++' in unop(s) else dec
            return ['%s %s;' % (self.lv(a), st)]
        if s.kind == K.CONDITIONAL_OPERATOR:
            cc, a, b = kids(s)
            return ['if (%s) {' % self.cond(cc)] + ['    ' + x for x in self.expr_stmt(a)] + ['} else {'] + \
                   ['    ' + x for x in self.expr_stmt(b)] + ['}']
        if s.kind == K.DECL_REF_EXPR:
            return []
        e = self.ex(s)
        if canon(s.type).kind == T.VOID:
            return ['%s;' % e.code]
        if e.lit is not None and s.kind != K.CALL_EXPR:
            return []
        return ['_ = %s;' % e.code]

    # ---------------------------------------------------------------- declarations
    def declare_local(self, d, zty, init='zero'):
        n = d.spelling
        nn, i = n, 2
        while nn in self.used_names or nn in self.top or nn in ZIG_KEYWORDS or is_prim(nn):
            nn = '%s_%d' % (n, i)
            i += 1
        self.used_names.add(nn)
        self.locals[decl_key(d)] = nn
        return nn

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
        name = self.declare_local(d, None)
        self.hoisted.append((name, self.zt(t), self.zero(t)))
        if it is None:
            return []
        return [p + '%s = %s;' % (name, self.init_value(it, t))]

    # ================================================================== functions
    def param_uses(self, body, params):
        """(params assigned or address-taken, params referenced at all)"""
        pk = {decl_key(x): x for x in params}
        mut, used = set(), set()

        def ref(x):
            x = strip(x)
            while x.kind == K.PAREN_EXPR:
                x = strip(kids(x)[0])
            if x.kind == K.DECL_REF_EXPR and x.referenced is not None:
                return decl_key(x.referenced)
            return None

        def walk(c):
            if c.kind == K.DECL_REF_EXPR and c.referenced is not None:
                k = decl_key(c.referenced)
                if k in pk:
                    used.add(k)
            if c.kind == K.BINARY_OPERATOR and binop(c) == '=' or c.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
                k = ref(kids(c)[0])
                if k in pk:
                    mut.add(k)
            if c.kind == K.UNARY_OPERATOR and unop(c) in ('&', 'pre++', 'pre--', 'post++', 'post--'):
                k = ref(kids(c)[0])
                if k in pk:
                    mut.add(k)
            for x in c.get_children():
                walk(x)
        walk(body)
        return mut, used

    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.cur_ret = c.result_type
        self.nlabel = 0
        self.hoisted = []
        self.targets = []
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        mut, used = self.param_uses(body, params)
        ps = []
        pre = []
        for prm in params:
            nm = self.declare_local(prm, None)
            zty = self.zt(prm.type)
            k = decl_key(prm)
            if k in mut:
                ps.append('%s_arg: %s' % (nm, zty))
                pre.append('    var %s: %s = %s_arg;' % (nm, zty, nm))
                pre.append('    _ = &%s;' % nm)
            else:
                ps.append('%s: %s' % (nm, zty))
                if k not in used:
                    pre.append('    _ = %s;' % nm)
        lines = self.body(body, 1)
        rt = self.zt(c.result_type)
        pub = '' if front.is_static(c) else 'pub '
        out = ['// %s:%d' % (b, c.location.line), '%sfn %s(%s) %s {' % (pub, self.fname[key], ', '.join(ps), rt)]
        out += pre
        seen = set()
        for nm, zty, z in self.hoisted:
            if nm in seen:
                continue
            seen.add(nm)
            out.append('    var %s: %s = %s;' % (nm, zty, z))
            out.append('    _ = &%s;' % nm)
        out += lines
        if canon(c.result_type).kind != T.VOID and self.completes(body):
            out.append('    return %s;' % self.zero(c.result_type))
        out.append('}')
        return out

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        kind = 'extern union' if name in self.F.unions else 'extern struct'
        out = ['const %s = %s {' % (self.recname.get(name, name), kind)]
        for f in fields:
            out.append('    %s: %s,' % (zfield(f.spelling), self.zt(f.type)))
        out.append('};')
        return out

    def global_decl(self, name, d, owner):
        self.cur_file = owner
        self.locals = {}
        self.nlabel = 0
        self.cur_decl = d
        t = canon(d.type)
        it = var_init(d)
        if it is None:
            if t.kind == T.INCOMPLETEARRAY:
                self.problem(d, 'incomplete array %s' % d.spelling)
            return 'var %s: %s = %s;' % (name, self.zt(t), self.zero(t))
        s = strip(it)
        if t.kind == T.INCOMPLETEARRAY or (info(t)[0] == 'arr' and s.kind == K.INIT_LIST_EXPR):
            v = self.init_list(s, t)
            zty = v[:v.index('{')].strip()
            return 'var %s: %s = %s;' % (name, zty, v)
        return 'var %s: %s = %s;' % (name, self.zt(t), self.init_value(it, t))

    def emit(self, outfile):
        self.int_t = None
        self.double_t = None
        self.float_t = None
        self.grown = {}
        self.cur_decl = None
        self._find_types()
        self.static_locals = []
        funcs = []
        for key, c in self.F.funcs.items():
            if key in SKIP_FUNCS:
                continue
            try:
                funcs += self.function(key, c) + ['']
            except Exception as ex:
                import traceback
                traceback.print_exc()
                self.problems.append('%s:%s CRASH %s' % (key[0], key[1], ex))
        out = ['// Generated from EPA SWMM 5.2.4 by tools/c2x/emit_zig.py. Do not edit by hand: fix the',
               '// translator or the runtime (rt.zig) instead.',
               '', 'const std = @import("std");', 'const R = @import("rt.zig");', 'const ix = R.ix;', '']
        out.append('// ---------------------------------------------------------------- records')
        for name, c in self.F.records.items():
            out += self.record(name, c)
        out += ['', '// ---------------------------------------------------------------- constants']
        for n, v in self.F.enum_consts.items():
            out.append('const %s: i32 = %d;' % (self.ename[n], v))
        for n, (kind, s) in self.mval.items():
            if kind == 'int':
                v = re.sub(r'[uUlL]+$', '', s)
                if len(v.lstrip('-')) > 1 and v.lstrip('-').startswith('0'):
                    v = str(int(v, 8))
                out.append('const %s = %s;' % (self.mname[n], v))
            else:
                txt = s.rstrip('fFlL')
                out.append('const %s: f64 = %s;' % (self.mname[n], float_text(float(Fraction(txt)), 64)))
        out += ['', '// ---------------------------------------------------------------- globals']
        for k, c in self.F.globals.items():
            out.append(self.global_decl(self.gname[k], c, self.F.global_owner[k]))
        for d, b in self.static_locals:
            out.append(self.global_decl(self.slname[decl_key(d)], d, b))
        out += ['', '// ---------------------------------------------------------------- functions']
        out += funcs
        # Zig compiles only what is reached from main; referencing every function makes the compiler check
        # the whole translation (the stepping API, unused helpers), not just the command line's paths
        out += ['// every translated function is compiled and type-checked, reached or not', 'comptime {']
        for key, c in self.F.funcs.items():
            if key not in SKIP_FUNCS:
                out.append('    _ = &%s;' % self.fname[key])
        out += ['}', '']
        out += ['// C layout check: every record has the size EPA\'s C compiler gives it', 'comptime {']
        for name, c in self.F.records.items():
            sz = canon(c.type).get_size()
            out.append('    if (@sizeOf(%s) != %d) @compileError("%s");' % (self.recname.get(name, name), sz, name))
        out.append('}')
        open(outfile, 'w').write('\n'.join(out) + '\n')
        return self.problems

    def _find_types(self):
        """canonical int / double / float types, taken from the AST"""
        for b, tu in self.F.tus.items():
            for c in tu.cursor.walk_preorder():
                if c.kind == K.VAR_DECL:
                    k = canon(c.type).kind
                    if k == T.INT and self.int_t is None:
                        self.int_t = canon(c.type)
                    elif k == T.DOUBLE and self.double_t is None:
                        self.double_t = canon(c.type)
                    elif k == T.FLOAT and self.float_t is None:
                        self.float_t = canon(c.type)
                if self.int_t is not None and self.double_t is not None and self.float_t is not None:
                    return


if __name__ == '__main__':
    F = front.Front()
    em = ZigEmitter(F)
    out = sys.argv[1] if len(sys.argv) > 1 else 'zig/src/swmm5.zig'
    probs = em.emit(out)
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
