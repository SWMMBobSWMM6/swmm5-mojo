"""
emit_lua.py - EPA SWMM 5.2.4 C  ->  Lua 5.4 (lua/swmm5: one chunk F_<file>.lua per C file, record constructors in
Types.lua, string literals and constants in Consts.lua). The engine runs in the Lua 5.4 that lupa (PyPI) embeds;
lua/runswmm.py only starts that Lua state and passes the command line.

The Java back end (emit_java.py) supplies the analysis: the front end's pointer modes, names (made unique per
function), Java's reachability rules. Everything Lua writes is its own. The mapping:

  int, enum, char, long   -> Lua integers (64-bit; C's 32-bit int never overflows in EPA's arithmetic, as the
                             Python port, whose integers have no width, showed on all 480 models); unsigned int is
                             kept in 0 .. 2^32-1 by masking (& 0xFFFFFFFF) after + - * << and negation
  int / int, int % int    -> R.idiv (truncating, as C) and math.fmod (which is C's % on two integers); Lua's // and %
                             floor. a >> n on a signed int is a // (1 << n) (Lua's >> is logical)
  double                  -> Lua float; a C conversion int -> double is written (x * 1.0), so a double never holds a
                             Lua integer (integer arithmetic would wrap at 64 bits instead of rounding)
  float                   -> a Lua float rounded to single precision after every float-typed operation (R.f32, a
                             string.pack('f') round trip: C's own (float) cast)
  double -> int           -> R.D2I / R.D2L (x86-64 cvttsd2si: NaN or out of range gives INT_MIN)
  char* / char[]          -> CPtr {b = byte table, o = offset}; p[i] -> p.b[p.o + i]; NULL -> nil
  T* (one object)         -> the table itself; T* / T[] (array) -> a 0-based table
  scalar pointer, ref     -> a PAIR of values (table, key), passed and returned as two values: &Node[j].depth is
                             (Node[j], 'depth'), &a[i] is (a, i), &G is (G, 'G'), a parameter p is (p, p__k), *p is
                             p[p__k]. A local whose address is taken lives in a one-element table x = {v} -> (x, 1)
  globals                 -> fields of the table G; functions -> fields of F (one chunk per C file); records -> Lua
                             tables built by T.<name>(); string literals -> CPtr objects S[n]. A function reads
                             G.Link once, into a local G_Link at its start, when Link is an array, pointer or
                             record that no function it can reach (by the call graph, every function whose address
                             is taken counting as called through any pointer) assigns, and whose address is never
                             taken (analyze_globals): G_Link[i] costs one table index less than G.Link[i]
  C constants             -> chunk-level `local NAME <const> = value`, which Lua 5.4 compiles as constants (no
                             register, no upvalue); K.<name> when a chunk needs too many
  switch                  -> local __sw; gotos to one label per case group, so C's fall-through is kept: an
                             if-chain, or for six or more constant cases a binary search on the case values (C's
                             jump table; a chain would test them one by one); break -> goto past the switch; every
                             loop body is a do ... end block followed by a ::continue:: label, so `continue` is a goto
  a = b used as a value   -> hoisted into a statement before the statement that uses it (26 places in EPA, all an
                             if condition, a return or a call argument; no ++ or -- is used as a value)
  c ? a : b               -> (c and a or b) when a can never be nil or false (numbers), else hoisted into an if
  math                    -> Lua's math library calls glibc (lupa's Lua binds glibc's old symbol versions, so the
                             runtime corrects log of a negative number); pow(x, c) for a constant c other than 2 is
                             x ^ c, any other pow is R.pow; glibc's pow when y == 2 (Lua's ^ computes a * a then)
                             and atan (Lua has only atan2) are glibc's GIMPLE translated by gim2x.py

Every chunk ends its preamble with `local _ENV = R.strict`: a name the translator failed to declare is an error at
run time, not a silent Lua global. Written by Claude (Anthropic) for Robert Dickinson; see lua/README.md.
"""
import os, re, sys, collections, struct, contextlib
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null
import emit_java
from emit_java import JavaEmitter, fclass

LUA_KEYWORDS = set('''and break do else elseif end false for function goto if in local nil not or repeat return then true
until while'''.split())
LUA_RESERVED = LUA_KEYWORDS | set('''F G R S T K self _ENV math string table io os type next print pairs ipairs error
tostring tonumber select setmetatable getmetatable rawget rawset assert pcall load require'''.split()) | {
    'm_abs', 'm_sqrt', 'm_exp', 'm_log10', 'm_sin', 'm_cos', 'm_tan', 'm_asin', 'm_acos', 'm_fmod', 'm_floor'}
MASK = '0xFFFFFFFF'
MATH = {'fabs': 'm_abs', 'sqrt': 'm_sqrt', 'exp': 'm_exp', 'log10': 'R.log10', 'sin': 'm_sin', 'cos': 'm_cos',
        'tan': 'm_tan', 'asin': 'm_asin', 'acos': 'm_acos', 'floor': 'R.floor', 'ceil': 'R.ceil', 'log': 'R.log',
        'atan': 'R.atan'}
PREAMBLE = ('local F, G, R, S, T, K = ...\n'
            'local m_abs, m_sqrt, m_exp, m_sin, m_cos, m_tan, m_asin, m_acos, m_fmod =\n'
            '      math.abs, math.sqrt, math.exp, math.sin, math.cos, math.tan, math.asin, math.acos, math.fmod\n')
INT_RE = re.compile(r'^-?\d+$')
MAX_CHUNK_CONSTS = 150


def lident(n):
    return n + '_' if n in LUA_RESERVED else n


@contextlib.contextmanager
def lua_names():
    old = emit_java.jident
    emit_java.jident = lident
    try:
        yield
    finally:
        emit_java.jident = old


def lua_string(b):
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
            out.append('\\%03d' % ch)
    return '"' + ''.join(out) + '"'


def flit(x):
    """a double as a Lua float literal (always with a point or an exponent)"""
    if x != x:
        return 'R.NAN'
    if x == float('inf'):
        return 'R.INF'
    if x == float('-inf'):
        return '(-R.INF)'
    s = repr(x)
    if 'e' not in s and '.' not in s:
        s += '.0'
    if s.startswith('-'):
        s = '(%s)' % s
    return s


class LuaEmitter(JavaEmitter):
    def __init__(self, F):
        with lua_names():
            super().__init__(F)
        self.boxed_globals = set()            # globals live in G: &G is (G, 'name'), no box needed
        self.jumps = []
        self.nlabel = 0
        self.consts_used = collections.OrderedDict()
        self.gcache_ok = {}                   # function key -> the global keys it may read into locals
        self.gcache_allowed, self.gcache_used = set(), collections.OrderedDict()
        self.loopdepth = 0

    # ================================================================== naming
    def global_ref(self, d):
        k = self.global_key(d)
        if k is not None:
            if k in self.gcache_allowed:            # a use inside a loop counts as two
                self.gcache_used[k] = self.gcache_used.get(k, 0) + (2 if self.loopdepth else 1)
                return 'G_' + self.gname[k]
            return 'G.' + self.gname[k]
        if d.spelling in ('stdout', 'stderr'):
            return 'R.stdout'
        return lident(d.spelling)

    def static_local_name(self, d):
        return lident('%s_%s' % (d.semantic_parent.spelling, d.spelling))

    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = len(self.lits)
        return 'S[%d]' % self.lits[b]

    def const(self, n, v):
        """an enum or macro constant: a chunk-level local of the current file"""
        self.consts_used.setdefault(self.cur_file, collections.OrderedDict())[n] = v
        return n

    def macro_name(self, n):
        for b, m in self.F.macros.items():
            if n in m and m[n][0] in ('int', 'float') and n in self.macro_global:
                kind, s = m[n]
                if kind == 'int':
                    v = re.sub(r'[uUlL]+$', '', s)
                    if len(v) > 1 and v.startswith('0'):
                        v = str(int(v, 8))
                    return self.const(lident(n), v)
                return self.const(lident(n), flit(float(s.rstrip('fF'))))
        return None

    def def_key(self, d):
        keys = self.F.func_by_decl.get(d.spelling) or []
        cand = [k for k in keys if k[0] == self.cur_file] or \
               [k for k in keys if self.F.funcs[k].storage_class != front.ci.StorageClass.STATIC]
        return cand[0] if cand else None

    def func_ref(self, d, cur_file):
        k = self.def_key(d)
        if k is None:
            return 'F.' + lident(d.spelling)
        return 'F.' + self.fname[k]

    def rec(self, t):
        return lident(record_name(t))

    def field(self, n):
        return lident(n)

    # ================================================================== types and values
    def zero(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0', 'l': '0', 'ul': '0', 'd': '0.0', 'f': '0.0'}.get(tg, 'nil')

    def is_ref_decl(self, d):
        cat = ptr_category(d.type)
        return cat in ('scalar', 'ptrptr') and self.P.mode_of(d) == 'ref'

    def paren(self, s):
        if re.fullmatch(r'[\w.\[\]]+', s) or (s.startswith('(') and s.endswith(')') and self._balanced(s[1:-1])):
            return s
        return '(' + s + ')'

    def to_ctype(self, e, t):
        if e.tag == 'b' and ctag(t) in NUMTAGS:
            return Ex('(%s and 1 or 0)' % e.code, ctag(t))
        return e

    def as_bool(self, e):
        if e.tag == 'b':
            return e.code
        if e.tag in ('i', 'u', 'l', 'ul'):
            return '(%s ~= 0)' % e.code
        if e.tag in ('d', 'f'):
            return '(%s ~= 0.0)' % e.code
        if e.tag == 'ref':
            return '(%s ~= nil)' % e.code.split(',')[0].strip()
        return '(%s ~= nil)' % e.code

    def conv(self, e, src_t, dst_t):
        s, d = ctag(src_t), ctag(dst_t)
        if e.tag == 'b' and d in NUMTAGS:
            e = Ex('(%s and 1 or 0)' % e.code, 'i'); s = 'i'
        if s == d or d in ('v', '?'):
            return Ex(e.code, d if d != '?' else e.tag)
        if d == 'rec':
            return e
        if d == 'i':
            if s in ('d', 'f'):
                return Ex('R.D2I(%s)' % e.code, 'i')
            if s in ('l', 'u', 'ul'):
                return Ex('R.i32(%s)' % e.code, 'i')
            return Ex(e.code, 'i')
        if d in ('l', 'ul'):
            if s in ('d', 'f'):
                return Ex('R.D2L(%s)' % e.code, d)
            return Ex(e.code, d)
        if d == 'u':
            if s in ('d', 'f'):
                return Ex('(R.D2L(%s) & %s)' % (e.code, MASK), 'u')
            if INT_RE.match(e.code) and int(e.code) >= 0:
                return Ex(e.code, 'u')
            return Ex('(%s & %s)' % (self.paren(e.code), MASK), 'u')
        if d == 'd':
            if s in ('i', 'u', 'l', 'ul'):
                return Ex(self.tofloat(e.code), 'd')
            return Ex(e.code, 'd')
        if d == 'f':
            if s in ('i', 'u', 'l', 'ul'):
                return Ex('R.f32(%s)' % self.tofloat(e.code), 'f')
            return Ex('R.f32(%s)' % e.code, 'f')
        if d in ('c', 'o'):
            if is_null(e.code) or e.code in ('nil', 'null') or e.tag == 'n' or (e.tag in ('i', 'l') and e.code == '0'):
                return Ex('nil', d)
            return Ex(e.code, d)
        return e

    def tofloat(self, code):
        """C's conversion of an integer to double"""
        if INT_RE.match(code):
            return code + '.0' if not code.startswith('-') else '(%s.0)' % code
        return '(%s * 1.0)' % code

    # ================================================================== leaves
    def x_INTEGER_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'\d+[uUlL]*', toks[0]):
            s = re.sub(r'[uUlL]+$', '', toks[0])
            if len(s) > 1 and s.startswith('0'):
                s = str(int(s, 8))
            return Ex(s, tg)
        if len(toks) == 1:
            mn = self.macro_name(toks[0])
            if mn:
                return Ex(mn, tg)
        v = evaluate(c)
        x = v[1] if v else 0
        if tg in ('u', 'ul') and x < 0:
            x &= 0xFFFFFFFFFFFFFFFF if tg == 'ul' else 0xFFFFFFFF
        if x > 9223372036854775807:
            x -= 1 << 64
        if x == -(1 << 63):
            return Ex('R.LMIN', tg)
        return Ex(str(x) if x >= 0 else '(%d)' % x, tg)

    def x_FLOATING_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and tg != 'f':
            mn = self.macro_name(toks[0])
            if mn:
                return Ex(mn, tg)
        v = evaluate(c)
        x = v[1] if v else 0.0
        if tg == 'f':
            x = struct.unpack('<f', struct.pack('<f', x))[0]
        return Ex(flit(x), tg)

    def x_CHARACTER_LITERAL(self, c):
        v = evaluate(c)
        return Ex(str(v[1] if v else 0), 'i')

    def x_STRING_LITERAL(self, c):
        return Ex(self.lit(self.string_bytes(c)), 'c')

    def x_CXX_UNARY_EXPR(self, c):
        v = evaluate(c)
        return Ex(str(v[1]) if v else '8', 'ul')

    def x_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        if e.tag == 'ref':
            return e
        return Ex('(%s)' % e.code, e.tag)

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return Ex(lident(c.spelling), '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return Ex(str(d.enum_value) if d.enum_value >= 0 else '(%d)' % d.enum_value, 'i')
            return Ex(self.const(lident(d.spelling), str(d.enum_value) if d.enum_value >= 0 else '(%d)' % d.enum_value), 'i')
        if d.kind == K.FUNCTION_DECL:
            k = self.def_key(d)
            if k is None:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex(lident(d.spelling), 'o')
            return Ex('F.' + self.fname[k], 'o')
        local = d.kind == K.PARM_DECL or (d.kind == K.VAR_DECL and d.semantic_parent is not None
                                           and d.semantic_parent.kind == K.FUNCTION_DECL
                                           and d.storage_class != front.ci.StorageClass.STATIC)
        if local:
            nm = self.local_name(d)
            if decl_key(d) in self.boxed_locals:
                return Ex(nm + '[1]', ctag(d.type))
            if self.is_ref_decl(d):
                return Ex('%s, %s__k' % (nm, nm), 'ref')
            return Ex(nm, ctag(d.type))
        if d.kind == K.VAR_DECL:
            if d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL:
                return Ex('G.' + self.static_local_name(d), ctag(d.type))
            if self.is_ref_decl(d):
                self.problem(c, 'global pointer in ref mode %s' % d.spelling)
            return Ex(self.global_ref(d), ctag(d.type))
        return Ex(lident(c.spelling), ctag(c.type))

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                return Ex(self.zero(c.type), ctag(c.type))
            return self.ex(ch[0])
        e = self.ex(ch[0])
        if e.tag == 'ref':
            return e
        if canon(c.type).kind == T.POINTER and e.tag in ('i', 'l') and e.code == '0':
            return Ex('nil', ctag(c.type))
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
        if e.tag == 'ref':
            return e
        if (e.tag in ('i', 'l') and e.code == '0' and canon(c.type).kind == T.POINTER) or e.code == 'nil':
            return Ex('nil', ctag(c.type))
        if ctag(c.type) in ('o', 'c') and ctag(inner.type) in ('o', 'c'):
            return Ex(e.code, ctag(c.type))
        e = self.to_ctype(e, inner.type)
        r = self.conv(e, inner.type, c.type)
        k = canon(c.type).kind
        if k in (T.UCHAR, T.CHAR_U):
            return Ex('(%s & 255)' % self.paren(r.code), 'i')
        if k in (T.CHAR_S, T.SCHAR) and canon(inner.type).kind not in (T.CHAR_S, T.SCHAR):
            return Ex('R.i8(%s)' % r.code, 'i')
        if k == T.SHORT:
            return Ex('R.i16(%s)' % r.code, 'i')
        if k == T.USHORT:
            return Ex('(%s & 65535)' % self.paren(r.code), 'i')
        return r

    # ================================================================== lvalues
    def lv_kind(self, l):
        """('char', cptr, index) | ('deref', t, k) | ('plain', code)"""
        sl = strip(l)
        if sl.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ix = kids(sl)
            if ptr_category(base.type) == 'char':
                return ('char', self.ex(base).code, self.val(ix).code)
        if sl.kind == K.UNARY_OPERATOR and unop(sl) == '*':
            a = kids(sl)[0]
            sa = strip(a)
            if ptr_category(a.type) == 'char':
                if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                    x, y = kids(sa)
                    if ptr_category(x.type) == 'char':
                        i = self.val(y).code
                        return ('char', self.ex(x).code, i if binop(sa) == '+' else '(-%s)' % self.paren(i))
                return ('char', self.ex(a).code, '0')
            e = self.ex(a)
            if e.tag == 'ref':
                t, k = [x.strip() for x in e.code.split(',', 1)]
                return ('deref', t, k)
            if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                x, y = kids(sa)
                i = self.val(y).code
                return ('plain', '%s[%s]' % (self.paren(self.ex(x).code), i if binop(sa) == '+' else '-' + self.paren(i)))
            return ('plain', '%s[0]' % self.paren(e.code))
        e = self.ex(l)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        return ('plain', code)

    def read_lv(self, l):
        k = self.lv_kind(l)
        if k[0] == 'char':
            return self.cget(k[1], k[2])
        if k[0] == 'deref':
            return '%s[%s]' % (k[1], k[2])
        return k[1]

    def cget(self, p, i):
        p = self.paren(p)
        if not re.fullmatch(r'[\w.\[\]]+', p):
            return 'R.cget(%s, %s)' % (p, i)
        return '%s.b[%s.o + %s]' % (p, p, i) if i != '0' else '%s.b[%s.o]' % (p, p)

    def assign_stmt(self, l, rhs):
        k = self.lv_kind(l)
        if k[0] == 'char':
            return 'R.cset(%s, %s, %s)' % (k[1], k[2], rhs)
        if k[0] == 'deref':
            return '%s[%s] = %s' % (k[1], k[2], rhs)
        return '%s = %s' % (k[1], rhs)

    def hoist(self, l, rhs, tg):
        """an assignment used as a value: the statement goes before the current statement, the value is a read"""
        self.pre.append(self.assign_stmt(l, rhs))
        return Ex(self.read_lv(l), tg)

    def ref_of(self, a):
        """the (table, key) pair for lvalue a"""
        sa = strip(a)
        if sa.kind == K.DECL_REF_EXPR:
            d = sa.referenced
            if d is not None and decl_key(d) in self.boxed_locals:
                return '%s, 1' % self.local_name(d)
            if d is not None and d.kind == K.VAR_DECL and (d.semantic_parent is None or d.semantic_parent.kind != K.FUNCTION_DECL):
                k = self.global_key(d)
                if k is None:
                    self.problem(a, 'reference to an unknown global %s' % sa.spelling)
                    return 'nil, nil'
                if k in self.gcache_allowed:
                    self.problem(a, 'reference to a global read into a local %s' % sa.spelling)
                return 'G, "%s"' % self.gname[k]
            if d is not None and d.kind == K.VAR_DECL and d.storage_class == front.ci.StorageClass.STATIC:
                return 'G, "%s"' % self.static_local_name(d)
            self.problem(a, 'reference to an unboxed local %s' % sa.spelling)
            return 'nil, nil'
        k = self.lv_kind(a)
        if k[0] == 'deref':
            return '%s, %s' % (k[1], k[2])
        if k[0] == 'char':
            self.problem(a, 'reference to a char element')
            return 'nil, nil'
        lv = k[1]
        if sa.kind == K.MEMBER_REF_EXPR:
            obj, attr = lv.rsplit('.', 1)
            return '%s, "%s"' % (obj, attr)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ix = kids(sa)
            return '%s, %s' % (self.paren(self.ex(base).code), self.val(ix).code)
        m = re.fullmatch(r'(.*)\[([^\[\]]+)\]', lv)
        if m:
            return '%s, %s' % (m.group(1), m.group(2))
        self.problem(a, 'reference to %s' % lv)
        return 'nil, nil'

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
            self.problem(c, '%s used as a value' % op)
            return Ex(self.read_lv(a), ctag(a.type))
        e = self.val(a)
        if op == '-':
            if e.tag == 'u':
                return Ex('((-%s) & %s)' % (self.paren(e.code), MASK), 'u')
            if e.tag == 'f':
                return Ex('(-%s)' % self.paren(e.code), 'f')
            return Ex('(-%s)' % self.paren(e.code), e.tag)
        if op == '+':
            return e
        if op == '~':
            if e.tag == 'u':
                return Ex('((~%s) & %s)' % (self.paren(e.code), MASK), 'u')
            return Ex('(~%s)' % self.paren(e.code), e.tag)
        self.problem(c, 'unary ' + op)
        return e

    def deref(self, a):
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                x, y = kids(sa)
                if ptr_category(x.type) == 'char':
                    i = self.val(y).code
                    return Ex(self.cget(self.ex(x).code, i if binop(sa) == '+' else '(-%s)' % self.paren(i)), 'i')
            return Ex(self.cget(self.ex(a).code, '0'), 'i')
        e = self.ex(a)
        if cat == 'record':
            return Ex(e.code, 'rec')
        pt = ctag(canon(a.type).get_pointee())
        if e.tag == 'ref':
            t, k = [x.strip() for x in e.code.split(',', 1)]
            return Ex('%s[%s]' % (t, k), pt)
        if sa.kind == K.BINARY_OPERATOR:
            l, r = kids(sa)
            return Ex('%s[%s]' % (self.paren(self.ex(l).code), self.val(r).code), pt)
        return Ex('%s[0]' % self.paren(e.code), pt)

    def addr_of(self, a, c):
        sa = strip(a)
        if canon(sa.type).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return self.ex(sa)
        if ctag(sa.type) == 'rec':
            return Ex(self.ex(sa).code, 'o')
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ix = kids(sa)
            if ptr_category(base.type) == 'char':
                b = self.ex(base).code
                i = self.val(ix).code
                return Ex(b if i == '0' else 'R.padd(%s, %s)' % (b, i), 'c')
            if ctag(sa.type) == 'rec':
                return Ex(self.ex(sa).code, 'o')
            if self.val(ix).code == '0':
                return Ex(self.ex(base).code, 'o')
        if canon(sa.type).kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            return Ex(self.ex(sa).code, ctag(sa.type))
        return Ex(self.ref_of(sa), 'ref')

    def arith(self, op, a, b, tg):
        if tg in ('i', 'l', 'ul', 'u'):
            if op == '/':
                return 'R.idiv(%s, %s)' % (a, b)
            if op == '%':
                return 'm_fmod(%s, %s)' % (a, b)
            if op == '^':
                op = '~'
            if op == '>>' and tg != 'u':
                return '(%s // (1 << %s))' % (a, b)
            if tg == 'u' and op in ('+', '-', '*', '<<'):
                return '((%s %s %s) & %s)' % (a, op, b, MASK)
            if tg == 'i' and op == '<<':
                return 'R.i32(%s << %s)' % (a, b)
            return '(%s %s %s)' % (a, op, b)
        if tg == 'f' and op in ('+', '-', '*', '/'):
            return 'R.f32(%s %s %s)' % (a, op, b)
        if tg in ('d', 'f') and op == '%':
            return 'm_fmod(%s, %s)' % (a, b)
        return '(%s %s %s)' % (a, op, b)

    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            if ctag(l.type) == 'rec':
                return self.hoist(l, '%s(%s)' % (self.copyfn(l.type), self.ex(r).code), 'rec')
            e = self.conv(self.val(r), r.type, l.type)
            return self.hoist(l, e.code, ctag(l.type))
        if op in ('&&', '||'):
            lc = self.cond(l)
            n = len(self.pre)
            rc = self.cond(r)
            if len(self.pre) != n:
                self.problem(c, 'a hoisted assignment inside the right operand of %s' % op)
            return Ex('(%s %s %s)' % (self.paren(lc), 'and' if op == '&&' else 'or', self.paren(rc)), 'b')
        if op == ',':
            self.pre.append(self.expr_stmt_code(l))
            return self.val(r)
        lt, rt = canon(l.type), canon(r.type)
        le, re_ = self.val(l), self.val(r)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            lop = '~=' if op == '!=' else op
            if le.tag in ('c', 'o', 'n', 'ref') or re_.tag in ('c', 'o', 'n', 'ref'):
                lcode = le.code.split(',')[0].strip() if le.tag == 'ref' else le.code
                rcode = re_.code.split(',')[0].strip() if re_.tag == 'ref' else re_.code
                nl = lcode in ('nil', '0') or is_null(lcode)
                nr = rcode in ('nil', '0') or is_null(rcode)
                if op in ('==', '!=') and (nl or nr):
                    x = lcode if not nl else rcode
                    return Ex('(%s %s nil)' % (x, lop), 'b')
                if ptr_category(l.type) == 'char' or ptr_category(r.type) == 'char':
                    if op in ('==', '!='):
                        return Ex('%sR.peq(%s, %s)' % ('' if op == '==' else 'not ', le.code, re_.code), 'b')
                    return Ex('(%s.o %s %s.o)' % (self.paren(le.code), lop, self.paren(re_.code)), 'b')
                return Ex('(%s %s %s)' % (lcode, lop, rcode), 'b')
            return Ex('(%s %s %s)' % (le.code, lop, re_.code), 'b')
        tg = ctag(c.type)
        if tg == 'c':
            if op == '+':
                if ptr_category(l.type) == 'char':
                    return Ex('R.padd(%s, %s)' % (le.code, re_.code), 'c')
                return Ex('R.padd(%s, %s)' % (re_.code, le.code), 'c')
            return Ex('R.padd(%s, -%s)' % (le.code, self.paren(re_.code)), 'c')
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            return Ex('(%s.o - %s.o)' % (self.paren(le.code), self.paren(re_.code)), 'l')
        return Ex(self.arith(op, le.code, re_.code, tg), tg)

    def compound_parts(self, c):
        """(lvalue node, new value code, tag) for lhs op= rhs, with C's conversions"""
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        re_ = self.val(r)
        if lt == 'c':
            cur = self.read_lv(l)
            return 'R.padd(%s, %s%s)' % (cur, '' if op == '+' else '-', self.paren(re_.code)), lt
        common = 'd' if 'd' in (lt, rt) else ('f' if 'f' in (lt, rt) else ('ul' if 'ul' in (lt, rt) else
                  ('l' if 'l' in (lt, rt) else ('u' if 'u' in (lt, rt) else 'i'))))
        cur = self.read_lv(l)
        if common == 'd' and lt in ('i', 'u', 'l', 'ul'):
            cur = self.tofloat(cur)
        rcode = re_.code
        if common in ('d', 'f') and rt in ('i', 'u', 'l', 'ul'):
            rcode = self.tofloat(rcode)
        v = self.arith(op, cur, self.paren(rcode), common)
        if lt in ('i', 'l', 'u', 'ul') and common in ('d', 'f'):
            v = {'i': 'R.D2I(%s)', 'l': 'R.D2L(%s)', 'u': '(R.D2L(%s) & 0xFFFFFFFF)', 'ul': 'R.D2L(%s)'}[lt] % v
        elif lt == 'f' and common == 'd':
            v = 'R.f32(%s)' % v
        elif lt == 'i' and common in ('l', 'u', 'ul'):
            v = 'R.i32(%s)' % v
        elif lt == 'u' and common != 'u':
            v = '(%s & %s)' % (v, MASK)
        return v, lt

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        v, tg = self.compound_parts(c)
        return self.hoist(kids(c)[0], v, tg)

    def compound_code(self, c):
        v, tg = self.compound_parts(c)
        return self.assign_stmt(kids(c)[0], v)

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        tg = ctag(c.type)
        cond = self.cond(cc)
        n = len(self.pre)
        ea = self.conv(self.val(a), a.type, c.type)
        eb = self.conv(self.val(b), b.type, c.type)
        if len(self.pre) != n:
            self.problem(c, 'a hoisted assignment inside a ?: branch')
        if ea.tag == 'ref' or eb.tag == 'ref':
            self.problem(c, '?: on references')
        if tg in NUMTAGS or ea.code.startswith('S['):
            return Ex('(%s and %s or %s)' % (cond, ea.code, eb.code), tg)
        if ea.code == 'nil':
            return Ex('(not %s and %s or nil)' % (self.paren(cond), eb.code), tg)
        if eb.code == 'nil':
            return Ex('(%s and %s or nil)' % (cond, ea.code), tg)
        self.tmp += 1
        t = '__t%d' % self.tmp
        self.pre.append('local %s; if %s then %s = %s else %s = %s end' % (t, cond, t, ea.code, t, eb.code))
        return Ex(t, tg)

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, ix = kids(c)
        if ptr_category(base.type) == 'char':
            return Ex(self.cget(self.ex(base).code, self.val(ix).code), 'i')
        b = self.ex(base)
        return Ex('%s[%s]' % (self.paren(b.code), self.val(ix).code), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        b = self.ex(base)
        return Ex('%s.%s' % (self.paren(b.code), self.field(c.referenced.spelling)), ctag(c.type))

    # ================================================================== initialisers and allocation
    def copyfn(self, t):
        return 'T.copy_' + self.rec(canon(t))

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
                self.defects.append('%s:%d string table without NULL sentinel' % (os.path.basename(c.location.file.name), c.location.line))
                n += 1
            if ctag(t) == 'c':
                return Ex('R.bufOf(%d, {%s})' % (n, ', '.join(self.val(it).code for it in items)), 'c')
            vals = []
            for it in items:
                if strip(it).kind == K.INIT_LIST_EXPR:
                    vals.append(self.init_list(strip(it), et).code)
                elif ctag(et) == 'c' and strip(it).kind == K.STRING_LITERAL and canon(et).kind == T.CONSTANTARRAY:
                    vals.append('R.bufFrom(%s, %d)' % (self.lit(self.string_bytes(strip(it))), canon(et).element_count))
                else:
                    vals.append(self.conv(self.val(it), it.type, et).code)
            while len(vals) < n:
                if ctag(et) == 'rec':
                    vals.append('T.%s()' % self.rec(et))
                elif et.kind == T.CONSTANTARRAY:
                    vals.append(self.new_array(et))
                else:
                    vals.append(self.zero(et))
            if not vals:
                return Ex('{}', 'o')
            return Ex('{[0] = %s}' % ', '.join(vals), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                if strip(it).kind == K.INIT_LIST_EXPR:
                    parts.append('__r.%s = %s' % (self.field(f.spelling), self.init_list(strip(it), f.type).code))
                else:
                    parts.append('__r.%s = %s' % (self.field(f.spelling), self.conv(self.val(it), it.type, f.type).code))
            return Ex('(function() local __r = T.%s(); %s; return __r end)()' % (self.rec(t), '; '.join(parts)), 'rec')
        if len(items) == 1:
            return self.val(items[0])
        self.problem(c, 'init list for %s' % t.spelling)
        return Ex('nil', '?')

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return 'R.recs(%d, T.%s)' % (n, self.rec(et))
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return 'R.bufs(%d, %d)' % (n, et.element_count)
        if et.kind == T.CONSTANTARRAY:
            inner = canon(et.element_type)
            if ctag(inner) in NUMTAGS:
                return 'R.grid(%d, %d, %s)' % (n, et.element_count, self.zero(inner))
            self.problems.append('array of arrays of %s' % inner.spelling)
            return 'nil'
        if et.kind == T.POINTER:
            return '{}'
        return 'R.fill(%d, %s)' % (n, self.zero(et))

    def alloc(self, call, t):
        args = list(call.get_arguments())
        t = canon(t)
        if t.kind != T.POINTER:
            return Ex('nil', 'o')
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
                return Ex('R.realloc_c(%s, %s)' % (old, n), 'c')
            if et.kind == T.RECORD:
                return Ex('R.realloc(%s, %s, T.%s)' % (old, n, self.rec(et)), 'o')
            return Ex('R.realloc(%s, %s, %s)' % (old, n, self.zero(et) if ctag(et) in NUMTAGS else 'nil'), 'o')
        if ctag(t) == 'c':
            return Ex('R.buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('T.%s()' % self.rec(et), 'o')
            return Ex('R.recs(%s, T.%s)' % (n, self.rec(et)), 'o')
        if et.kind == T.POINTER:
            return Ex('{}', 'o')
        return Ex('R.fill(%s, %s)' % (n, self.zero(et)), 'o')

    def count_expr(self, a, b, et, mul):
        size = self.sizeof_type(et)
        def is_sizeof(x):
            return strip(x).kind == K.CXX_UNARY_EXPR
        if mul:
            if is_sizeof(b):
                return self.val(a).code
            if is_sizeof(a):
                return self.val(b).code
            return 'R.idiv(%s * %s, %d)' % (self.val(a).code, self.val(b).code, size)
        sa = strip(a)
        if is_sizeof(sa):
            return '1'
        if sa.kind == K.BINARY_OPERATOR and binop(sa) == '*':
            l, r = kids(sa)
            if is_sizeof(l):
                return self.val(r).code
            if is_sizeof(r):
                return self.val(l).code
        return 'R.idiv(%s, %d)' % (self.val(a).code, size)

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
            n = self.func_ref(d, self.cur_file)
            params = list(fdef.get_arguments())
            codes = [self.arg(a, p) for a, p in zip(args, params)]
            return Ex('%s(%s)' % (n, ', '.join(codes)), ctag(c.type))
        fe = self.ex(callee)
        ft = canon(canon(strip(callee).type).get_pointee()) if canon(strip(callee).type).kind == T.POINTER else None
        argcodes = []
        for i, a in enumerate(args):
            sa = strip(a)
            mode = self.bound_param_mode(ft, i) if ft is not None else None
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and ctag(strip(kids(sa)[0]).type) in NUMTAGS:
                if mode == 'array':
                    argcodes.append(self.one_elem(kids(sa)[0], a))
                else:
                    argcodes.append(self.ref_of(kids(sa)[0]))
            else:
                e = self.val(a)
                argcodes.append(e.code)
        return Ex('%s(%s)' % (self.paren(fe.code), ', '.join(argcodes)), ctag(c.type))

    def one_elem(self, o, a):
        """&x passed where the callee indexes an array: a one-element array, copied back after the statement"""
        self.tmp += 1
        t = '__a%d' % self.tmp
        self.pre.append('local %s = {[0] = %s}' % (t, self.read_lv(o)))
        self.post.append(self.assign_stmt(o, '%s[0]' % t))
        return t

    def arg(self, a, p):
        pmode = self.P.mode_of(p)
        cat = ptr_category(p.type)
        sa = strip(a)
        if cat in ('scalar', 'ptrptr') and pmode == 'ref':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return self.ref_of(kids(sa)[0])
            e = self.ex(sa)
            if e.tag == 'ref':
                return e.code
            if is_null(e.code) or e.code == 'nil' or (e.tag in ('i', 'l') and e.code == '0'):
                return 'nil, nil'
            return '%s, 0' % e.code                 # an array passed where the callee dereferences: its element 0
        if cat == 'scalar' and pmode == 'array':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = strip(kids(sa)[0])
                if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                    base, ix = kids(o)
                    if self.val(ix).code != '0':
                        self.problem(a, 'array offset passed to array param %s' % p.spelling)
                    return self.ex(base).code
                return self.one_elem(kids(sa)[0], a)
        if cat == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and front.is_char(strip(kids(sa)[0]).type) \
                and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR:
            o = kids(sa)[0]
            self.tmp += 1
            t = '__c%d' % self.tmp
            self.pre.append('local %s = R.buf(2); R.cset(%s, 0, %s)' % (t, t, self.read_lv(o)))
            self.post.append(self.assign_stmt(o, '%s.b[0]' % t))
            return t
        e = self.conv(self.val(a), a.type, p.type)
        if cat in ('char', 'record', 'void', 'func', 'file') and (is_null(e.code) or e.code == 'nil'):
            return 'nil'
        if e.tag == 'ref':
            self.problem(a, 'a reference passed to a non-reference parameter')
        return e.code

    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name in MATH:
            return Ex('%s(%s)' % (MATH[name], A(0)), 'd')
        if name == 'pow':
            ev = evaluate(args[1])
            if ev is not None and ev[0] in ('int', 'float') and float(ev[1]) != 2.0:
                # Lua's x ^ y is C's pow(x, y) except when y == 2 (rt.lua R.pow)
                return Ex('(%s ^ %s)' % (self.paren(A(0)), self.paren(A(1))), 'd')
            return Ex('R.pow(%s, %s)' % (A(0), A(1)), 'd')
        if name in ('fprintf', 'snprintf', 'sscanf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}[name]
            head = [A(i) for i in range(fixed)]
            rest = [self.vararg(a, name == 'sscanf') for a in args[fixed:]]
            return Ex('R.%s(%s)' % (name, ', '.join(head + rest)), 'i')
        if name == 'free':
            return Ex('nil', 'v')
        if name in ('calloc', 'malloc', 'realloc'):
            return self.alloc(c, c.type)
        if name in ('fwrite', 'fread'):
            return self.freadwrite(c, name, args)
        if name == 'memset':
            dst = strip(args[0])
            if dst.kind == K.UNARY_OPERATOR and unop(dst) == '&' and ctag(strip(kids(dst)[0]).type) == 'rec':
                o = strip(kids(dst)[0])
                return Ex(self.assign_stmt(o, 'T.%s()' % self.rec(o.type)), 'v')
            return Ex('R.memset(%s, %s, %s)' % (A(0), A(1), A(2)), 'v')
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return Ex('R.strtod(%s, %s)' % (A(0), self.ref_of(kids(ep)[0])), 'd')
            return Ex('R.strtod(%s, nil, nil)' % A(0), 'd')
        if name == 'time':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                self.pre.append(self.assign_stmt(kids(a0)[0], 'R.time()'))
                return Ex(self.read_lv(kids(a0)[0]), 'l')
            return Ex('R.time()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('R.ctime(%s)' % (self.ex(kids(a0)[0]).code if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('((%s - %s) * 1.0)' % (A(0), A(1)), 'd')
        if name == 'fseeko':
            name = 'fseek'
        rt = {'strlen': 'ul', 'atoi': 'i', 'strcmp': 'i', 'feof': 'i', 'fclose': 'i', 'atof': 'd', 'ftell': 'l',
              'strcspn': 'ul', 'toupper': 'i', 'fseek': 'i', 'remove': 'i', 'fflush': 'i', 'rewind': 'v'}.get(name, tg)
        return Ex('R.%s(%s)' % (name, ', '.join(A(i) for i in range(len(args)))), rt)

    def vararg(self, a, scanf):
        sa = strip(a)
        if scanf:
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = kids(sa)[0]
                if ctag(strip(o).type) == 'f':
                    return 'R.FLOAT, ' + self.ref_of(o)
                return self.ref_of(o)
            e = self.ex(sa)
            if e.tag == 'ref':
                if ctag(canon(sa.type).get_pointee()) == 'f':
                    return 'R.FLOAT, ' + e.code
                return e.code
            return self.val(a).code
        return self.val(a).code

    def freadwrite(self, c, name, args):
        buf, size, cnt, f = args
        sb = strip(buf)
        fc = self.val(f).code
        sz = evaluate(strip(size))
        sz = sz[1] if sz and sz[0] == 'int' else None

        def kindof(t):
            k = canon(t).kind
            return {T.DOUBLE: 'd', T.FLOAT: 'f', T.INT: 'i', T.ENUM: 'i', T.UINT: 'I', T.LONG: 'l', T.ULONG: 'l',
                    T.LONGLONG: 'l', T.ULONGLONG: 'l', T.CHAR_S: 'c', T.SCHAR: 'c', T.UCHAR: 'c', T.CHAR_U: 'c'}.get(k, '?')
        if sb.kind == K.UNARY_OPERATOR and unop(sb) == '&':
            o = strip(kids(sb)[0])
            if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                base, ix = kids(o)
                return Ex('R.%s_arr("%s", %s, %s, %s, %s)' % (name, kindof(o.type), self.ex(base).code, self.val(ix).code, self.val(cnt).code, fc), 'ul')
            k = kindof(o.type)
            n = sz or self.sizeof_type(o.type)
            if name == 'fwrite':
                return Ex('R.fwrite1("%s", %d, %s, %s)' % (k, n, self.read_lv(o), fc), 'ul')
            return Ex('R.fread1("%s", %d, %s, %s)' % (k, n, self.ref_of(o), fc), 'ul')
        e = self.ex(sb)
        if e.tag == 'ref':
            et = canon(canon(sb.type).get_pointee())
            t, kk = [x.strip() for x in e.code.split(',', 1)]
            if name == 'fwrite':
                return Ex('R.fwrite1("%s", %d, %s[%s], %s)' % (kindof(et), sz or self.sizeof_type(et), t, kk, fc), 'ul')
            return Ex('R.fread1("%s", %d, %s, %s)' % (kindof(et), sz or self.sizeof_type(et), e.code, fc), 'ul')
        bt = canon(sb.type)
        et = canon(bt.get_pointee()) if bt.kind == T.POINTER else canon(bt.element_type)
        return Ex('R.%s_arr("%s", %s, 0, %s, %s)' % (name, kindof(et), e.code, self.val(cnt).code, fc), 'ul')

    # ================================================================== statements
    def new_label(self, kind):
        self.nlabel += 1
        return '%s%d' % (kind, self.nlabel)

    def flush(self, lines, ind):
        if not self.pre and not self.post:
            return lines
        p = '  ' * ind
        pre, post = self.pre, self.post
        self.pre, self.post = [], []
        if post and any(re.match(r'^(return|if |while |repeat|until|goto)\b', l.strip()) for l in lines):
            self.problems.append('copy-back after %s' % lines[0].strip())
        return [p + x for x in pre] + lines + [p + x for x in post]

    def body(self, c, ind):
        return self.stmt(c, ind + 1)

    def stmt(self, c, ind):
        if c.kind in (K.WHILE_STMT, K.DO_STMT, K.FOR_STMT):
            self.loopdepth += 1
            try:
                return self._stmt(c, ind)
            finally:
                self.loopdepth -= 1
        return self._stmt(c, ind)

    def _stmt(self, c, ind):
        k = c.kind
        p = '  ' * ind
        if k == K.COMPOUND_STMT:
            out = []
            for ch in kids(c):
                if ch.kind == K.COMPOUND_STMT:
                    # a nested C block keeps its own scope (its locals end with it, as Lua counts them)
                    out += [p + 'do'] + self.stmt(ch, ind + 1) + [p + 'end']
                else:
                    out += self.stmt(ch, ind)
                if not self.completes(ch):
                    break
            return out
        if k == K.DECL_STMT:
            out = []
            for d in kids(c):
                out += self.flush(self.local_decl(d, ind), ind)
            return out
        if k == K.IF_STMT:
            ch = kids(c)
            out = self.flush([p + 'if %s then' % self.cond(ch[0])], ind)
            out += self.block_body(ch[1], ind)
            x = c
            while len(kids(x)) > 2:
                e = kids(x)[2]
                if e.kind == K.IF_STMT:
                    ec = kids(e)
                    cond = self.cond(ec[0])
                    if self.pre or self.post:
                        self.pre, self.post = [], []
                        out.append(p + 'else')
                        out += self.stmt(e, ind + 1)
                        out.append(p + 'end')
                        return out
                    out.append(p + 'elseif %s then' % cond)
                    out += self.block_body(ec[1], ind)
                    x = e
                else:
                    out.append(p + 'else')
                    out += self.block_body(e, ind)
                    break
            out.append(p + 'end')
            return out
        if k == K.WHILE_STMT:
            ch = kids(c)
            cond = self.cond(ch[0])
            if self.pre or self.post:
                self.problems.append('%s: set-up statements in a while condition' % self.where(c))
            return self.loop(p + 'while %s do' % cond, ch[1], [], ind, p + 'end')
        if k == K.DO_STMT:
            ch = kids(c)
            lab = self.new_label('continue')
            self.jumps.append(['loop', lab, False])
            body = self.body(ch[0], ind + 1)
            j = self.jumps.pop()
            cond = self.cond(ch[1])
            if self.pre or self.post:
                self.problems.append('%s: set-up statements in a do-while condition' % self.where(c))
            out = [p + 'repeat', p + '  do'] + body + [p + '  end']
            if j[2]:
                out.append(p + '  ::%s::' % lab)
            return out + [p + 'until not %s' % self.paren(cond)]
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            j = self.jumps[-1]
            if j[0] == 'switch':
                j[2] = True
                return [p + 'goto %s' % j[1]]
            return [p + 'break']
        if k == K.CONTINUE_STMT:
            for j in reversed(self.jumps):
                if j[0] == 'loop':
                    j[2] = True
                    return [p + 'goto %s' % j[1]]
            self.problem(c, 'continue outside a loop')
            return []
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'do return end']
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            if ctag(self.cur_ret) in ('c', 'o') and (is_null(e.code) or e.code == 'nil'):
                e = Ex('nil', 'o')
            if self.post:
                self.tmp += 1
                t = '__r%d' % self.tmp
                return self.flush([p + 'local %s = %s' % (t, e.code)], ind) + [p + 'do return %s end' % t]
            return self.flush([p + 'do return %s end' % e.code], ind)
        if k == K.NULL_STMT:
            return []
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unhandled statement %s' % k.name)
            return []
        code = self.expr_stmt_code(c)
        if code.startswith('('):
            code = ';' + code                       # else Lua reads it as a call on the previous line's value
        return self.flush([p + code] if code else [], ind)

    def where(self, c):
        return '%s:%s' % (os.path.basename(c.location.file.name) if c.location.file else '?', c.location.line)

    def block_body(self, c, ind):
        return self.stmt(c, ind + 1)

    def loop(self, head, body_node, inc_lines, ind, tail):
        """head; do body end; ::continue::; inc; tail"""
        p = '  ' * ind
        lab = self.new_label('continue')
        self.jumps.append(['loop', lab, False])
        body = self.body(body_node, ind + 1)
        j = self.jumps.pop()
        out = [head, p + '  do'] + body + [p + '  end']
        if j[2]:
            out.append(p + '  ::%s::' % lab)
        out += [p + '  ' + x for x in inc_lines]
        out.append(tail)
        return out

    def expr_stmt_code(self, c):
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) == 'v':
            return self.expr_stmt_code(kids(s)[-1])
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            if ctag(l.type) == 'rec':
                return self.assign_stmt(l, '%s(%s)' % (self.copyfn(l.type), self.ex(r).code))
            e = self.conv(self.val(r), r.type, l.type)
            if e.tag == 'ref':
                k = self.lv_kind(l)
                return '%s, %s__k = %s' % (k[1], k[1], e.code)
            return self.assign_stmt(l, e.code)
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            a = self.expr_stmt_code(l)
            b = self.expr_stmt_code(r)
            return '; '.join(x for x in (a, b) if x)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            return self.compound_code(s)
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            d = '+' if '++' in unop(s) else '-'
            tg = ctag(a.type)
            cur = self.read_lv(a)
            if tg == 'c':
                return self.assign_stmt(a, 'R.padd(%s, %s1)' % (cur, '' if d == '+' else '-'))
            if tg == 'u':
                return self.assign_stmt(a, '((%s %s 1) & %s)' % (cur, d, MASK))
            if tg == 'f':
                return self.assign_stmt(a, 'R.f32(%s %s 1.0)' % (cur, d))
            if tg == 'd':
                return self.assign_stmt(a, '%s %s 1.0' % (cur, d))
            return self.assign_stmt(a, '%s %s 1' % (cur, d))
        if s.kind == K.CONDITIONAL_OPERATOR:
            cc, a, b = kids(s)
            return 'if %s then %s else %s end' % (self.cond(cc), self.expr_stmt_code(a), self.expr_stmt_code(b))
        e = self.ex(c)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        if s.kind == K.CALL_EXPR or code.startswith('R.') and '(' in code and s.kind != K.DECL_REF_EXPR:
            if re.match(r'^[\w.\[\]]+\s*\(', code) or re.match(r'^\(.*\)\s*\(', code):
                return code
            if re.match(r'^[\w.\[\]]+ = ', code) or re.match(r'^[\w.\[\]]+\s*, \S+ = ', code):
                return code
            return 'local _ = %s' % code
        if re.match(r'^[\w.\[\]]+ = ', code) or code.startswith('R.cset(') or code == 'nil' or code == '':
            return code if code != 'nil' else ''
        return 'local _ = %s' % code

    def for_parts(self, c):
        ch = kids(c)
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
        init = cond = inc = None
        for x in parts:
            o = x.extent.start.offset
            if len(semis) >= 2 and o < semis[0]:
                init = x
            elif len(semis) >= 2 and o < semis[1]:
                cond = x
            else:
                inc = x
        return init, cond, inc, body

    def for_stmt(self, c, ind):
        p = '  ' * ind
        init, cond, inc, body = self.for_parts(c)
        out = [p + 'do']
        if init is not None:
            if init.kind == K.DECL_STMT:
                for d in kids(init):
                    out += self.flush(self.local_decl(d, ind + 1), ind + 1)
            else:
                code = self.expr_stmt_code(init)
                out += self.flush(['  ' * (ind + 1) + code] if code else [], ind + 1)
        cond_s = self.cond(cond) if cond is not None else 'true'
        if self.pre or self.post:
            self.problems.append('%s: set-up statements in a for condition' % self.where(c))
        inc_lines = []
        if inc is not None:
            code = self.expr_stmt_code(inc)
            if self.pre or self.post:
                inc_lines += self.pre
                self.pre, self.post = [], []
            if code:
                inc_lines.append(code)
        out += self.loop(p + '  while %s do' % cond_s, body, inc_lines, ind + 1, p + '  end')
        out.append(p + 'end')
        return out

    def switch(self, c, ind):
        p = '  ' * ind
        ch = kids(c)
        e = self.val(ch[0])
        code = e.code if e.tag != 'b' else '(%s and 1 or 0)' % e.code
        body = ch[-1]
        items = kids(body) if body.kind == K.COMPOUND_STMT else [body]
        groups, case_exprs = [], []
        for it in items:
            x = it
            labels = []
            while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                xc = kids(x)
                if x.kind == K.CASE_STMT:
                    labels.append(self.val(xc[0]).code)
                    case_exprs.append(xc[0])
                    x = xc[1]
                else:
                    labels.append(None)
                    x = xc[0]
            if labels or not groups:
                groups.append((labels, []))
            if x.kind not in (K.CASE_STMT, K.DEFAULT_STMT):
                groups[-1][1].append(x)
        head = self.flush([], ind)
        self.tmp += 1
        sv = '__sw%d' % self.tmp
        end = self.new_label('swend')
        jump = ['switch', end, False]
        self.jumps.append(jump)
        labs = [self.new_label('case') for _ in groups]
        disp, default = [], None
        cases = []                                  # (value, code, label) for a binary dispatch
        for gi, (labels, _) in enumerate(groups):
            if not labels:
                continue
            if None in labels:
                default = labs[gi]
            vals = [x for x in labels if x is not None]
            if vals:
                disp.append((' or '.join('%s == %s' % (sv, v) for v in vals), labs[gi]))
                cases += [(v, labs[gi]) for v in vals]
        nums = [evaluate(x) for x in case_exprs]
        tree = None
        if len(cases) >= 6 and all(ev is not None and ev[0] == 'int' for ev in nums) and len(nums) == len(cases):
            tree = sorted(((ev[1],) + cs for ev, cs in zip(nums, cases)), key=lambda t: t[0])
        bodies = []
        live = True
        for gi, (labels, stmts) in enumerate(groups):
            if not labels and gi == 0:
                continue           # statements before the first label are unreachable
            lines = []
            for s in stmts:
                lines += self.stmt(s, ind + 2)
                if not self.completes(s):
                    break
            bodies.append((labs[gi], lines, self.seq_completes(stmts)))
        self.jumps.pop()
        out = head + [p + 'do', p + '  local %s = %s' % (sv, code)]

        def bisect(cs, q):                          # cs sorted by value; C's jump table as a binary search
            if len(cs) <= 3:
                return [q + '%s %s == %s then goto %s' % ('if' if i == 0 else 'elseif', sv, v, lab)
                        for i, (_, v, lab) in enumerate(cs)] + [q + 'end']
            m = len(cs) // 2
            return ([q + 'if %s < %s then' % (sv, cs[m][1])] + bisect(cs[:m], q + '  ') + [q + 'else'] +
                    bisect(cs[m:], q + '  ') + [q + 'end'])
        if tree:
            out += bisect(tree, p + '  ')
            out.append(p + '  goto %s' % (default or end))
        elif disp:
            for i, (test, lab) in enumerate(disp):
                out.append(p + '  %s %s then goto %s' % ('if' if i == 0 else 'elseif', test, lab))
            out.append(p + '  else goto %s end' % (default or end))
        elif default:
            out.append(p + '  goto %s' % default)
        else:
            out.append(p + '  goto %s' % end)
        for lab, lines, completes in bodies:
            out.append(p + '  ::%s::' % lab)
            out += [p + '  do'] + lines + [p + '  end']
        out.append(p + '  ::%s::' % end)
        out.append(p + 'end')
        return out

    def seq_completes(self, stmts):
        for s in stmts:
            if not self.completes(s):
                return False
        return True

    def local_decl(self, d, ind):
        p = '  ' * ind
        if d.kind != K.VAR_DECL:
            return []
        if d.storage_class == front.ci.StorageClass.EXTERN:
            return []
        if d.storage_class == front.ci.StorageClass.STATIC:
            self.static_locals.append((d, self.cur_file))
            return []
        name = self.declare_local(d)
        init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        t = canon(d.type)
        boxed = decl_key(d) in self.boxed_locals
        if t.kind == T.CONSTANTARRAY:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return [p + 'local %s = %s' % (name, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return [p + 'local %s = R.bufFrom(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return [p + 'local %s = R.buf(%d)' % (name, t.element_count)]
            return [p + 'local %s = %s' % (name, self.new_array(t))]
        if ctag(t) == 'rec':
            if init:
                return [p + 'local %s = %s(%s)' % (name, self.copyfn(t), self.ex(init[-1]).code)]
            return [p + 'local %s = T.%s()' % (name, self.rec(t))]
        if self.is_ref_decl(d):
            v = self.ex(init[-1]) if init else Ex('nil, nil', 'ref')
            vc = v.code if v.tag == 'ref' else ('nil, nil' if v.code == 'nil' else '%s, 0' % v.code)
            return [p + 'local %s, %s__k = %s' % (name, name, vc)]
        v = self.conv(self.val(init[-1]), init[-1].type, d.type).code if init else self.zero(d.type)
        if boxed:
            return [p + 'local %s = {%s}' % (name, v)]
        return [p + 'local %s = %s' % (name, v)]

    # ================================================================== functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.cur_ret = c.result_type
        self.boxed_locals = set()
        self.tmp = 0
        self.jumps = []
        self.nlabel = 0
        self.pre, self.post = [], []
        self.gcache_allowed = self.gcache_ok.get(key, set())
        self.gcache_used = collections.OrderedDict()
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]

        def scan(x):
            if x.kind == K.UNARY_OPERATOR and unop(x) == '&':
                o = strip(kids(x)[0])
                if o.kind == K.DECL_REF_EXPR and o.referenced is not None and o.referenced.kind in (K.VAR_DECL, K.PARM_DECL):
                    d = o.referenced
                    boxable = ctag(d.type) in NUMTAGS or canon(d.type).kind == T.POINTER
                    if boxable and (d.kind == K.PARM_DECL or (d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL
                                                              and d.storage_class != front.ci.StorageClass.STATIC)):
                        if not self.is_ref_decl(d):
                            self.boxed_locals.add(decl_key(d))
            for y in x.get_children():
                scan(y)
        scan(body)
        ps, pre = [], []
        for prm in params:
            nm = self.declare_local(prm)
            if self.is_ref_decl(prm):
                ps += [nm, nm + '__k']
            else:
                ps.append(nm)
                if decl_key(prm) in self.boxed_locals:
                    pre.append('  %s = {%s}' % (nm, nm))
        self.loopdepth = 0
        lines = self.stmt(body, 1)
        cached = [self.gname[k] for k, n in self.gcache_used.items() if n >= 2]
        once = [self.gname[k] for k, n in self.gcache_used.items() if n < 2]
        if once:                                    # read once: a local would cost more than it saves
            once_re = re.compile(r'\bG_(%s)\b' % '|'.join(re.escape(n) for n in once))
            lines = [once_re.sub(r'G.\1', l) for l in lines]
        self.gcache_allowed, self.gcache_used = set(), collections.OrderedDict()
        for i in range(0, len(cached), 6):
            part = cached[i:i + 6]
            pre.append('  local %s = %s' % (', '.join('G_' + n for n in part), ', '.join('G.' + n for n in part)))
        nloc = len(ps) + len(cached) + sum(len(m.group(1).split(',')) for m in
                                           (re.match(r'\s*local (.*?)( =|$)', l) for l in lines) if m)
        if nloc > 180:
            self.problem(c, '%d locals in %s' % (nloc, self.fname[key]))
        out = ['-- %s:%d' % (b, c.location.line), 'F.%s = function(%s)' % (self.fname[key], ', '.join(ps))]
        out += pre + lines + ['end']
        return out

    def analyze_globals(self):
        """which globals each function may read once into a local: arrays, pointers and records (their binding,
        G.name, changes only when C assigns the variable itself) that the function and everything it can call
        never assign, and whose address C never takes (a (G, 'name') pair could be written through)"""
        calls, assigns = {}, {}
        addr_funcs, indirect, addr_globals = set(), set(), set()

        def target_global(x):
            x = strip(x)
            if x.kind == K.DECL_REF_EXPR and x.referenced is not None and x.referenced.kind == K.VAR_DECL:
                return self.global_key(x.referenced)
            return None

        for key, c in self.F.funcs.items():
            self.cur_file = key[0]
            cs, asg, takes = set(), set(), set()
            stack = [c]
            while stack:
                x = stack.pop()
                k = x.kind
                ch = kids(x)
                if k == K.CALL_EXPR and ch:
                    fn = strip(ch[0])
                    if fn.kind == K.DECL_REF_EXPR and fn.referenced is not None and fn.referenced.kind == K.FUNCTION_DECL:
                        dk = self.def_key(fn.referenced)
                        if dk is not None:
                            cs.add(dk)
                        ch = ch[1:]
                    else:
                        indirect.add(key)
                elif k == K.DECL_REF_EXPR and x.referenced is not None and x.referenced.kind == K.FUNCTION_DECL:
                    dk = self.def_key(x.referenced)
                    if dk is not None:
                        takes.add(dk)
                elif k == K.BINARY_OPERATOR and binop(x) == '=' or k == K.COMPOUND_ASSIGNMENT_OPERATOR:
                    g = target_global(ch[0])
                    if g is not None:
                        asg.add(g)
                elif k == K.UNARY_OPERATOR:
                    op = unop(x)
                    g = target_global(ch[0])
                    if g is not None and op in ('post++', 'post--', 'pre++', 'pre--'):
                        asg.add(g)
                    if g is not None and op == '&':
                        addr_globals.add(g)
                stack.extend(ch)
            calls[key], assigns[key] = cs | takes, asg     # a function that takes an address may hand it on
            addr_funcs |= takes
        for key in indirect:
            calls[key] |= addr_funcs
        cand = set()
        for gk, c in self.F.globals.items():
            t = canon(c.type)
            if gk in self.gname and (t.kind in (T.POINTER, T.CONSTANTARRAY, T.INCOMPLETEARRAY) or ctag(t) == 'rec'):
                cand.add(gk)
        cand -= addr_globals
        for key in self.F.funcs:
            seen, stack, asg = {key}, [key], set()
            while stack:
                f = stack.pop()
                asg |= assigns.get(f, set())
                for g in calls.get(f, ()):
                    if g not in seen:
                        seen.add(g)
                        stack.append(g)
            self.gcache_ok[key] = cand - asg
        self.cur_file = None

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = lident(name)
        mk, cp = [], []
        for f in fields:
            t = canon(f.type)
            fn = self.field(f.spelling)
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    mk.append('%s = R.buf(%d)' % (fn, t.element_count))
                    cp.append('%s = R.copyBuf(s.%s)' % (fn, fn))
                else:
                    mk.append('%s = %s' % (fn, self.new_array(t)))
                    if et.kind == T.RECORD:
                        cp.append('%s = R.copyRecs(s.%s, T.copy_%s)' % (fn, fn, self.rec(et)))
                    elif et.kind == T.CONSTANTARRAY:
                        cp.append('%s = R.copyGrid(s.%s)' % (fn, fn))
                    else:
                        cp.append('%s = R.copyArr(s.%s)' % (fn, fn))
            elif t.kind == T.RECORD:
                mk.append('%s = T.%s()' % (fn, self.rec(t)))
                cp.append('%s = T.copy_%s(s.%s)' % (fn, self.rec(t), fn))
            else:
                if self.is_ref_decl(f):
                    self.problems.append('ref field %s.%s' % (name, f.spelling))
                z = self.zero(f.type)
                if z != 'nil':
                    mk.append('%s = %s' % (fn, z))
                cp.append('%s = s.%s' % (fn, fn))
        out = ['T.%s = function() return {%s} end' % (nm, ', '.join(mk)),
               'T.copy_%s = function(s) return {%s} end' % (nm, ', '.join(cp)), '']
        return out

    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        self.boxed_locals = set(); self.locals = {}
        self.pre, self.post = [], []
        t = canon(c.type)
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return 'G.%s = %s' % (name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return 'G.%s = R.bufFrom(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return 'G.%s = R.buf(%d)' % (name, t.element_count)
            return 'G.%s = %s' % (name, self.new_array(t))
        if t.kind == T.RECORD:
            return 'G.%s = T.%s()' % (name, self.rec(t))
        v = self.conv(self.val(init[-1]), init[-1].type, c.type).code if init else self.zero(c.type)
        return 'G.%s = %s' % (name, v)

    def emit(self, outdir):
        with lua_names():
            return self._emit(outdir)

    def _emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        for f in os.listdir(outdir):
            if f.startswith('F_') and f.endswith('.lua') or f in ('Types.lua', 'Consts.lua'):
                os.remove(os.path.join(outdir, f))
        self.delegate_ref = {}
        self.static_locals = []
        self.cur_file = None
        self.tmp = 0
        self.pre, self.post = [], []
        self.analyze_globals()
        files = collections.defaultdict(list)
        for key, c in self.F.funcs.items():
            if key[0] in SKIP_FILES or key in OVERRIDES:
                continue
            try:
                files[key[0]] += self.function(key, c) + ['']
            except Exception as ex:
                import traceback; traceback.print_exc()
                self.problems.append('%s:%s CRASH %s' % (key[0], key[1], ex))
        glob = collections.defaultdict(list)
        for k, c in self.F.globals.items():
            b = self.F.global_owner[k]
            if b in SKIP_FILES:
                continue
            glob[b].append(self.global_decl(k, c))
        for d, b in self.static_locals:
            self.cur_file = b
            t = canon(d.type)
            init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
            name = self.static_local_name(d)
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                glob[b].append('G.%s = %s' % (name, self.init_list(strip(init[-1]), t).code))
            elif ctag(t) == 'c' and t.kind == T.CONSTANTARRAY:
                if init:
                    glob[b].append('G.%s = R.bufFrom(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count))
                else:
                    glob[b].append('G.%s = R.buf(%d)' % (name, t.element_count))
            elif t.kind == T.CONSTANTARRAY:
                glob[b].append('G.%s = %s' % (name, self.new_array(t)))
            elif ctag(t) == 'rec':
                glob[b].append('G.%s = T.%s()' % (name, self.rec(t)))
            elif init:
                glob[b].append('G.%s = %s' % (name, self.conv(self.val(init[-1]), init[-1].type, d.type).code))
            else:
                glob[b].append('G.%s = %s' % (name, self.zero(d.type)))
        names = sorted(set(files) | set(glob))
        allconsts = collections.OrderedDict()
        for b in names:
            consts = self.consts_used.get(b, {})
            items = list(consts.items())
            local_items, k_items = items[:MAX_CHUNK_CONSTS], items[MAX_CHUNK_CONSTS:]
            body = '\n'.join(glob.get(b, []) + [''] + files.get(b, []))
            for n, v in k_items:
                body = re.sub(r'(?<![\w.])%s(?![\w])' % re.escape(n), 'K.' + n, body)
            for n, v in items:
                allconsts[n] = v
            lines = ['-- Generated from EPA SWMM 5.2.4 (%s) by tools/c2x/emit_lua.py. Do not edit by hand;' % b,
                     '-- fix the translator, rt.lua or overrides.lua instead.', PREAMBLE.rstrip('\n')]
            for n, v in local_items:            # one per statement: Lua folds only a statement's last <const>
                lines.append('local %s <const> = %s' % (n, v))
            lines += ['local _ENV = R.strict', '', body]
            open(os.path.join(outdir, fclass(b) + '.lua'), 'w').write('\n'.join(lines) + '\n')
        out = ['-- Generated by tools/c2x/emit_lua.py from EPA SWMM 5.2.4 headers: one constructor and one copy',
               '-- function per C struct (a C value copy).', 'local F, G, R, S, T, K = ...', 'local _ENV = R.strict', '']
        for name, c in self.F.records.items():
            out += self.record(name, c)
        open(os.path.join(outdir, 'Types.lua'), 'w').write('\n'.join(out) + '\n')
        out = ['-- Generated by tools/c2x/emit_lua.py from EPA SWMM 5.2.4 string literals and constants.',
               'local F, G, R, S, T, K = ...', 'local _ENV = R.strict', '']
        for bts, i in self.lits.items():
            out.append('S[%d] = R.lit(%s)' % (i, lua_string(bts)))
        for n, v in allconsts.items():
            out.append('K.%s = %s' % (n, v))
        open(os.path.join(outdir, 'Consts.lua'), 'w').write('\n'.join(out) + '\n')
        open(os.path.join(outdir, 'files.lua'), 'w').write(
            '-- Generated by tools/c2x/emit_lua.py: the engine chunks main.lua loads, in this order.\nreturn {%s}\n'
            % ', '.join('"%s"' % fclass(b) for b in names))
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = LuaEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_lua')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
