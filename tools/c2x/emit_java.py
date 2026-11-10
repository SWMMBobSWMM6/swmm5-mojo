"""
emit_java.py - EPA SWMM 5.2.4 C  ->  Java 17+ (package swmm5: one class F_<file> per C file, records and
function-pointer interfaces in Types.java, enums/macros/string literals in Consts.java).

Derived from the C# back end (static types, classes for structs), with the reference model of the
Python and TypeScript back ends, because Java has no ref parameters:
  int/long/double/float     -> int/long/double/float  (Java's binary promotion and wrapping are C's)
  unsigned int              -> long masked to 32 bits (& 0xFFFFFFFFL)     size_t / unsigned long -> long
  double/float -> int       -> R.D2I / R.D2L (x86-64 cvttsd2si: NaN or out of range -> INT_MIN;
                               Java's own casts saturate instead)
  exp log log10 pow sin cos tan asin acos atan -> Glibm.* : bit-exact ports of glibc 2.39's FMA variants
  char* / char[]            -> CPtr (byte[] + offset); p[i] -> p.g(i), p[i] = v -> p.s(i, v)
  scalar pointer params     -> DRef/IRef/LRef/FRef (get/set); locals whose address is taken -> DBox/IBox/...
  T* / T[]                  -> T[]          struct -> class with copy() = C value copy
  function pointers         -> generated interfaces FP0.. (method references F_x::f)
Java rejects unreachable statements and non-statement expressions that C accepts; the emitter drops the
first and wraps the second (R.discard). Written by Claude (Anthropic); see AI-USE.md.
"""
import os, re, sys, collections, struct
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import CSEmitter, Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null

JAVA_RESERVED = set('''abstract assert boolean break byte case catch char class const continue default do double else enum
extends final finally float for goto if implements import instanceof int interface long native new package private
protected public return short static strictfp super switch synchronized this throw throws transient try void volatile
while true false null var record yield sealed permits R Math Double Integer Long Float System String Object CPtr CFile
Glibm Consts Overrides Types Main DRef IRef LRef FRef ORef DBox IBox LBox FBox OBox equals hashCode toString getClass
notify notifyAll wait finalize clone'''.split())

JT = {'i': 'int', 'u': 'long', 'l': 'long', 'ul': 'long', 'd': 'double', 'f': 'float'}
REFT = {'d': 'DRef', 'f': 'FRef', 'i': 'IRef', 'u': 'LRef', 'l': 'LRef', 'ul': 'LRef'}
BOXT = {'d': 'DBox', 'f': 'FBox', 'i': 'IBox', 'u': 'LBox', 'l': 'LBox', 'ul': 'LBox'}
MATH = {'fabs': 'Math.abs', 'sqrt': 'Math.sqrt', 'floor': 'Math.floor', 'ceil': 'Math.ceil',
        'exp': 'Glibm.exp', 'log': 'Glibm.log', 'log10': 'Glibm.log10', 'sin': 'Glibm.sin', 'cos': 'Glibm.cos',
        'tan': 'Glibm.tan', 'asin': 'Glibm.asin', 'acos': 'Glibm.acos', 'atan': 'Glibm.atan'}
MASK = '0xFFFFFFFFL'


def jident(n):
    return n + '_' if n in JAVA_RESERVED else n


def java_string(b):
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
            out.append('\\u%04x' % ch)
    return '"' + ''.join(out) + '"'


def fclass(b):
    return 'F_' + re.sub(r'\W', '_', b[:-2])


class JavaEmitter(CSEmitter):
    def __init__(self, F):
        super().__init__(F)
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        self.fname = {}
        for (b, n), c in F.funcs.items():
            self.fname[(b, n)] = jident(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.gname = {}
        for k, c in F.globals.items():
            n = c.spelling
            b = F.global_owner[k]
            self.gname[k] = jident(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.boxed_globals = set()
        self._find_boxed_globals()
        self.pre, self.post = [], []

    _find_boxed_globals = None   # set below (shared with the TypeScript back end)

    # ================================================================== naming
    def global_key(self, d):
        k = decl_key(d)
        if k in self.gname:
            return k
        for gk, c in self.F.globals.items():
            if c.spelling == d.spelling and not front.is_static(c):
                return gk
        return None

    def global_ref(self, d):
        k = self.global_key(d)
        if k is not None:
            return self.gname[k]
        if d.spelling in ('stdout', 'stderr'):
            return 'R.stdout'
        return jident(d.spelling)

    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = 'L%d' % len(self.lits)
        return self.lits[b]

    def macro_name(self, n):
        for b, m in self.F.macros.items():
            if n in m and m[n][0] in ('int', 'float') and n in self.macro_global:
                return jident(n)
        return None

    def static_local_name(self, d):
        return jident('%s_%s' % (d.semantic_parent.spelling, d.spelling))

    def local_name(self, d):
        return self.locals.get(decl_key(d), jident(d.spelling))

    def declare_local(self, d):
        n = d.spelling
        nn = n
        if n in self.used_names:
            i = 2
            while '%s_%d' % (n, i) in self.used_names:
                i += 1
            nn = '%s_%d' % (n, i)
        self.used_names.add(nn)
        self.locals[decl_key(d)] = jident(nn)
        return jident(nn)

    def field(self, n):
        return jident(n)

    # ================================================================== types
    def rec(self, t):
        return jident(record_name(t))

    def jtype(self, t, decl=None, mode=None):
        t = canon(t)
        tg = ctag(t)
        if tg in JT:
            return JT[tg]
        if tg == 'v':
            return 'void'
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
            return 'Object'
        if cat == 'func':
            return self.delegate(t)
        e = canon(t.element_type if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) else t.get_pointee())
        if cat == 'record':
            if (mode in (None, 'array') and t.kind != T.POINTER) or mode == 'array':
                return self.rec(e) + '[]'
            return self.rec(e)
        if cat == 'scalar':
            if mode == 'ref':
                return REFT[ctag(e)]
            return JT[ctag(e)] + '[]'
        if cat == 'ptrptr':
            inner = self.jtype(e, mode='obj' if ptr_category(e) == 'record' else 'array')
            if mode == 'ref':
                return 'ORef<%s>' % inner
            return inner + '[]'
        return 'Object'

    def cs_type(self, t, decl=None, mode=None):
        return self.jtype(t, decl, mode)

    def box_type(self, d):
        tg = ctag(d.type)
        if tg in BOXT:
            return BOXT[tg]
        return 'OBox<%s>' % self.jtype(d.type, d)

    def zero(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0L', 'l': '0L', 'ul': '0L', 'd': '0.0', 'f': '0.0f'}.get(tg, 'null')

    # ================================================================== conversions
    def to_ctype(self, e, t):
        want = ctag(t)
        if e.tag == 'b' and want in NUMTAGS:
            return Ex('(%s ? 1 : 0)' % e.code, want)
        return e

    def as_bool(self, e):
        if e.tag == 'b':
            return e.code
        if e.tag in ('i', 'u', 'l', 'ul'):
            return '(%s != 0)' % e.code
        if e.tag in ('d', 'f'):
            return '(%s != 0.0)' % e.code
        return '(%s != null)' % e.code

    def conv(self, e, src_t, dst_t):
        s, d = ctag(src_t), ctag(dst_t)
        if e.tag == 'b' and d in NUMTAGS:
            e = Ex('(%s ? 1 : 0)' % e.code, 'i'); s = 'i'
        if s == d or d in ('v', '?'):
            return Ex(e.code, d if d != '?' else e.tag)
        if d == 'rec':
            return e
        if d == 'i':
            if s in ('d', 'f'):
                return Ex('R.D2I(%s)' % e.code, 'i')
            if s in ('l', 'u', 'ul'):
                return Ex('(int) (%s)' % e.code, 'i')
            return Ex(e.code, 'i')
        if d in ('l', 'ul'):
            if s in ('d', 'f'):
                return Ex('R.D2L(%s)' % e.code, d)
            return Ex(e.code, d)
        if d == 'u':
            if s in ('d', 'f'):
                return Ex('(R.D2L(%s) & %s)' % (e.code, MASK), 'u')
            return Ex('((%s) & %s)' % (e.code, MASK), 'u')
        if d == 'd':
            return Ex(e.code, 'd')
        if d == 'f':
            if s == 'f':
                return e
            return Ex('(float) (%s)' % e.code, 'f')
        if d in ('c', 'o'):
            if is_null(e.code) or e.code == 'null' or e.tag == 'n' or (e.tag in ('i', 'l') and e.code == '0'):
                return Ex('null', d)
            return Ex(e.code, d)
        return e

    # ================================================================== leaves
    def x_INTEGER_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        suf = 'L' if tg in ('l', 'u', 'ul') else ''
        if len(toks) == 1 and re.fullmatch(r'\d+[uUlL]*', toks[0]):
            s = re.sub(r'[uUlL]+$', '', toks[0])
            if len(s) > 1 and s.startswith('0'):
                s = str(int(s, 8))
            return Ex(s + suf, tg)
        if len(toks) == 1 and self.macro_name(toks[0]):
            return Ex(self.macro_name(toks[0]), tg)
        v = evaluate(c)
        x = v[1] if v else 0
        if tg in ('u', 'ul') and x < 0:
            x &= 0xFFFFFFFFFFFFFFFF if tg == 'ul' else 0xFFFFFFFF
        if x > 9223372036854775807:
            x -= 1 << 64
        return Ex(str(x) + suf, tg)

    def x_FLOATING_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?[lL]?', toks[0]) and tg != 'f':
            s = toks[0].rstrip('lL')
            if s.startswith('.'):
                s = '0' + s
            s = re.sub(r'\.([eE])', r'.0\1', s)
            if s.endswith('.'):
                s += '0'
            if '.' not in s and 'e' not in s.lower():
                s += '.0'
            return Ex(s, tg)
        if len(toks) == 1 and self.macro_name(toks[0]) and tg != 'f':
            return Ex(self.macro_name(toks[0]), tg)
        v = evaluate(c)
        x = v[1] if v else 0.0
        if tg == 'f':
            x = struct.unpack('<f', struct.pack('<f', x))[0]
        if x != x:
            return Ex('Double.NaN', tg)
        if abs(x) == float('inf'):
            return Ex('Double.POSITIVE_INFINITY' if x > 0 else 'Double.NEGATIVE_INFINITY', tg)
        return Ex(repr(x) + ('f' if tg == 'f' else ''), tg)

    def x_CHARACTER_LITERAL(self, c):
        v = evaluate(c)
        return Ex(str(v[1] if v else 0), 'i')

    def x_STRING_LITERAL(self, c):
        return Ex(self.lit(self.string_bytes(c)), 'c')

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return Ex(jident(c.spelling), '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return Ex(str(d.enum_value), 'i')
            return Ex(jident(d.spelling), 'i')
        if d.kind == K.FUNCTION_DECL:
            keys = self.F.func_by_decl.get(d.spelling) or []
            cand = [k for k in keys if k[0] == self.cur_file] or [k for k in keys if self.F.funcs[k].storage_class != front.ci.StorageClass.STATIC]
            if not cand:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex(jident(d.spelling), 'o')
            return Ex('%s::%s' % (fclass(cand[0][0]), self.fname[cand[0]]), 'o')
        if d.kind == K.PARM_DECL or (d.kind == K.VAR_DECL and d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL
                                     and d.storage_class != front.ci.StorageClass.STATIC):
            nm = self.local_name(d)
            if decl_key(d) in self.boxed_locals:
                return Ex(nm + '.v', ctag(d.type))
            return Ex(nm, ctag(d.type))
        if d.kind == K.VAR_DECL:
            if d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL:
                return Ex(self.static_local_name(d), ctag(d.type))
            gk = self.global_key(d)
            nm = self.global_ref(d)
            if gk in self.boxed_globals:
                return Ex(nm + '.v', ctag(d.type))
            return Ex(nm, ctag(d.type))
        return Ex(jident(c.spelling), ctag(c.type))

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                return Ex(self.zero(c.type), ctag(c.type))
            return self.ex(ch[0])
        e = self.ex(ch[0])
        if canon(c.type).kind == T.POINTER and e.tag in ('i', 'l') and e.code in ('0', '0L'):
            return Ex('null', ctag(c.type))
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
        if (e.tag in ('i', 'l') and e.code in ('0', '0L') and canon(c.type).kind == T.POINTER) or is_null(e.code) or e.code == 'null':
            return Ex('null', ctag(c.type))
        if ctag(c.type) == 'o' and ctag(inner.type) == 'o':
            if ptr_category(inner.type) == 'void' and ptr_category(c.type) in ('record', 'scalar', 'ptrptr'):
                return Ex('((%s) %s)' % (self.jtype(c.type, mode='obj' if ptr_category(c.type) == 'record' else 'array'), self.paren(e.code)), 'o')
            return e
        tgt, src = ctag(c.type), ctag(inner.type)
        e = self.to_ctype(e, inner.type)
        if tgt == 'd' and src in ('i', 'l', 'u', 'ul'):
            return Ex('((double) (%s))' % e.code, 'd')
        if tgt == 'f' and src != 'f':
            return Ex('((float) (%s))' % e.code, 'f')
        r = self.conv(e, inner.type, c.type)
        k = canon(c.type).kind
        if k in (T.UCHAR, T.CHAR_U):
            return Ex('((%s) & 255)' % r.code, 'i')
        if k in (T.CHAR_S, T.SCHAR) and canon(inner.type).kind not in (T.CHAR_S, T.SCHAR):
            return Ex('((byte) (%s))' % r.code, 'i')
        if k == T.SHORT:
            return Ex('((short) (%s))' % r.code, 'i')
        if k == T.USHORT:
            return Ex('((%s) & 65535)' % r.code, 'i')
        return r

    def x_CXX_UNARY_EXPR(self, c):
        v = evaluate(c)
        return Ex((str(v[1]) if v else '8') + 'L', 'ul')

    def x_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        return Ex('(%s)' % e.code, e.tag)

    def paren(self, s):
        if re.fullmatch(r'[\w.\[\]]+', s) or (s.startswith('(') and s.endswith(')') and self._balanced(s[1:-1])):
            return s
        return '(' + s + ')'

    def idx(self, e):
        """an array index (Java wants int)"""
        if e.tag in ('l', 'u', 'ul'):
            return '(int) (%s)' % e.code
        return e.code

    # ================================================================== lvalues
    def lv_kind(self, l):
        """('char', base, index) | ('ref', refcode, tag) | ('plain', code)"""
        sl = strip(l)
        if sl.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ix = kids(sl)
            if ptr_category(base.type) == 'char':
                return ('char', self.ex(base).code, self.idx(self.val(ix)))
        if sl.kind == K.UNARY_OPERATOR and unop(sl) == '*':
            a = kids(sl)[0]
            sa = strip(a)
            if ptr_category(a.type) == 'char':
                if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                    x, y = kids(sa)
                    if ptr_category(x.type) == 'char':
                        i = self.idx(self.val(y))
                        return ('char', self.ex(x).code, i if binop(sa) == '+' else '-(%s)' % i)
                return ('char', self.ex(a).code, '0')
            if ptr_category(a.type) in ('scalar', 'ptrptr') and self.mode_of_expr(sa) == 'ref':
                return ('ref', self.ex(a).code, ctag(canon(a.type).get_pointee()))
        return ('plain', self.lvalue(l))

    def assign_code(self, l, rhs):
        k = self.lv_kind(l)
        if k[0] == 'char':
            return '%s.s(%s, %s)' % (self.paren(k[1]), k[2], rhs)
        if k[0] == 'ref':
            return '%s.set(%s)' % (k[1], rhs)
        return '%s = %s' % (k[1], rhs)

    def ref_of(self, a):
        """a reference object for lvalue a"""
        sa = strip(a)
        k = self.lv_kind(a)
        if k[0] == 'char':
            return 'new CharRef(%s, %s)' % (k[1], k[2])
        if k[0] == 'ref':
            return k[1]
        lv = k[1]
        tg = ctag(sa.type)
        if lv.endswith('.v') and sa.kind == K.DECL_REF_EXPR:
            return lv[:-2]
        if sa.kind == K.MEMBER_REF_EXPR:
            obj, attr = lv.rsplit('.', 1)
            base = kids(sa)[0]
            bt = canon(base.type)
            rt = self.rec(bt.get_pointee() if bt.kind == T.POINTER else bt)
            if tg in REFT:
                return 'new %sField<%s>(%s, __o -> __o.%s, (__o, __x) -> __o.%s = __x)' % (REFT[tg][0], rt, obj, attr, attr)
            return 'new OField<%s, %s>(%s, __o -> __o.%s, (__o, __x) -> __o.%s = __x)' % (rt, self.jtype(sa.type), obj, attr, attr)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ix = kids(sa)
            if tg in REFT:
                return 'new %sElem(%s, %s)' % (REFT[tg][0], self.ex(base).code, self.idx(self.val(ix)))
            return 'new OElem<%s>(%s, %s)' % (self.jtype(sa.type), self.ex(base).code, self.idx(self.val(ix)))
        if sa.kind == K.DECL_REF_EXPR:
            if tg in REFT:
                return 'new %sAcc(() -> %s, (__x) -> %s = __x)' % (REFT[tg][0], lv, lv)
            return 'new OAcc<%s>(() -> %s, (__x) -> %s = __x)' % (self.jtype(sa.type), lv, lv)
        self.problem(a, 'reference to %s' % lv)
        return 'null'

    def read_lv(self, a):
        k = self.lv_kind(a)
        if k[0] == 'char':
            return '%s.g(%s)' % (self.paren(k[1]), k[2])
        if k[0] == 'ref':
            return '%s.get()' % k[1]
        return k[1]

    # ================================================================== operators
    def x_UNARY_OPERATOR(self, c):
        op = unop(c)
        a = kids(c)[0]
        if op == '&':
            return self.addr_of(a, c)
        if op == '*':
            return self.deref(a)
        if op == '!':
            return Ex('!%s' % self.paren(self.cond(a)), 'b')
        if op in ('pre++', 'pre--', 'post++', 'post--'):
            return self.incdec_expr(a, op)
        e = self.val(a)
        if op == '-':
            if e.tag == 'u':
                return Ex('((-%s) & %s)' % (self.paren(e.code), MASK), 'u')
            return Ex('(-%s)' % self.paren(e.code), e.tag)
        if op == '+':
            return e
        if op == '~':
            if e.tag == 'u':
                return Ex('((~%s) & %s)' % (self.paren(e.code), MASK), 'u')
            return Ex('(~%s)' % self.paren(e.code), e.tag)
        self.problem(c, 'unary ' + op)
        return e

    def incdec_expr(self, a, op):
        d = '+' if '++' in op else '-'
        tg = ctag(a.type)
        pre = op.startswith('pre')
        k = self.lv_kind(a)
        if k[0] == 'char':
            nv = '%s.s(%s, %s.g(%s) %s 1)' % (self.paren(k[1]), k[2], self.paren(k[1]), k[2], d)
            return Ex(nv if pre else '(%s %s 1)' % (nv, '-' if d == '+' else '+'), 'i')
        if k[0] == 'ref':
            nv = '%s.set(%s.get() %s 1)' % (k[1], k[1], d)
            if pre:
                return Ex(nv, tg)
            if tg in ('i', 'l', 'ul'):
                return Ex('(%s %s 1)' % (nv, '-' if d == '+' else '+'), tg)
            return Ex('R.post(%s, %s1)' % (k[1], d), tg)
        lv = k[1]
        if tg == 'c':
            step = '1' if d == '+' else '-1'
            nv = '(%s = %s.add(%s))' % (lv, self.paren(lv), step)
            return Ex(nv if pre else '%s.add(%s)' % (nv, '-1' if d == '+' else '1'), 'c')
        if tg == 'u':
            if pre:
                return Ex('(%s = (%s %s 1) & %s)' % (lv, lv, d, MASK), 'u')
        return Ex(('%s%s%s' % (d, d, lv)) if pre else ('%s%s%s' % (lv, d, d)), tg)

    def deref(self, a):
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                x, y = kids(sa)
                if ptr_category(x.type) == 'char':
                    i = self.idx(self.val(y))
                    return Ex('%s.g(%s)' % (self.paren(self.ex(x).code), i if binop(sa) == '+' else '-(%s)' % i), 'i')
            return Ex('%s.g(0)' % self.paren(self.ex(a).code), 'i')
        e = self.ex(a)
        if cat == 'record':
            return Ex(e.code, 'rec')
        mode = self.mode_of_expr(sa)
        pt = ctag(canon(a.type).get_pointee())
        if mode == 'ref':
            return Ex(e.code + '.get()', pt)
        if sa.kind == K.BINARY_OPERATOR:
            l, r = kids(sa)
            return Ex('%s[%s]' % (self.ex(l).code, self.idx(self.val(r))), pt)
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
                b = self.ex(base).code; i = self.idx(self.val(ix))
                return Ex(b if i == '0' else '%s.add(%s)' % (self.paren(b), i), 'c')
            if ctag(sa.type) == 'rec':
                return Ex(self.ex(sa).code, 'o')
            i = self.val(ix).code
            if i == '0':
                return Ex(self.ex(base).code, 'o')
        return Ex(self.ref_of(sa), 'ref')

    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            if ctag(l.type) == 'rec':
                return Ex('(%s)' % self.assign_code(l, '%s.copy()' % self.paren(self.ex(r).code)), 'rec')
            re_ = self.conv(self.val(r), r.type, l.type)
            return Ex('(%s)' % self.assign_code(l, re_.code), ctag(l.type))
        if op in ('&&', '||'):
            return Ex('(%s %s %s)' % (self.paren(self.cond(l)), op, self.paren(self.cond(r))), 'b')
        if op == ',':
            self.problem(c, 'comma operator')
            return Ex('R.comma(%s, %s)' % (self.val(l).code, self.val(r).code), ctag(c.type))
        lt, rt = canon(l.type), canon(r.type)
        le, re_ = self.val(l), self.val(r)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            if le.tag in ('c', 'o', 'n') or re_.tag in ('c', 'o', 'n'):
                nl = is_null(le.code) or le.code == 'null' or (le.tag in ('i', 'l') and le.code in ('0', '0L'))
                nr = is_null(re_.code) or re_.code == 'null' or (re_.tag in ('i', 'l') and re_.code in ('0', '0L'))
                if op in ('==', '!=') and (nl or nr):
                    x = le.code if not nl else re_.code
                    return Ex('(%s %s null)' % (self.paren(x), op), 'b')
                if ptr_category(l.type) == 'char' or ptr_category(r.type) == 'char':
                    if op in ('==', '!='):
                        return Ex('%sR.peq(%s, %s)' % ('' if op == '==' else '!', le.code, re_.code), 'b')
                    return Ex('(%s.o %s %s.o)' % (self.paren(le.code), op, self.paren(re_.code)), 'b')
                return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
            return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
        tg = ctag(c.type)
        if tg == 'c':
            if op == '+':
                if ptr_category(l.type) == 'char':
                    return Ex('%s.add(%s)' % (self.paren(le.code), self.idx(re_)), 'c')
                return Ex('%s.add(%s)' % (self.paren(re_.code), self.idx(le)), 'c')
            return Ex('%s.add(-%s)' % (self.paren(le.code), self.paren(self.idx(re_))), 'c')
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            return Ex('((long) (%s.o - %s.o))' % (self.paren(le.code), self.paren(re_.code)), 'l')
        return Ex(self.arith(op, le.code, re_.code, tg), tg)

    def arith(self, op, a, b, tg):
        if tg == 'u':
            if op in ('+', '-', '*', '<<'):
                return '((%s %s %s) & %s)' % (a, op, b, MASK)
            return '(%s %s %s)' % (a, op, b)
        if tg == 'i' and op in ('<<', '>>'):
            return '(%s %s %s)' % (a, op, b)
        return '(%s %s %s)' % (a, op, b)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        return Ex('(%s)' % self.compound_code(c), ctag(kids(c)[0].type))

    def compound_code(self, c):
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        re_ = self.val(r)
        k = self.lv_kind(l)
        if lt == 'c':
            lv = k[1]
            if op == '+':
                return '%s = %s.add(%s)' % (lv, self.paren(lv), self.idx(re_))
            return '%s = %s.add(-%s)' % (lv, self.paren(lv), self.paren(self.idx(re_)))
        common = 'd' if 'd' in (lt, rt) else ('f' if 'f' in (lt, rt) else ('ul' if 'ul' in (lt, rt) else
                  ('l' if 'l' in (lt, rt) else ('u' if 'u' in (lt, rt) else 'i'))))
        cur = self.read_lv(l)
        v = self.arith(op, cur, self.paren(re_.code), common)
        if lt in ('i', 'l', 'u', 'ul') and common in ('d', 'f'):
            v = {'i': 'R.D2I(%s)', 'l': 'R.D2L(%s)', 'u': '(R.D2L(%s) & 0xFFFFFFFFL)', 'ul': 'R.D2L(%s)'}[lt] % v
        elif lt == 'f' and common == 'd':
            v = '(float) %s' % v
        elif lt == 'i' and common in ('l', 'u', 'ul'):
            v = '(int) %s' % v
        elif lt == 'u' and common != 'u':
            v = '(%s & %s)' % (v, MASK)
        if k[0] == 'char':
            if common in ('d', 'f'):
                v = 'R.D2I(%s)' % v
            return '%s.s(%s, %s)' % (self.paren(k[1]), k[2], v)
        if k[0] == 'ref':
            return '%s.set(%s)' % (k[1], v)
        if common == lt and lt in ('d', 'f', 'i', 'l', 'ul') and op in ('+', '-', '*', '/'):
            return '%s %s= %s' % (k[1], op, self.paren(re_.code))
        return '%s = %s' % (k[1], v)

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        tg = ctag(c.type)
        ea = self.conv(self.val(a), a.type, c.type)
        eb = self.conv(self.val(b), b.type, c.type)
        if tg in ('c', 'o') and (ea.code == 'null' or eb.code == 'null'):
            ty = self.jtype(c.type, mode='obj' if ptr_category(c.type) == 'record' else 'array')
            if ea.code == 'null':
                ea = Ex('(%s) null' % ty, tg)
            if eb.code == 'null':
                eb = Ex('(%s) null' % ty, tg)
        return Ex('(%s ? %s : %s)' % (self.cond(cc), ea.code, eb.code), tg)

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, ix = kids(c)
        if ptr_category(base.type) == 'char':
            return Ex('%s.g(%s)' % (self.paren(self.ex(base).code), self.idx(self.val(ix))), 'i')
        b = self.ex(base)
        return Ex('%s[%s]' % (self.paren(b.code), self.idx(self.val(ix))), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        b = self.ex(base)
        return Ex('%s.%s' % (self.paren(b.code), self.field(c.referenced.spelling)), ctag(c.type))

    # ================================================================== init lists
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
                return Ex('R.bufOf(%d, new int[] { %s })' % (n, ', '.join(self.val(it).code for it in items)), 'c')
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
                    vals.append('new %s()' % self.rec(et))
                elif et.kind == T.CONSTANTARRAY:
                    vals.append(self.new_array(et))
                else:
                    vals.append(self.zero(et))
            return Ex('new %s { %s }' % (self.jtype(t, mode='array'), ', '.join(vals)), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                if strip(it).kind == K.INIT_LIST_EXPR:
                    parts.append('__r.%s = %s;' % (self.field(f.spelling), self.init_list(strip(it), f.type).code))
                else:
                    parts.append('__r.%s = %s;' % (self.field(f.spelling), self.conv(self.val(it), it.type, f.type).code))
            return Ex('R.make(new %s(), __r -> { %s })' % (self.rec(t), ' '.join(parts)), 'rec')
        if len(items) == 1:
            return self.val(items[0])
        self.problem(c, 'init list for %s' % t.spelling)
        return Ex('null', '?')

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
            codes = []
            for i, (a, p) in enumerate(zip(args, params)):
                sa = strip(a)
                if (ptr_category(p.type) == 'scalar' and self.P.mode_of(p) == 'array' and sa.kind == K.UNARY_OPERATOR
                        and unop(sa) == '&' and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    # &x passed where the callee indexes an array: a one-element array, copied back
                    o = kids(sa)[0]
                    self.tmp += 1
                    t = '__a%d' % self.tmp
                    pt = canon(p.type)
                    et = JT[ctag(pt.get_pointee() if pt.kind == T.POINTER else pt.element_type)]
                    self.pre.append('%s[] %s = new %s[] { %s };' % (et, t, et, self.read_lv(o)))
                    self.post.append(self.assign_code(o, '%s[0]' % t) + ';')
                    codes.append(t)
                    continue
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    o = kids(sa)[0]
                    self.tmp += 1
                    t = '__c%d' % self.tmp
                    self.pre.append('CPtr %s = R.buf(2); %s.s(0, %s);' % (t, t, self.read_lv(o)))
                    self.post.append(self.assign_code(o, '%s.g(0)' % t) + ';')
                    codes.append(t)
                    continue
                codes.append(self.arg(a, p))
            return Ex('%s(%s)' % (n, ', '.join(codes)), ctag(c.type))
        fe = self.ex(callee)
        dname = self.delegate(canon(strip(callee).type)) if canon(strip(callee).type).kind == T.POINTER else None
        argcodes = []
        for i, a in enumerate(args):
            sa = strip(a)
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and ctag(strip(kids(sa)[0]).type) in NUMTAGS:
                self.delegate_ref[(dname, i)] = True
                argcodes.append(self.ref_of(kids(sa)[0]))
            elif ptr_category(a.type) == 'scalar' and self.mode_of_expr(sa) == 'ref':
                self.delegate_ref[(dname, i)] = True
                argcodes.append(self.ex(sa).code)
            else:
                argcodes.append(self.val(a).code)
        return Ex('%s.call(%s)' % (self.paren(fe.code), ', '.join(argcodes)), ctag(c.type))

    def arg(self, a, p):
        pmode = self.P.mode_of(p)
        cat = ptr_category(p.type)
        sa = strip(a)
        if (cat == 'scalar' and pmode == 'ref') or (cat == 'ptrptr' and pmode == 'ref'):
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return self.ref_of(kids(sa)[0])
            if self.mode_of_expr(sa) == 'ref':
                return self.ex(sa).code
            e = self.ex(sa)
            if is_null(e.code) or e.code == 'null' or (e.tag in ('i', 'l') and e.code in ('0', '0L')):
                return 'null'
            pt = ctag(canon(p.type).get_pointee())
            if pt in REFT:
                return 'new %sElem(%s, 0)' % (REFT[pt][0], e.code)
            return 'new OElem<>(%s, 0)' % e.code
        if cat == 'scalar' and pmode == 'array':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = strip(kids(sa)[0])
                if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                    base, ix = kids(o)
                    i = self.val(ix).code
                    if i != '0':
                        self.problem(a, 'array offset &x[%s] passed to array param %s' % (i, p.spelling))
                    return self.ex(base).code
        e = self.conv(self.val(a), a.type, p.type)
        if cat == 'char' and is_null(e.code):
            return 'null'
        if cat in ('record', 'void', 'func', 'file') and is_null(e.code):
            return 'null'
        return e.code

    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name in MATH:
            return Ex('%s(%s)' % (MATH[name], A(0)), 'd')
        if name == 'pow':
            return Ex('Glibm.pow(%s, %s)' % (A(0), A(1)), 'd')
        if name in ('fprintf', 'snprintf', 'sscanf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}[name]
            head = [A(i) for i in range(fixed)]
            if name == 'snprintf':
                head[1] = '(int) (%s)' % head[1]
            rest = [self.vararg(a, name == 'sscanf') for a in args[fixed:]]
            return Ex('R.%s(%s)' % (name, ', '.join(head + rest)), 'i')
        if name == 'free':
            return Ex('R.free(%s)' % A(0), 'v')
        if name in ('calloc', 'malloc', 'realloc'):
            return self.alloc(c, c.type)
        if name in ('fwrite', 'fread'):
            return self.freadwrite(c, name, args)
        if name == 'memset':
            dst = strip(args[0])
            if dst.kind == K.UNARY_OPERATOR and unop(dst) == '&' and ctag(strip(kids(dst)[0]).type) == 'rec':
                o = strip(kids(dst)[0])
                return Ex('%s = new %s()' % (self.lvalue(o), self.rec(o.type)), 'v')
            return Ex('R.memset(%s, %s, %s)' % (A(0), A(1), A(2)), 'v')
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return Ex('R.strtod(%s, %s)' % (A(0), self.ref_of(kids(ep)[0])), 'd')
            return Ex('R.strtod(%s, null)' % A(0), 'd')
        if name == 'time':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                return Ex('(%s)' % self.assign_code(kids(a0)[0], 'R.time()'), 'l')
            return Ex('R.time()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('R.ctime(%s)' % (self.ex(kids(a0)[0]).code if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('((double) (%s - %s))' % (A(0), A(1)), 'd')
        if name == 'fseeko':
            name = 'fseek'
        rt = {'strlen': 'ul', 'atoi': 'i', 'strcmp': 'i', 'feof': 'i', 'fclose': 'i', 'atof': 'd', 'ftell': 'l',
              'strcspn': 'ul', 'toupper': 'i', 'fseek': 'i', 'remove': 'i', 'fflush': 'i', 'rewind': 'v'}.get(name, tg)
        al = [A(i) for i in range(len(args))]
        if name == 'fgets':
            al[1] = '(int) (%s)' % al[1]
        return Ex('R.%s(%s)' % (name, ', '.join(al)), rt)

    def vararg(self, a, scanf):
        sa = strip(a)
        if scanf:
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return self.ref_of(kids(sa)[0])
            return self.val(a).code
        return self.val(a).code

    def alloc(self, call, t):
        args = list(call.get_arguments())
        t = canon(t)
        if t.kind != T.POINTER:
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
                return Ex('R.realloc(%s, %s)' % (old, n), 'c')
            if et.kind == T.RECORD:
                return Ex('R.realloc(%s, %s, %s::new)' % (old, n, self.rec(et)), 'o')
            return Ex('R.realloc(%s, %s)' % (old, n), 'o')
        if ctag(t) == 'c':
            return Ex('R.buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('new %s()' % self.rec(et), 'o')
            return Ex('R.fill(new %s[%s], %s::new)' % (self.rec(et), n, self.rec(et)), 'o')
        if et.kind == T.POINTER:
            inner = self.jtype(et, mode='array') if ptr_category(et) != 'record' else self.rec(canon(et.get_pointee()))
            if ptr_category(et) == 'char':
                inner = 'CPtr'
            if inner.endswith('[]'):
                i = inner.index('[')
                return Ex('new %s[%s]%s' % (inner[:i], n, inner[i:]), 'o')
            return Ex('new %s[%s]' % (inner, n), 'o')
        return Ex('new %s[%s]' % (self.jtype(et), n), 'o')

    def int_code(self, x):
        e = self.val(x)
        if e.tag in ('ul', 'l', 'u'):
            return '(int) (%s)' % e.code
        return e.code

    def freadwrite(self, c, name, args):
        buf, size, cnt, f = args
        sb = strip(buf)
        fc = self.val(f).code
        sz = evaluate(strip(size))
        sz = sz[1] if sz and sz[0] == 'int' else None
        if sb.kind == K.UNARY_OPERATOR and unop(sb) == '&':
            o = strip(kids(sb)[0])
            et = canon(o.type)
            if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                base, ix = kids(o)
                return Ex('R.%s(%s, %s, %s, %s)' % (name, self.ex(base).code, self.idx(self.val(ix)), self.int_code(cnt), fc), 'ul')
            nat = self.sizeof_type(et)
            if name == 'fwrite':
                return Ex('R.fwrite1(%s, %d, %s)' % (self.read_lv(o), sz or nat, fc), 'ul')
            return Ex('R.fread1(%s, %d, %s)' % (self.ref_of(o), sz or nat, fc), 'ul')
        if self.mode_of_expr(sb) == 'ref':
            et = canon(canon(sb.type).get_pointee())
            nat = self.sizeof_type(et)
            if name == 'fwrite':
                return Ex('R.fwrite1(%s.get(), %d, %s)' % (self.ex(sb).code, sz or nat, fc), 'ul')
            return Ex('R.fread1(%s, %d, %s)' % (self.ex(sb).code, sz or nat, fc), 'ul')
        return Ex('R.%s(%s, 0, %s, %s)' % (name, self.ex(sb).code, self.int_code(cnt), fc), 'ul')

    # ================================================================== statements
    def stmt(self, c, ind):
        k = c.kind
        p = '    ' * ind
        if k == K.COMPOUND_STMT:
            out = [p + '{']
            for ch in kids(c):
                out += self.stmt(ch, ind + 1)
                if not self.completes(ch):
                    break          # Java rejects unreachable statements; C ignores them
            out.append(p + '}')
            return out
        if k == K.DECL_STMT:
            out = []
            for d in kids(c):
                out += self.flush(self.local_decl(d, ind), ind)
            return out
        if k == K.IF_STMT:
            ch = kids(c)
            out = self.flush([p + 'if (%s)' % self.cond(ch[0])], ind)
            out += self.block(ch[1], ind)
            if len(ch) > 2:
                if ch[2].kind == K.IF_STMT:
                    sub = self.stmt(ch[2], ind)
                    out.append(p + 'else ' + sub[0].lstrip())
                    out += sub[1:]
                else:
                    out.append(p + 'else')
                    out += self.block(ch[2], ind)
            return out
        if k == K.WHILE_STMT:
            ch = kids(c)
            return self.flush([p + 'while (%s)' % self.cond(ch[0])], ind) + self.block(ch[1], ind)
        if k == K.DO_STMT:
            ch = kids(c)
            return [p + 'do'] + self.block(ch[0], ind) + self.flush([p + 'while (%s);' % self.cond(ch[1])], ind)
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            return [p + 'break;']
        if k == K.CONTINUE_STMT:
            return [p + 'continue;']
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'return;']
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            if ctag(self.cur_ret) in ('c', 'o') and is_null(e.code):
                e = Ex('null', 'o')
            return self.flush([p + 'return %s;' % e.code], ind)
        if k == K.NULL_STMT:
            return [p + ';']
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unhandled statement %s' % k.name)
            return []
        return self.flush([p + self.expr_stmt_code(c) + ';'], ind)

    def flush(self, lines, ind):
        """wrap a statement with the set-up and copy-back statements its call arguments needed"""
        if not self.pre and not self.post:
            return lines
        p = '    ' * ind
        pre, post = self.pre, self.post
        self.pre, self.post = [], []
        if post and any(l.strip().startswith(('return', 'if', 'while')) for l in lines):
            self.problems.append('copy-back after %s' % lines[0].strip())
        return [p + '{'] + [p + '    ' + x for x in pre] + ['    ' + l for l in lines] + [p + '    ' + x for x in post] + [p + '}']

    def block(self, c, ind):
        if c.kind == K.COMPOUND_STMT:
            return self.stmt(c, ind)
        return ['    ' * ind + '{'] + self.stmt(c, ind + 1) + ['    ' * ind + '}']

    def expr_stmt_code(self, c):
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) == 'v':
            return self.expr_stmt_code(kids(s)[-1])
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            if ctag(l.type) == 'rec':
                return self.assign_code(l, '%s.copy()' % self.paren(self.ex(r).code))
            return self.assign_code(l, self.conv(self.val(r), r.type, l.type).code)
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmt_code(l) + '; ' + self.expr_stmt_code(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            return self.compound_code(s)
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            d = '+' if '++' in unop(s) else '-'
            k = self.lv_kind(a)
            if k[0] == 'char':
                return '%s.s(%s, %s.g(%s) %s 1)' % (self.paren(k[1]), k[2], self.paren(k[1]), k[2], d)
            if k[0] == 'ref':
                return '%s.set(%s.get() %s 1)' % (k[1], k[1], d)
            lv = k[1]
            tg = ctag(a.type)
            if tg == 'c':
                return '%s = %s.add(%s1)' % (lv, self.paren(lv), '' if d == '+' else '-')
            if tg == 'u':
                return '%s = (%s %s 1) & %s' % (lv, lv, d, MASK)
            return '%s%s%s' % (lv, d, d)
        if s.kind == K.CONDITIONAL_OPERATOR:
            cc, a, b = kids(s)
            return 'if (%s) { %s; } else { %s; }' % (self.cond(cc), self.expr_stmt_code(a), self.expr_stmt_code(b))
        e = self.ex(c)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        if s.kind == K.CALL_EXPR or code.startswith(('R.free(', 'R.memset(')) or re.match(r'^[\w.\[\]]+ = ', code):
            return code
        return 'R.discard(%s)' % code

    def for_stmt(self, c, ind):
        p = '    ' * ind
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
        pre = []
        init_s = ''
        if init is not None:
            if init.kind == K.DECL_STMT:
                for d in kids(init):
                    pre += self.local_decl(d, ind + 1)
            else:
                init_s = self.expr_stmt_code(init).replace('; ', ', ')
        cond_s = self.cond(cond) if cond is not None else ''
        inc_s = self.expr_stmt_code(inc).replace('; ', ', ') if inc is not None else ''
        if self.pre or self.post:
            self.problems.append('call copy-back inside a for header')
        head = p + 'for (%s; %s; %s)' % (init_s, cond_s, inc_s)
        if pre:
            return [p + '{'] + pre + ['    ' + head] + ['    ' + l for l in self.block(body, ind)] + [p + '}']
        return [head] + self.block(body, ind)

    def switch(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        e = self.val(ch[0])
        code = e.code if e.tag != 'b' else '(%s ? 1 : 0)' % e.code
        if e.tag in ('l', 'u', 'ul'):
            code = '(int) (%s)' % code
        body = ch[-1]
        items = kids(body) if body.kind == K.COMPOUND_STMT else [body]
        out = self.flush([p + 'switch (%s) {' % code], ind)
        live = True
        for it in items:
            x = it
            labels = []
            while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                xc = kids(x)
                if x.kind == K.CASE_STMT:
                    labels.append(p + '    case %s:' % self.val(xc[0]).code)
                    x = xc[1]
                else:
                    labels.append(p + '    default:')
                    x = xc[0]
            if labels:
                live = True
                out += labels
            if not live:
                continue
            out += self.stmt(x, ind + 2)
            if not self.completes(x):
                live = False
        out.append(p + '}')
        return out

    # --- Java's "can complete normally" (JLS 14.22), on the C statement
    def completes(self, c):
        k = c.kind
        if k in (K.RETURN_STMT, K.BREAK_STMT, K.CONTINUE_STMT):
            return False
        if k == K.COMPOUND_STMT:
            for ch in kids(c):
                if not self.completes(ch):
                    return False
            return True
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
                cond = self.for_cond(c)
            const_true = cond is None or self.const_true(cond)
            if not const_true:
                return True
            return self.has_break(ch[-1] if k != K.DO_STMT else ch[0])
        if k == K.SWITCH_STMT:
            body = kids(c)[-1]
            items = kids(body) if body.kind == K.COMPOUND_STMT else [body]
            if not any(self.has_default(it) for it in items):
                return True
            if self.has_break(body):
                return True
            last = items[-1] if items else None
            if last is None:
                return True
            x = last
            while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                x = kids(x)[-1]
            return self.completes(x)
        if k in (K.CASE_STMT, K.DEFAULT_STMT):
            return self.completes(kids(c)[-1])
        return True

    def has_default(self, it):
        x = it
        while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
            if x.kind == K.DEFAULT_STMT:
                return True
            x = kids(x)[-1]
        return False

    def has_break(self, c):
        """a break that exits the enclosing loop/switch (not one inside a nested loop or switch)"""
        if c.kind == K.BREAK_STMT:
            return True
        if c.kind in (K.FOR_STMT, K.WHILE_STMT, K.DO_STMT, K.SWITCH_STMT):
            return False
        return any(self.has_break(x) for x in kids(c))

    def const_true(self, cond):
        v = evaluate(strip(cond))
        return v is not None and v[0] in ('int', 'float') and v[1] != 0

    def for_cond(self, c):
        ch = kids(c)
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
        for x in ch[:-1]:
            o = x.extent.start.offset
            if len(semis) >= 2 and semis[0] < o < semis[1]:
                return x
        return None

    def local_decl(self, d, ind):
        p = '    ' * ind
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
        ty = self.jtype(d.type, d)
        if t.kind == T.CONSTANTARRAY:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return [p + '%s %s = %s;' % (self.jtype(d.type, mode='array'), name, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return [p + 'CPtr %s = R.bufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return [p + 'CPtr %s = R.buf(%d);' % (name, t.element_count)]
            return [p + '%s %s = %s;' % (self.jtype(d.type, mode='array'), name, self.new_array(t))]
        if ctag(t) == 'rec':
            if init:
                return [p + '%s %s = %s.copy();' % (ty, name, self.paren(self.ex(init[-1]).code))]
            return [p + '%s %s = new %s();' % (ty, name, ty)]
        v = self.conv(self.val(init[-1]), init[-1].type, d.type).code if init else self.zero(d.type)
        if boxed:
            bt = self.box_type(d)
            return [p + '%s %s = new %s(%s);' % (bt, name, bt.replace('<%s>' % self.jtype(d.type, d), '<>'), v)]
        return [p + '%s %s = %s;' % (ty, name, v)]

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return 'R.fill(new %s[%d], %s::new)' % (self.rec(et), n, self.rec(et))
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return 'R.bufs(%d, %d)' % (n, et.element_count)
        if et.kind == T.CONSTANTARRAY:
            inner = canon(et.element_type)
            if ctag(inner) in JT:
                return 'new %s[%d][%d]' % (JT[ctag(inner)], n, et.element_count)
            self.problems.append('array of arrays of %s' % inner.spelling)
            return 'null'
        if et.kind == T.POINTER:
            ety = self.jtype(et, mode='array') if ptr_category(et) != 'record' else self.rec(canon(et.get_pointee()))
            if ptr_category(et) == 'char':
                ety = 'CPtr'
            if ety.endswith('[]'):
                i = ety.index('[')
                return 'new %s[%d]%s' % (ety[:i], n, ety[i:])
            return 'new %s[%d]' % (ety, n)
        return 'new %s[%d]' % (self.jtype(et), n)

    # ================================================================== functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.cur_ret = c.result_type
        self.boxed_locals = set()
        self.tmp = 0
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
                        self.boxed_locals.add(decl_key(d))
            for y in x.get_children():
                scan(y)
        scan(body)
        ps, pre = [], []
        for prm in params:
            nm = self.declare_local(prm)
            ty = self.jtype(prm.type, prm)
            if decl_key(prm) in self.boxed_locals:
                bt = self.box_type(prm)
                ps.append('%s __%s' % (ty, nm))
                pre.append('        %s %s = new %s(__%s);' % (bt, nm, bt.replace('<%s>' % ty, '<>'), nm))
            else:
                ps.append('%s %s' % (ty, nm))
        lines = self.stmt(body, 1)
        rt = self.jtype(c.result_type)
        out = ['    // %s:%d' % (b, c.location.line), '    static %s %s(%s)' % (rt, self.fname[key], ', '.join(ps))]
        out += [lines[0]] + pre + lines[1:]
        return out

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = jident(name)
        out = ['final class %s {' % nm]
        cp = ['    %s copy() {' % nm, '        %s c = new %s();' % (nm, nm)]
        for f in fields:
            t = canon(f.type)
            fn = self.field(f.spelling)
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    out.append('    CPtr %s = R.buf(%d);' % (fn, t.element_count))
                    cp.append('        c.%s = R.copyBuf(%s);' % (fn, fn))
                else:
                    ty = self.jtype(f.type, mode='array')
                    out.append('    %s %s = %s;' % (ty, fn, self.new_array(t)))
                    if et.kind == T.RECORD:
                        cp.append('        c.%s = R.copyRecs(%s, new %s[%s.length]);' % (fn, fn, self.rec(et), fn))
                    elif et.kind == T.CONSTANTARRAY:
                        cp.append('        c.%s = R.cloneGrid(%s);' % (fn, fn))
                    else:
                        cp.append('        c.%s = %s.clone();' % (fn, fn))
            elif t.kind == T.RECORD:
                out.append('    %s %s = new %s();' % (self.rec(t), fn, self.rec(t)))
                cp.append('        c.%s = %s.copy();' % (fn, fn))
            else:
                ty = self.jtype(f.type, f)
                if ty in REFT.values():
                    self.problems.append('ref field %s.%s' % (name, f.spelling))
                out.append('    %s %s = %s;' % (ty, fn, self.zero(f.type)))
                cp.append('        c.%s = %s;' % (fn, fn))
        cp += ['        return c;', '    }']
        return out + cp + ['}', '']

    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        self.boxed_locals = set(); self.locals = {}
        t = canon(c.type)
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        ty = self.jtype(c.type, c)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            aty = self.jtype(c.type, mode='array')
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return '    static %s %s = %s;' % (aty, name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return '    static CPtr %s = R.bufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return '    static CPtr %s = R.buf(%d);' % (name, t.element_count)
            return '    static %s %s = %s;' % (aty, name, self.new_array(t))
        if t.kind == T.RECORD:
            return '    static %s %s = new %s();' % (ty, name, ty)
        v = self.conv(self.val(init[-1]), init[-1].type, c.type).code if init else self.zero(c.type)
        if k in self.boxed_globals:
            bt = BOXT.get(ctag(c.type), 'OBox<%s>' % ty)
            return '    static %s %s = new %s(%s);' % (bt, name, bt.replace('<%s>' % ty, '<>'), v)
        return '    static %s %s = %s;' % (ty, name, v)

    def delegate_decl_auto(self, name, ft):
        ps = []
        for i, a in enumerate(ft.argument_types()):
            a = canon(a)
            cat = ptr_category(a)
            if cat == 'scalar':
                isref = self.delegate_ref.get((name, i))
                if isref is None:
                    isref = self.bound_param_mode(ft, i) == 'ref'
                e = ctag(canon(a.get_pointee()))
                ps.append((REFT[e] if isref else JT[e] + '[]') + ' a%d' % i)
            else:
                ps.append(self.jtype(a, mode='obj' if cat == 'record' else None) + ' a%d' % i)
        return 'interface %s { %s call(%s); }' % (name, self.jtype(ft.get_result()), ', '.join(ps))

    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        for f in os.listdir(outdir):
            if f.startswith('F_') and f.endswith('.java') or f in ('Types.java', 'Consts.java'):
                os.remove(os.path.join(outdir, f))
        self.delegate_ref = {}
        self.static_locals = []
        self.cur_file = None
        self.tmp = 0
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
            ty = self.jtype(d.type, d)
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                glob[b].append('    static %s %s = %s;' % (self.jtype(d.type, mode='array'), name, self.init_list(strip(init[-1]), t).code))
            elif ctag(t) == 'c' and t.kind == T.CONSTANTARRAY:
                if init:
                    glob[b].append('    static CPtr %s = R.bufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count))
                else:
                    glob[b].append('    static CPtr %s = R.buf(%d);' % (name, t.element_count))
            elif t.kind == T.CONSTANTARRAY:
                glob[b].append('    static %s %s = %s;' % (self.jtype(d.type, mode='array'), name, self.new_array(t)))
            elif init:
                glob[b].append('    static %s %s = %s;' % (ty, name, self.conv(self.val(init[-1]), init[-1].type, d.type).code))
            else:
                glob[b].append('    static %s %s = %s;' % (ty, name, self.zero(d.type)))
        names = sorted(set(files) | set(glob))
        imports = ['import static swmm5.Consts.*;', 'import static swmm5.Overrides.*;'] + \
                  ['import static swmm5.%s.*;' % fclass(b) for b in names]
        for b in names:
            lines = ['// Generated from EPA SWMM 5.2.4 (%s) by tools/c2x/emit_java.py. Do not edit by hand;' % b,
                     '// fix the translator, R.java or Overrides.java instead.',
                     'package swmm5;', ''] + imports + ['', '@SuppressWarnings("all")', 'final class %s {' % fclass(b)]
            lines += glob.get(b, [])
            if glob.get(b):
                lines.append('')
            lines += files.get(b, [])
            lines += ['}']
            open(os.path.join(outdir, fclass(b) + '.java'), 'w').write('\n'.join(lines) + '\n')
        out = ['// Generated by tools/c2x/emit_java.py from EPA SWMM 5.2.4 headers.', 'package swmm5;', '']
        out += ['import static swmm5.Consts.*;'] + ['import static swmm5.%s.*;' % fclass(b) for b in names] + ['']
        for name, c in self.F.records.items():
            out += ['@SuppressWarnings("all")'] + self.record(name, c)
        for sig, (name, ft) in self.delegates.items():
            out.append(self.delegate_decl_auto(name, ft))
        open(os.path.join(outdir, 'Types.java'), 'w').write('\n'.join(out) + '\n')
        out = ['// Generated by tools/c2x/emit_java.py from EPA SWMM 5.2.4 headers and string literals.', 'package swmm5;', '',
               '@SuppressWarnings("all")', 'final class Consts {']
        for n, v in self.F.enum_consts.items():
            out.append('    static final int %s = %d;' % (jident(n), v))
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, s) in m.items():
                if n in self.macro_global and n not in done and kind in ('int', 'float') and n not in self.F.enum_consts:
                    done.add(n)
                    if kind == 'int':
                        v = re.sub(r'[uUlL]+$', '', s)
                        if len(v) > 1 and v.startswith('0'):
                            v = str(int(v, 8))
                        out.append('    static final int %s = %s;' % (jident(n), v))
                    else:
                        out.append('    static final double %s = %s;' % (jident(n), self.cs_float(s, 'd')))
        for bts, name in self.lits.items():
            out.append('    static final CPtr %s = R.lit(%s);' % (name, java_string(bts)))
        out.append('}')
        open(os.path.join(outdir, 'Consts.java'), 'w').write('\n'.join(out) + '\n')
        return self.problems


import emit_ts
JavaEmitter._find_boxed_globals = emit_ts.TSEmitter._find_boxed_globals


if __name__ == '__main__':
    F = front.Front()
    em = JavaEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_java')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
