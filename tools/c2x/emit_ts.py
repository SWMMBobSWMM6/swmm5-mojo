"""
emit_ts.py - EPA SWMM 5.2.4 C  ->  TypeScript (one module, ts/src/engine.ts), run under Node.

Statement syntax is C-like, so statements follow the C# back end (JavaScript's switch falls through
like C's, so no goto is needed). Values follow the Python back end's model, because JavaScript, like
Python, has no pointers, no ref parameters and no value structs:
  int                      -> number kept an exact int32 where C wraps or truncates: Math.imul, (a / b) | 0,
                              (a % b) | 0, unary minus as (0 - x) (JavaScript would give -0 for -0)
  unsigned                 -> number in [0, 2^32): results >>> 0      long / size_t -> number (values < 2^53)
  double                   -> number              float -> Math.fround after every float-typed operation
  double/float -> int      -> R.D2I / R.D2L  (x86-64 cvttsd2si: NaN or out of range -> INT_MIN)
  exp log log10 pow sin cos tan asin acos atan -> M.* : bit-exact ports of glibc 2.39's FMA variants
  char* / char[]           -> CPtr (Uint8Array + offset); p[i] -> p.g(i) (signed), p[i] = v -> p.s(i, v)
  numeric T* / T[]         -> Float64Array / Int32Array / Uint32Array / Float32Array
  scalar pointer params    -> R.Box / R.ElemRef / R.FieldRef objects with .v; locals whose address is
                              taken are boxed
  struct                   -> class with clone() = C value copy
Local declarations are hoisted to the top of each function (C lets a switch jump past a declaration;
JavaScript's let would throw there), and run as assignments where C declares them.
Written by Claude (Anthropic); see AI-USE.md.
"""
import os, re, sys, collections, struct
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import CSEmitter, Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null

JS_RESERVED = set('''break case catch class const continue debugger default delete do else enum export extends false
finally for function if import in instanceof new null return super switch this throw true try typeof var void while
with yield let static implements interface package private protected public await arguments eval undefined NaN
Infinity Math Number String Object Array Boolean Symbol Error Date JSON Map Set Function Float64Array Float32Array
Int32Array Uint32Array Uint8Array BigInt Promise Reflect Proxy RegExp require exports module process console global
globalThis Buffer type any number string boolean declare namespace abstract as async from get set of readonly
keyof infer is never unknown object symbol bigint constructor prototype R M CPtr CFile Box'''.split())

TYPED = {'d': 'Float64Array', 'f': 'Float32Array', 'i': 'Int32Array', 'u': 'Uint32Array', 'l': 'Float64Array',
         'ul': 'Float64Array'}

MATH = {'fabs': 'Math.abs', 'sqrt': 'Math.sqrt', 'floor': 'Math.floor', 'ceil': 'Math.ceil',
        'exp': 'M.exp', 'log': 'M.log', 'log10': 'M.log10', 'sin': 'M.sin', 'cos': 'M.cos', 'tan': 'M.tan',
        'asin': 'M.asin', 'acos': 'M.acos', 'atan': 'M.atan'}


def jsident(n):
    return n + '_' if n in JS_RESERVED else n


def js_string(b):
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


class TSEmitter(CSEmitter):
    def __init__(self, F):
        super().__init__(F)
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        self.fname = {}
        for (b, n), c in F.funcs.items():
            self.fname[(b, n)] = jsident(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.gname = {}
        for k, c in F.globals.items():
            n = c.spelling
            b = F.global_owner[k]
            self.gname[k] = jsident(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.boxed_globals = set()
        self._find_boxed_globals()

    def _find_boxed_globals(self):
        """global scalars and pointers whose address is taken (&G) live in a Box"""
        taken = set()

        def walk(c):
            if c.location.file is not None and not self.F.in_src(c):
                return
            if c.kind == K.UNARY_OPERATOR and unop(c) == '&':
                o = strip(kids(c)[0])
                if o.kind == K.DECL_REF_EXPR and o.referenced is not None and o.referenced.kind in (K.VAR_DECL, K.PARM_DECL):
                    if ctag(o.referenced.type) in NUMTAGS or canon(o.referenced.type).kind == T.POINTER:
                        taken.add(decl_key(o.referenced))
            for ch in c.get_children():
                walk(ch)
        for b, tu in self.F.tus.items():
            walk(tu.cursor)
        self.addr_taken = taken
        for k in self.F.globals:
            if k in taken:
                self.boxed_globals.add(k)

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
        return jsident(d.spelling)

    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = 'L%d' % len(self.lits)
        return self.lits[b]

    def macro_name(self, n):
        for b, m in self.F.macros.items():
            if n in m and m[n][0] in ('int', 'float') and n in self.macro_global:
                return jsident(n)
        return None

    def static_local_name(self, d):
        return jsident('%s_%s' % (d.semantic_parent.spelling, d.spelling))

    def local_name(self, d):
        return self.locals.get(decl_key(d), jsident(d.spelling))

    def declare_local(self, d, hoist=True):
        n = d.spelling
        nn = n
        if n in self.used_names:
            i = 2
            while '%s_%d' % (n, i) in self.used_names:
                i += 1
            nn = '%s_%d' % (n, i)
        self.used_names.add(nn)
        nm = jsident(nn)
        self.locals[decl_key(d)] = nm
        if hoist:
            self.hoisted[nm] = self.hoist_decl(d)
        return nm

    # ================================================================== types
    def rec(self, t):
        return jsident(record_name(t))

    def ts_type(self, t, decl=None, mode=None):
        t = canon(t)
        tg = ctag(t)
        if tg in NUMTAGS:
            return 'number'
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
        if cat in ('void', 'func'):
            return 'any'
        e = canon(t.element_type if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) else t.get_pointee())
        if cat == 'record':
            if t.kind != T.POINTER or mode == 'array':
                return self.rec(e) + '[]'
            return self.rec(e)
        if cat == 'scalar':
            if mode == 'ref' and t.kind == T.POINTER:
                return 'R.Ref'
            return TYPED.get(ctag(e), 'any')
        return 'any'

    def hoist_decl(self, d):
        """(type, initial value) for a local hoisted to the top of its function"""
        if decl_key(d) in self.boxed_locals:
            return ('R.Box', 'null')
        ty = self.ts_type(d.type, d)
        tg = ctag(d.type)
        if tg in NUMTAGS:
            return ('number', '0')
        return (ty, 'null')

    def zero(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0', 'l': '0', 'ul': '0', 'd': '0.0', 'f': '0.0'}.get(tg, 'null')

    # ================================================================== conversions
    def to_ctype(self, e, t):
        want = ctag(t)
        if e.tag in ('b', 'L') and want in NUMTAGS:
            return Ex('(%s ? 1 : 0)' % e.code, want)
        return e

    def as_bool(self, e):
        if e.tag in ('b', 'L'):
            return e.code
        if e.tag in NUMTAGS:
            return '(%s !== 0)' % e.code
        return '(%s !== null)' % e.code

    def conv(self, e, src_t, dst_t):
        s, d = ctag(src_t), ctag(dst_t)
        if e.tag in ('b', 'L') and d in NUMTAGS:
            e = Ex('(%s ? 1 : 0)' % e.code, 'i'); s = 'i'
        if s == d or d in ('v', '?', 'rec'):
            return Ex(e.code, d if d != '?' else e.tag)
        if d == 'i':
            if s in ('d', 'f'):
                return Ex('R.D2I(%s)' % e.code, 'i')
            if s in ('l', 'u', 'ul'):
                return Ex('(%s | 0)' % e.code, 'i')
            return Ex(e.code, 'i')
        if d == 'l':
            if s in ('d', 'f'):
                return Ex('R.D2L(%s)' % e.code, 'l')
            return Ex(e.code, 'l')
        if d == 'u':
            if s in ('d', 'f'):
                return Ex('(R.D2L(%s) >>> 0)' % e.code, 'u')
            return Ex('(%s >>> 0)' % e.code, 'u')
        if d == 'ul':
            if s in ('d', 'f'):
                return Ex('R.toUL(R.D2L(%s))' % e.code, 'ul')
            if s in ('i', 'l'):
                return Ex('R.toUL(%s)' % e.code, 'ul')
            return Ex(e.code, 'ul')
        if d == 'd':
            return Ex(e.code, 'd')
        if d == 'f':
            return Ex('Math.fround(%s)' % e.code, 'f')
        if d in ('c', 'o'):
            if is_null(e.code) or e.code == 'null' or e.tag == 'n' or (e.tag in ('i', 'l') and e.code == '0'):
                return Ex('null', d)
            return Ex(e.code, d)
        return e

    # ================================================================== leaves
    def x_INTEGER_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'\d+[uUlL]*', toks[0]):
            s = re.sub(r'[uUlL]+$', '', toks[0])
            if len(s) > 1 and s.startswith('0'):
                s = str(int(s, 8))
            return Ex(s, tg)
        if len(toks) == 1 and self.macro_name(toks[0]):
            return Ex(self.macro_name(toks[0]), tg)
        v = evaluate(c)
        return Ex(str(v[1]) if v else '0', tg)

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
        return Ex(repr(x) if x == x and abs(x) != float('inf') else ('Infinity' if x > 0 else '-Infinity'), tg)

    def x_CHARACTER_LITERAL(self, c):
        v = evaluate(c)
        return Ex(str(v[1] if v else 0), 'i')

    def x_STRING_LITERAL(self, c):
        return Ex(self.lit(self.string_bytes(c)), 'c')

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return Ex(jsident(c.spelling), '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return Ex(str(d.enum_value), 'i')
            return Ex(jsident(d.spelling), 'i')
        if d.kind == K.FUNCTION_DECL:
            n = self.func_ref(d, self.cur_file)
            if n is None:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex(jsident(d.spelling), 'o')
            return Ex(n, 'o')
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
        return Ex(jsident(c.spelling), ctag(c.type))

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                return Ex(self.zero(c.type), ctag(c.type))
            return self.ex(ch[0])
        e = self.ex(ch[0])
        if canon(c.type).kind == T.POINTER and e.tag in ('i', 'l') and e.code == '0':
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
        if (e.tag in ('i', 'l') and e.code == '0' and canon(c.type).kind == T.POINTER) or is_null(e.code) or e.code == 'null':
            return Ex('null', ctag(c.type))
        if ctag(c.type) == 'o' and ctag(inner.type) == 'o':
            return e
        r = self.conv(self.to_ctype(e, inner.type), inner.type, c.type)
        # narrow integer casts: (unsigned char), (char), (short), (unsigned short) truncate in C
        k = canon(c.type).kind
        if k in (T.UCHAR, T.CHAR_U):
            return Ex('(%s & 255)' % r.code, 'i')
        if k in (T.CHAR_S, T.SCHAR) and canon(inner.type).kind not in (T.CHAR_S, T.SCHAR):
            return Ex('((%s << 24) >> 24)' % r.code, 'i')
        if k == T.SHORT:
            return Ex('((%s << 16) >> 16)' % r.code, 'i')
        if k == T.USHORT:
            return Ex('(%s & 65535)' % r.code, 'i')
        return r

    def x_CXX_UNARY_EXPR(self, c):
        v = evaluate(c)
        return Ex(str(v[1]) if v else '8', 'ul')

    def x_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        return Ex('(%s)' % e.code, e.tag)

    def paren(self, s):
        if re.fullmatch(r'[\w.\[\]]+', s) or (s.startswith('(') and s.endswith(')') and self._balanced(s[1:-1])):
            return s
        return '(' + s + ')'

    # ================================================================== lvalues
    def char_lv(self, l):
        """(base, index) codes when lvalue l is a char element: p[i], *p, *(p + i)"""
        sl = strip(l)
        if sl.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sl)
            if ptr_category(base.type) == 'char':
                return self.ex(base).code, self.val(idx).code
        if sl.kind == K.UNARY_OPERATOR and unop(sl) == '*':
            a = kids(sl)[0]
            if ptr_category(a.type) == 'char':
                sa = strip(a)
                if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                    x, y = kids(sa)
                    if ptr_category(x.type) == 'char':
                        i = self.val(y).code
                        return self.ex(x).code, (i if binop(sa) == '+' else '-(%s)' % i)
                return self.ex(a).code, '0'
        return None

    def assign_code(self, l, rhs):
        """C assignment l = rhs (rhs already converted to l's type) as a JavaScript expression"""
        cl = self.char_lv(l)
        if cl:
            return '%s.s(%s, %s)' % (self.paren(cl[0]), cl[1], rhs)
        return '%s = %s' % (self.lvalue(l), rhs)

    def ref_of(self, a):
        """a reference object (.v) for lvalue a"""
        sa = strip(a)
        cl = self.char_lv(a)
        if cl:
            return 'new R.CharRef(%s, %s)' % (cl[0], cl[1])
        lv = self.lvalue(a)
        if lv.endswith('.v') and (sa.kind == K.DECL_REF_EXPR or (sa.kind == K.UNARY_OPERATOR and unop(sa) == '*')):
            return lv[:-2]
        if sa.kind == K.MEMBER_REF_EXPR:
            obj, attr = lv.rsplit('.', 1)
            return 'new R.FieldRef(%s, "%s")' % (obj, attr)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sa)
            return 'new R.ElemRef(%s, %s)' % (self.ex(base).code, self.val(idx).code)
        if sa.kind == K.DECL_REF_EXPR:
            # a static local or unboxed global: an accessor pair over the module variable
            return 'R.acc(() => %s, (__t) => { %s = __t; })' % (lv, lv)
        self.problem(a, 'reference to %s' % lv)
        return 'new R.Box(%s)' % lv

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
            if e.tag in ('i', 'l', 'ul'):
                return Ex('(0 - %s)' % self.paren(e.code), e.tag)
            if e.tag == 'u':
                return Ex('((0 - %s) >>> 0)' % self.paren(e.code), 'u')
            return Ex('-%s' % self.paren(e.code), e.tag)
        if op == '+':
            return e
        if op == '~':
            if e.tag == 'u':
                return Ex('(~%s >>> 0)' % self.paren(e.code), 'u')
            return Ex('~%s' % self.paren(e.code), e.tag)
        self.problem(c, 'unary ' + op)
        return e

    def incdec_expr(self, a, op):
        d = '+' if '++' in op else '-'
        tg = ctag(a.type)
        pre = op.startswith('pre')
        cl = self.char_lv(a)
        if cl:
            b, i = cl
            nv = '%s.s(%s, %s.g(%s) %s 1)' % (self.paren(b), i, self.paren(b), i, d)
            return Ex(nv if pre else '(%s %s 1)' % (nv, '-' if d == '+' else '+'), 'i')
        lv = self.lvalue(a)
        if tg == 'c':
            step = '1' if d == '+' else '-1'
            nv = '(%s = %s.add(%s))' % (lv, self.paren(lv), step)
            return Ex(nv if pre else '%s.add(%s)' % (nv, '-1' if d == '+' else '1'), 'c')
        if tg == 'f':
            if pre:
                return Ex('(%s = Math.fround(%s %s 1))' % (lv, lv, d), 'f')
            return Ex('R.postf(%s, %s1)' % (self.ref_of(a), d), 'f')
        if tg == 'u':
            if pre:
                return Ex('(%s = (%s %s 1) >>> 0)' % (lv, lv, d), 'u')
            return Ex('R.postu(%s, %s1)' % (self.ref_of(a), d), 'u')
        return Ex(('%s%s%s' % (d, d, lv)) if pre else ('%s%s%s' % (lv, d, d)), tg)

    def deref(self, a):
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                x, y = kids(sa)
                if ptr_category(x.type) == 'char':
                    i = self.val(y).code
                    return Ex('%s.g(%s)' % (self.paren(self.ex(x).code), i if binop(sa) == '+' else '-(%s)' % i), 'i')
            return Ex('%s.g(0)' % self.paren(self.ex(a).code), 'i')
        e = self.ex(a)
        if cat == 'record':
            return Ex(e.code, 'rec')
        mode = self.mode_of_expr(sa)
        pt = ctag(canon(a.type).get_pointee())
        if mode == 'ref':
            return Ex(e.code + '.v', pt)
        if sa.kind == K.BINARY_OPERATOR:
            l, r = kids(sa)
            return Ex('%s[%s]' % (self.ex(l).code, self.val(r).code), pt)
        return Ex('%s[0]' % self.paren(e.code), pt)

    def addr_of(self, a, c):
        sa = strip(a)
        if canon(sa.type).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return self.ex(sa)
        if ctag(sa.type) == 'rec':
            return Ex(self.ex(sa).code, 'o')
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sa)
            if ptr_category(base.type) == 'char':
                b = self.ex(base).code; i = self.val(idx).code
                return Ex(b if i == '0' else '%s.add(%s)' % (self.paren(b), i), 'c')
            if ctag(sa.type) == 'rec':
                return Ex(self.ex(sa).code, 'o')
            i = self.val(idx).code
            if i == '0':
                return Ex(self.ex(base).code, 'o')
        return Ex(self.ref_of(sa), 'ref')

    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            if ctag(l.type) == 'rec':
                return Ex('(%s)' % self.assign_code(l, '%s.clone()' % self.paren(self.ex(r).code)), 'rec')
            re_ = self.conv(self.val(r), r.type, l.type)
            return Ex('(%s)' % self.assign_code(l, re_.code), ctag(l.type))
        if op in ('&&', '||'):
            return Ex('(%s %s %s)' % (self.paren(self.cond(l)), op, self.paren(self.cond(r))), 'b')
        if op == ',':
            return Ex('(%s, %s)' % (self.val(l).code, self.val(r).code), ctag(c.type))
        lt, rt = canon(l.type), canon(r.type)
        le, re_ = self.val(l), self.val(r)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            if le.tag in ('c', 'o', 'n') or re_.tag in ('c', 'o', 'n'):
                nl = is_null(le.code) or le.code == 'null' or (le.tag in ('i', 'l') and le.code == '0')
                nr = is_null(re_.code) or re_.code == 'null' or (re_.tag in ('i', 'l') and re_.code == '0')
                if op in ('==', '!=') and (nl or nr):
                    x = le.code if not nl else re_.code
                    return Ex('(%s %s null)' % (self.paren(x), '===' if op == '==' else '!=='), 'b')
                if ptr_category(l.type) == 'char' or ptr_category(r.type) == 'char':
                    if op in ('==', '!='):
                        return Ex('%sR.peq(%s, %s)' % ('' if op == '==' else '!', le.code, re_.code), 'b')
                    return Ex('(%s.o %s %s.o)' % (self.paren(le.code), op, self.paren(re_.code)), 'b')
                return Ex('(%s %s %s)' % (le.code, '===' if op == '==' else ('!==' if op == '!=' else op), re_.code), 'b')
            jop = {'==': '===', '!=': '!=='}.get(op, op)
            return Ex('(%s %s %s)' % (le.code, jop, re_.code), 'b')
        tg = ctag(c.type)
        if tg == 'c':
            if op == '+':
                if ptr_category(l.type) == 'char':
                    return Ex('%s.add(%s)' % (self.paren(le.code), re_.code), 'c')
                return Ex('%s.add(%s)' % (self.paren(re_.code), le.code), 'c')
            return Ex('%s.add(-%s)' % (self.paren(le.code), self.paren(re_.code)), 'c')
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            return Ex('(%s.o - %s.o)' % (self.paren(le.code), self.paren(re_.code)), 'l')
        return Ex(self.arith(op, le.code, re_.code, tg, r), tg)

    def arith(self, op, a, b, tg, rnode=None):
        """a op b computed in C type tg"""
        if tg == 'f':
            return 'Math.fround(%s %s %s)' % (a, op, b)
        if tg == 'd':
            return '(%s %s %s)' % (a, op, b)
        if tg == 'i':
            if op == '*':
                return 'Math.imul(%s, %s)' % (a, b)
            if op == '/':
                return '((%s / %s) | 0)' % (a, b)
            if op == '%':
                return '((%s %% %s) | 0)' % (a, b)
            return '(%s %s %s)' % (a, op, b)
        if tg == 'u':
            if op == '*':
                return '(Math.imul(%s, %s) >>> 0)' % (a, b)
            if op == '>>':
                return '(%s >>> %s)' % (a, b)
            return '((%s %s %s) >>> 0)' % (a, op, b)
        if tg in ('l', 'ul'):
            if op == '/':
                return '(Math.trunc(%s / %s) + 0)' % (a, b)
            if op in ('*', '%'):
                return '(%s %s %s + 0)' % (a, op, b)
            if op in ('&', '|', '^', '<<', '>>'):
                self.problems.append('64-bit bitwise %s' % op)
            return '(%s %s %s)' % (a, op, b)
        return '(%s %s %s)' % (a, op, b)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        return Ex('(%s)' % self.compound_code(c), ctag(kids(c)[0].type))

    def compound_code(self, c):
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        re_ = self.val(r)
        cl = self.char_lv(l)
        if cl:
            cur = '%s.g(%s)' % (self.paren(cl[0]), cl[1])
            common = 'd' if rt == 'd' else ('f' if rt == 'f' else 'i')
            v = self.arith(op, cur, self.paren(re_.code), common)
            if common in ('d', 'f'):
                v = 'R.D2I(%s)' % v
            return '%s.s(%s, %s)' % (self.paren(cl[0]), cl[1], v)
        lv = self.lvalue(l)
        if lt == 'c':
            if op == '+':
                return '%s = %s.add(%s)' % (lv, self.paren(lv), re_.code)
            return '%s = %s.add(-%s)' % (lv, self.paren(lv), self.paren(re_.code))
        common = 'd' if 'd' in (lt, rt) else ('f' if 'f' in (lt, rt) else ('ul' if 'ul' in (lt, rt) else ('l' if 'l' in (lt, rt) else ('u' if 'u' in (lt, rt) else 'i'))))
        if common == lt and op in ('+', '-') and lt in ('d', 'i', 'l', 'ul'):
            return '%s %s= %s' % (lv, op, self.paren(re_.code))
        if common == lt == 'd' and op in ('*', '/'):
            return '%s %s= %s' % (lv, op, self.paren(re_.code))
        v = self.arith(op, lv, self.paren(re_.code), common)
        if lt in ('i', 'l', 'u', 'ul') and common in ('d', 'f'):
            v = {'i': 'R.D2I(%s)', 'l': 'R.D2L(%s)', 'u': '(R.D2L(%s) >>> 0)', 'ul': 'R.toUL(R.D2L(%s))'}[lt] % v
        elif lt == 'f' and common == 'd':
            v = 'Math.fround(%s)' % v
        elif lt == 'i' and common in ('l', 'u', 'ul'):
            v = '(%s | 0)' % v
        elif lt == 'u' and common != 'u':
            v = '(%s >>> 0)' % v
        return '%s = %s' % (lv, v)

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        ea = self.conv(self.val(a), a.type, c.type)
        eb = self.conv(self.val(b), b.type, c.type)
        return Ex('(%s ? %s : %s)' % (self.cond(cc), ea.code, eb.code), ctag(c.type))

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, idx = kids(c)
        if ptr_category(base.type) == 'char':
            return Ex('%s.g(%s)' % (self.paren(self.ex(base).code), self.val(idx).code), 'i')
        b = self.ex(base)
        i = self.val(idx)
        return Ex('%s[%s]' % (self.paren(b.code), i.code), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        b = self.ex(base)
        f = c.referenced.spelling
        return Ex('%s.%s' % (self.paren(b.code), 'constructor_' if f == 'constructor' else f), ctag(c.type))

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
                # string table with no NULL sentinel: C's findmatch() reads past the end; EPA's build
                # finds a zero word there, so the table gets the NULL the C source forgot (as in C#, Python)
                self.defects.append('%s:%d string table without NULL sentinel' % (os.path.basename(c.location.file.name), c.location.line))
                n += 1
            if ctag(t) == 'c':
                # char array initialised from a list of character constants
                vals = [self.val(it).code for it in items]
                return Ex('R.bufOf(%d, [%s])' % (n, ', '.join(vals)), 'c')
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
            if ctag(et) in NUMTAGS:
                return Ex('new %s([%s])' % (TYPED[ctag(et)], ', '.join(vals)), 'o')
            return Ex('[%s]' % ', '.join(vals), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                if strip(it).kind == K.INIT_LIST_EXPR:
                    parts.append('%s: %s' % (f.spelling, self.init_list(strip(it), f.type).code))
                else:
                    parts.append('%s: %s' % (f.spelling, self.conv(self.val(it), it.type, f.type).code))
            return Ex('Object.assign(new %s(), { %s })' % (self.rec(t), ', '.join(parts)), 'rec')
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
            for i, (a, p) in enumerate(zip(args, params)):
                sa = strip(a)
                if (ptr_category(p.type) == 'scalar' and self.P.mode_of(p) == 'array' and sa.kind == K.UNARY_OPERATOR
                        and unop(sa) == '&' and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    # &x passed where the callee indexes an array: a one-element array, copied back
                    codes = [self.arg(x, q) if j != i else '__a' for j, (x, q) in enumerate(zip(args, params))]
                    pt = canon(p.type)
                    et = TYPED[ctag(pt.get_pointee() if pt.kind == T.POINTER else pt.element_type)]
                    return Ex('R.arr1(%s, %s, (__a) => %s(%s))' % (self.ref_of(kids(sa)[0]), et, n, ', '.join(codes)), ctag(c.type))
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    codes = [self.arg(x, q) if j != i else '__c' for j, (x, q) in enumerate(zip(args, params))]
                    return Ex('R.chr1(%s, (__c) => %s(%s))' % (self.ref_of(kids(sa)[0]), n, ', '.join(codes)), ctag(c.type))
            return Ex('%s(%s)' % (n, ', '.join(self.arg(a, p) for a, p in zip(args, params))), ctag(c.type))
        fe = self.ex(callee)
        argcodes = []
        for a in args:
            sa = strip(a)
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and ctag(strip(kids(sa)[0]).type) in NUMTAGS:
                argcodes.append(self.ref_of(kids(sa)[0]))
            else:
                argcodes.append(self.val(a).code)
        return Ex('%s(%s)' % (self.paren(fe.code), ', '.join(argcodes)), ctag(c.type))

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
            if is_null(e.code) or e.code == 'null' or (e.tag in ('i', 'l') and e.code == '0'):
                return 'null'
            return 'new R.ElemRef(%s, 0)' % e.code
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
        if cat == 'char' and is_null(e.code):
            return 'null'
        return e.code

    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name in MATH:
            return Ex('%s(%s)' % (MATH[name], A(0)), 'd')
        if name == 'pow':
            return Ex('M.pow(%s, %s)' % (A(0), A(1)), 'd')
        if name in ('fprintf', 'snprintf', 'sscanf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}[name]
            head = [A(i) for i in range(fixed)]
            rest = [self.vararg(a, name == 'sscanf') for a in args[fixed:]]
            return Ex('R.%s(%s)' % (name, ', '.join(head + rest)), 'i')
        if name == 'free':
            return Ex('void 0', 'v')
        if name in ('calloc', 'malloc', 'realloc'):
            return self.alloc(c, c.type)
        if name in ('fwrite', 'fread'):
            return self.freadwrite(c, name, args)
        if name == 'memset':
            dst = strip(args[0])
            if dst.kind == K.UNARY_OPERATOR and unop(dst) == '&' and ctag(strip(kids(dst)[0]).type) == 'rec':
                o = strip(kids(dst)[0])
                return Ex('(%s = new %s())' % (self.lvalue(o), self.rec(o.type)), 'v')
            return Ex('R.memset(%s, %s, %s)' % (A(0), A(1), A(2)), 'v')
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return Ex('R.strtod(%s, %s)' % (A(0), self.ref_of(kids(ep)[0])), 'd')
            return Ex('R.strtod(%s, null)' % A(0), 'd')
        if name == 'time':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                return Ex('(%s = R.time())' % self.lvalue(kids(a0)[0]), 'l')
            return Ex('R.time()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('R.ctime(%s)' % (self.ex(kids(a0)[0]).code if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('(%s - %s)' % (A(0), A(1)), 'd')
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
                cl = self.char_lv(o)
                t = ctag(strip(o).type)
                return '["%s", %s]' % ({'i': 'i', 'd': 'd', 'f': 'f', 'l': 'l', 'u': 'i', 'ul': 'l'}.get(t, 'i'), self.ref_of(o))
            if ptr_category(sa.type) == 'scalar':
                t = ctag(canon(sa.type).get_pointee())
                if t in NUMTAGS:
                    return '["%s", %s]' % ({'u': 'i', 'ul': 'l'}.get(t, t), self.val(a).code)
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
                return Ex('R.reallocBuf(%s, %s)' % (old, n), 'c')
            if et.kind == T.RECORD:
                return Ex('R.reallocArr(%s, %s, () => new %s())' % (old, n, self.rec(et)), 'o')
            if ctag(et) in NUMTAGS:
                return Ex('R.reallocTyped(%s, %s, %s)' % (old, n, TYPED[ctag(et)]), 'o')
            return Ex('R.reallocArr(%s, %s, () => null)' % (old, n), 'o')
        if ctag(t) == 'c':
            return Ex('R.buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('new %s()' % self.rec(et), 'o')
            return Ex('R.recs(%s, () => new %s())' % (n, self.rec(et)), 'o')
        if et.kind == T.POINTER:
            return Ex('R.nulls(%s)' % n, 'o')
        if ctag(et) in NUMTAGS:
            return Ex('new %s(%s)' % (TYPED[ctag(et)], n), 'o')
        self.problem(call, 'alloc of %s' % et.spelling)
        return Ex('null', 'o')

    def count_expr(self, a, b, et, mul):
        r = CSEmitter.count_expr(self, a, b, et, mul)
        if '/' in r:
            return 'Math.trunc(%s)' % r
        return r

    def int_code(self, x):
        return self.val(x).code

    def freadwrite(self, c, name, args):
        buf, size, cnt, f = args
        sb = strip(buf)
        sz = evaluate(strip(size))
        sz = sz[1] if sz else 8
        fc = self.val(f).code
        if sb.kind == K.UNARY_OPERATOR and unop(sb) == '&':
            o = strip(kids(sb)[0])
            et = canon(o.type)
            if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                base, idx = kids(o)
                return Ex('R.%s_arr("%s", %d, %s, %s, %s, %s)' % (name, self.code_of(et), sz, self.ex(base).code, self.val(idx).code, self.val(cnt).code, fc), 'ul')
            if name == 'fwrite':
                return Ex('R.fwrite1("%s", %d, %s, %s)' % (self.code_of(et), sz, self.ex(o).code, fc), 'ul')
            return Ex('R.fread1("%s", %d, %s, %s)' % (self.code_of(et), sz, self.ref_of(o), fc), 'ul')
        if self.mode_of_expr(sb) == 'ref':
            et = canon(canon(sb.type).get_pointee())
            if name == 'fwrite':
                return Ex('R.fwrite1("%s", %d, %s.v, %s)' % (self.code_of(et), sz, self.ex(sb).code, fc), 'ul')
            return Ex('R.fread1("%s", %d, %s, %s)' % (self.code_of(et), sz, self.ex(sb).code, fc), 'ul')
        bt = canon(sb.type)
        et = canon(bt.get_pointee()) if bt.kind == T.POINTER else canon(bt.element_type)
        return Ex('R.%s_arr("%s", %d, %s, 0, %s, %s)' % (name, self.code_of(et), sz, self.ex(sb).code, self.val(cnt).code, fc), 'ul')

    def code_of(self, et):
        return {T.DOUBLE: 'd', T.FLOAT: 'f', T.INT: 'i', T.LONG: 'q', T.CHAR_S: 'c', T.SCHAR: 'c', T.UINT: 'I', T.ENUM: 'i'}.get(canon(et).kind, '?')

    # ================================================================== statements
    def stmt(self, c, ind):
        k = c.kind
        p = '  ' * ind
        if k == K.COMPOUND_STMT:
            out = [p + '{']
            for ch in kids(c):
                out += self.stmt(ch, ind + 1)
            out.append(p + '}')
            return out
        if k == K.DECL_STMT:
            out = []
            for d in kids(c):
                out += self.local_decl(d, ind)
            return out
        if k == K.IF_STMT:
            ch = kids(c)
            out = [p + 'if (%s)' % self.cond(ch[0])]
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
            return [p + 'while (%s)' % self.cond(ch[0])] + self.block(ch[1], ind)
        if k == K.DO_STMT:
            ch = kids(c)
            return [p + 'do'] + self.block(ch[0], ind) + [p + 'while (%s);' % self.cond(ch[1])]
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
            if ctag(self.cur_ret) == 'rec':
                return [p + 'return %s.clone();' % self.paren(self.ex(ch[0]).code)]
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            return [p + 'return %s;' % e.code]
        if k == K.NULL_STMT:
            return [p + ';']
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unhandled statement %s' % k.name)
            return []
        return [p + self.expr_stmt_code(c) + ';']

    def block(self, c, ind):
        if c.kind == K.COMPOUND_STMT:
            return self.stmt(c, ind)
        return ['  ' * ind + '{'] + self.stmt(c, ind + 1) + ['  ' * ind + '}']

    def expr_stmt_code(self, c):
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) == 'v':
            return self.expr_stmt_code(kids(s)[-1])
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            if ctag(l.type) == 'rec':
                return self.assign_code(l, '%s.clone()' % self.paren(self.ex(r).code))
            return self.assign_code(l, self.conv(self.val(r), r.type, l.type).code)
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmt_code(l) + ', ' + self.expr_stmt_code(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            return self.compound_code(s)
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            d = '+' if '++' in unop(s) else '-'
            cl = self.char_lv(a)
            if cl:
                return '%s.s(%s, %s.g(%s) %s 1)' % (self.paren(cl[0]), cl[1], self.paren(cl[0]), cl[1], d)
            lv = self.lvalue(a)
            tg = ctag(a.type)
            if tg == 'f':
                return '%s = Math.fround(%s %s 1)' % (lv, lv, d)
            if tg == 'c':
                return '%s = %s.add(%s1)' % (lv, self.paren(lv), '' if d == '+' else '-')
            if tg == 'u':
                return '%s = (%s %s 1) >>> 0' % (lv, lv, d)
            return '%s%s%s' % (lv, d, d)
        e = self.ex(c)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        if code in ('void 0', ''):
            return 'void 0'
        return code

    def for_stmt(self, c, ind):
        p = '  ' * ind
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
                    pre += self.local_decl(d, ind)
            else:
                init_s = self.expr_stmt_code(init)
        cond_s = self.cond(cond) if cond is not None else ''
        inc_s = self.expr_stmt_code(inc) if inc is not None else ''
        return pre + [p + 'for (%s; %s; %s)' % (init_s, cond_s, inc_s)] + self.block(body, ind)

    def switch(self, c, ind):
        p = '  ' * ind
        ch = kids(c)
        e = self.val(ch[0])
        body = ch[-1]
        items = kids(body) if body.kind == K.COMPOUND_STMT else [body]
        out = [p + 'switch (%s) {' % (e.code if e.tag != 'b' else '(%s ? 1 : 0)' % e.code)]
        for it in items:
            out += self.switch_item(it, ind + 1)
        out.append(p + '}')
        return out

    def switch_item(self, it, ind):
        p = '  ' * ind
        out = []
        x = it
        while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
            xc = kids(x)
            if x.kind == K.CASE_STMT:
                out.append(p + 'case %s:' % self.val(xc[0]).code)
                x = xc[1]
            else:
                out.append(p + 'default:')
                x = xc[0]
        out += self.stmt(x, ind + 1)
        return out

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
                return [p + '%s = %s;' % (name, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return [p + '%s = R.bufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return [p + '%s = R.buf(%d);' % (name, t.element_count)]
            return [p + '%s = %s;' % (name, self.new_array(t))]
        if ctag(t) == 'rec':
            if init:
                return [p + '%s = %s.clone();' % (name, self.paren(self.ex(init[-1]).code))]
            return [p + '%s = new %s();' % (name, self.rec(t))]
        v = self.conv(self.val(init[-1]), init[-1].type, d.type).code if init else self.zero(d.type)
        if boxed:
            return [p + '%s = new R.Box(%s);' % (name, v)]
        return [p + '%s = %s;' % (name, v)]

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return 'R.recs(%d, () => new %s())' % (n, self.rec(et))
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return 'R.bufs(%d, %d)' % (n, et.element_count)
        if et.kind == T.CONSTANTARRAY:
            return 'R.grid(%d, () => %s)' % (n, self.new_array(et))
        if et.kind == T.POINTER:
            return 'R.nulls(%d)' % n
        if ctag(et) in NUMTAGS:
            return 'new %s(%d)' % (TYPED[ctag(et)], n)
        self.problem(t.get_declaration(), 'array of %s' % et.spelling)
        return 'R.nulls(%d)' % n

    # ================================================================== functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.hoisted = collections.OrderedDict()
        self.cur_ret = c.result_type
        self.boxed_locals = set()
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
            nm = self.declare_local(prm, hoist=False)
            ty = self.ts_type(prm.type, prm)
            if decl_key(prm) in self.boxed_locals:
                ps.append('__%s: %s' % (nm, ty))
                pre.append('  const %s = new R.Box(__%s);' % (nm, nm))
            else:
                ps.append('%s: %s' % (nm, ty))
        lines = self.stmt(body, 0)
        assert lines[0] == '{' and lines[-1] == '}'
        rt = self.ts_type(c.result_type)
        if ctag(c.result_type) == 'o':
            rt = 'any'
        out = ['// %s:%d' % (b, c.location.line), 'export function %s(%s): %s {' % (self.fname[key], ', '.join(ps), rt)]
        if self.hoisted:
            out.append('  let ' + ', '.join('%s: %s = %s' % (v, ty, z) for v, (ty, z) in self.hoisted.items()) + ';')
        out += pre
        out += lines[1:-1]
        out.append('}')
        return out

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = jsident(name)
        out = ['export class %s {' % nm]
        clone = ['  clone(): %s {' % nm, '    const c = new %s();' % nm]
        for f in fields:
            t = canon(f.type)
            fn = 'constructor_' if f.spelling == 'constructor' else f.spelling
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    out.append('  %s: CPtr = R.buf(%d);' % (fn, t.element_count))
                    clone.append('    c.%s = R.copyBuf(this.%s);' % (fn, fn))
                else:
                    ty = TYPED[ctag(et)] if ctag(et) in NUMTAGS else 'any'
                    out.append('  %s: %s = %s;' % (fn, ty, self.new_array(t)))
                    if et.kind == T.RECORD:
                        clone.append('    c.%s = this.%s.map((x) => x.clone());' % (fn, fn))
                    elif et.kind == T.CONSTANTARRAY:
                        clone.append('    c.%s = R.cloneGrid(this.%s);' % (fn, fn))
                    else:
                        clone.append('    c.%s = this.%s.slice();' % (fn, fn))
            elif t.kind == T.RECORD:
                out.append('  %s: %s = new %s();' % (fn, self.rec(t), self.rec(t)))
                clone.append('    c.%s = this.%s.clone();' % (fn, fn))
            else:
                ty = self.ts_type(f.type, f)
                if ty == 'R.Ref':
                    ty = 'any'
                out.append('  %s: %s = %s;' % (fn, ty, self.zero(f.type)))
                clone.append('    c.%s = this.%s;' % (fn, fn))
        clone += ['    return c;', '  }']
        return out + clone + ['}', '']

    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        self.boxed_locals = set(); self.locals = {}
        t = canon(c.type)
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        ty = self.ts_type(c.type, c)
        if ty == 'R.Ref':
            ty = 'any'
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return 'let %s: any = %s;' % (name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return 'let %s: CPtr = R.bufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return 'let %s: CPtr = R.buf(%d);' % (name, t.element_count)
            return 'let %s: any = %s;' % (name, self.new_array(t))
        if t.kind == T.RECORD:
            return 'let %s: %s = new %s();' % (name, ty, ty)
        v = self.conv(self.val(init[-1]), init[-1].type, c.type).code if init else self.zero(c.type)
        if k in self.boxed_globals:
            return 'let %s: R.Box = new R.Box(%s);' % (name, v)
        return 'let %s: %s = %s;' % (name, ty, v)

    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        self.static_locals = []
        self.cur_file = None
        self.boxed_locals = set(); self.locals = {}
        self.hoisted = collections.OrderedDict(); self.used_names = set()
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
            t = canon(d.type)
            init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
            name = self.static_local_name(d)
            ty = self.ts_type(d.type, d)
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                glob.append('let %s: any = %s;' % (name, self.init_list(strip(init[-1]), t).code))
            elif ctag(t) == 'c' and t.kind == T.CONSTANTARRAY:
                if init:
                    glob.append('let %s: CPtr = R.bufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count))
                else:
                    glob.append('let %s: CPtr = R.buf(%d);' % (name, t.element_count))
            elif t.kind == T.CONSTANTARRAY:
                glob.append('let %s: any = %s;' % (name, self.new_array(t)))
            elif init:
                glob.append('let %s: %s = %s;' % (name, ty, self.conv(self.val(init[-1]), init[-1].type, d.type).code))
            else:
                glob.append('let %s: %s = %s;' % (name, ty, self.zero(d.type)))
        out = ['// Generated from EPA SWMM 5.2.4 by tools/c2x/emit_ts.py. Do not edit by hand;',
               '// fix the translator, crt.ts or overrides.ts instead.',
               '/* eslint-disable */',
               'import * as R from "./crt";',
               'import { CPtr, CFile } from "./crt";',
               'import * as M from "./glibm";',
               'import { sstrncpy, sstrcat, getAbsolutePath, getTempFileName, project_createMatrix, project_freeMatrix,',
               '         odesolve_open, odesolve_close, odesolve_integrate, AllocInit, Alloc, AllocSetPool, AllocReset,',
               '         AllocFreePool } from "./overrides";',
               '']
        for n, v in self.F.enum_consts.items():
            out.append('export const %s = %d;' % (jsident(n), v))
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, s) in m.items():
                if n in self.macro_global and n not in done and kind in ('int', 'float') and n not in self.F.enum_consts:
                    done.add(n)
                    v = re.sub(r'[uUlL]+$', '', s) if kind == 'int' else s.rstrip('fFlL')
                    if v.startswith('.'):
                        v = '0' + v
                    elif v.startswith('-.'):
                        v = '-0' + v[1:]
                    v = re.sub(r'\.([eE])', r'.0\1', v)
                    if v.endswith('.'):
                        v += '0'
                    if kind == 'int' and len(v) > 1 and v.startswith('0'):
                        v = str(int(v, 8))
                    out.append('export const %s = %s;' % (jsident(n), v))
        out.append('')
        for bts, name in self.lits.items():
            out.append('const %s = R.lit(%s);' % (name, js_string(bts)))
        out.append('')
        for name, c in self.F.records.items():
            out += self.record(name, c)
        out += glob + ['']
        out += funcs
        open(os.path.join(outdir, 'engine.ts'), 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = TSEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_ts')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
