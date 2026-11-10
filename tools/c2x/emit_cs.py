"""
emit_cs.py - EPA SWMM 5.2.4 C  ->  C# (one static partial class `S` per C file, records as classes)

Mapping rules (see README in the swmm5-csharp repo):
  int/long/unsigned/double/float -> int/long/uint/double/float ; char scalars -> int
  char* / char[]                 -> CPtr   (byte buffer + offset, exact C string semantics)
  struct/union                   -> class  (embedded structs and fixed arrays owned, Clone() = C value copy)
  T* indexed                     -> T[]    ; T* used with -> only -> T (object reference)
  scalar* dereferenced           -> ref T  (parameters only; the analysis found no stored scalar pointers)
  FILE*                          -> CFile  ; function pointers -> generated delegates ; void* -> object
  double->int conversions        -> R.D2I  (x86 cvttsd2si semantics: NaN/out of range -> int.MinValue)
"""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key

CS_KEYWORDS = set('''abstract as base bool break byte case catch char checked class const continue decimal default delegate
do double else enum event explicit extern false finally fixed float for foreach goto if implicit in int interface internal is
lock long namespace new null object operator out override params private protected public readonly ref return sbyte sealed
short sizeof stackalloc static string struct switch this throw true try typeof uint ulong unchecked unsafe ushort using
virtual void volatile while R S CPtr CFile'''.split())

# C functions replaced by hand-written runtime code (pointer tricks the mapping cannot express)
OVERRIDES = {('swmm5.c', 'sstrncpy'), ('swmm5.c', 'sstrcat'), ('swmm5.c', 'getAbsolutePath'), ('swmm5.c', 'getTempFileName'),
             ('project.c', 'project_createMatrix'), ('project.c', 'project_freeMatrix'),
             ('odesolve.c', 'odesolve_open'), ('odesolve.c', 'odesolve_close'), ('odesolve.c', 'odesolve_integrate'),
             ('odesolve.c', 'rkqs'), ('odesolve.c', 'rkck')}
SKIP_FILES = {'mempool.c', 'odesolve.c'}


RESERVED = {'S', 'R', 'CPtr', 'CFile', 'Math', 'System', 'Console', 'Program'}


def ident(n):
    if n in RESERVED:
        return n + '_'
    return '@' + n if n in CS_KEYWORDS else n


def is_null(code):
    code = code.strip()
    while code.startswith('(') and code.endswith(')'):
        code = code[1:-1].strip()
    return code in ('null', 'CPtr.Null')


class Ex:
    __slots__ = ('code', 'tag')

    def __init__(self, code, tag):
        self.code, self.tag = code, tag

    def __repr__(self):
        return 'Ex(%r,%r)' % (self.code, self.tag)


def ctag(t):
    """semantic tag of a C type"""
    t = canon(t)
    k = t.kind
    if k in (T.INT, T.ENUM, T.SHORT, T.USHORT, T.CHAR_S, T.SCHAR, T.CHAR_U, T.UCHAR, T.BOOL):
        return 'i'
    if k == T.UINT:
        return 'u'
    if k in (T.LONG, T.LONGLONG):
        return 'l'
    if k in (T.ULONG, T.ULONGLONG):
        return 'ul'
    if k == T.DOUBLE:
        return 'd'
    if k == T.FLOAT:
        return 'f'
    if k == T.VOID:
        return 'v'
    if k == T.RECORD:
        return 'rec'
    if k in (T.POINTER, T.CONSTANTARRAY, T.INCOMPLETEARRAY):
        cat = ptr_category(t)
        return 'c' if cat == 'char' else 'o'
    return '?'


NUMTAGS = ('i', 'u', 'l', 'ul', 'd', 'f')


class CSEmitter:
    def __init__(self, F):
        self.F = F
        self.P = front.PtrInfo(F)
        self.lits = collections.OrderedDict()   # bytes -> name
        self.delegates = collections.OrderedDict()  # signature -> name
        self.problems = []
        self.defects = []
        self._names()

    # ------------------------------------------------------------------ naming
    def _names(self):
        F = self.F
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        self.fname = {}
        for (b, n), c in F.funcs.items():
            static = front.is_static(c)
            self.fname[(b, n)] = ident(b[:-2] + '_' + n if (cnt[n] > 1 and static) else n)
        self.gname = {}
        for k, c in F.globals.items():
            static = front.is_static(c)
            b = self.F.global_owner[k]
            n = c.spelling
            self.gname[k] = ident(b[:-2] + '_' + n if (cnt[n] > 1 and static) else n)
        # macros: global if same value everywhere
        vals = collections.defaultdict(set)
        for b, m in F.macros.items():
            for n, v in m.items():
                vals[n].add(v)
        taken = set(cnt) | set(F.enum_consts) | set(F.records) | {c.spelling for c in F.globals.values()}
        self.macro_global = {n for n, v in vals.items() if len(v) == 1 and n not in taken and n not in RESERVED}

    def func_ref(self, d, cur_file):
        """C# name for a referenced function declaration"""
        n = d.spelling
        keys = self.F.func_by_decl.get(n)
        if not keys:
            return None
        if len(keys) == 1:
            return self.fname[keys[0]]
        for k in keys:
            if k[0] == cur_file:
                return self.fname[k]
        # non-static one
        for k in keys:
            if self.F.funcs[k].storage_class != front.ci.StorageClass.STATIC:
                return self.fname[k]
        return self.fname[keys[0]]

    def func_def(self, d, cur_file):
        n = d.spelling
        keys = self.F.func_by_decl.get(n) or []
        cand = [k for k in keys if k[0] == cur_file] or [k for k in keys if self.F.funcs[k].storage_class != front.ci.StorageClass.STATIC]
        return self.F.funcs[cand[0]] if cand else None

    def global_ref(self, d):
        k = decl_key(d)
        if k in self.gname:
            return self.gname[k]
        # extern declaration: find definition by name
        for gk, c in self.F.globals.items():
            if c.spelling == d.spelling and c.storage_class != front.ci.StorageClass.STATIC:
                return self.gname[gk]
        return ident(d.spelling)

    # ------------------------------------------------------------------ types
    def rec(self, t):
        return ident(record_name(t))

    def cs_type(self, t, decl=None, mode=None):
        t0 = t
        t = canon(t)
        tg = ctag(t)
        if tg in ('i',):
            return 'int'
        if tg == 'u':
            return 'uint'
        if tg == 'l':
            return 'long'
        if tg == 'ul':
            return 'ulong'
        if tg == 'd':
            return 'double'
        if tg == 'f':
            return 'float'
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
            return 'object'
        if cat == 'func':
            return self.delegate(t)
        e = canon(t.element_type if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) else t.get_pointee())
        if cat == 'record':
            return self.rec(e) + ('[]' if (mode in (None, 'array') and t.kind != T.POINTER) or mode == 'array' else '')
        if cat == 'scalar':
            base = self.cs_type(e)
            if mode == 'ref':
                return 'ref ' + base
            return base + '[]'
        if cat == 'ptrptr':
            inner = self.cs_type(e, mode='obj' if ptr_category(e) == 'record' else 'array')
            if mode == 'ref':
                return 'ref ' + inner
            return inner + '[]'
        return 'object /*?%s*/' % t.spelling

    def delegate(self, t):
        t = canon(t)
        ft = canon(t.get_pointee())
        sig = (ft.get_result().spelling,) + tuple(a.spelling for a in ft.argument_types())
        if sig not in self.delegates:
            self.delegates[sig] = ('FP%d' % len(self.delegates), ft)
        return self.delegates[sig][0]

    def delegate_decl(self, name, ft):
        ps = []
        for i, a in enumerate(ft.argument_types()):
            a = canon(a)
            cat = ptr_category(a)
            if cat == 'scalar':
                # callbacks: findroot passes f/df by pointer (ref); odesolve passes arrays
                ps.append(('ref ' if self.delegate_ref.get((name, i)) else '') + self.cs_type(a.get_pointee()) + ('' if self.delegate_ref.get((name, i)) else '[]') + ' a%d' % i)
            else:
                ps.append(self.cs_type(a, mode='obj' if cat == 'record' else None) + ' a%d' % i)
        return 'public delegate %s %s(%s);' % (self.cs_type(ft.get_result()), name, ', '.join(ps))

    # ------------------------------------------------------------------ literals
    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = 'L%d' % len(self.lits)
        return 'S.' + self.lits[b]

    @staticmethod
    def cs_bytes(b):
        out = []
        for ch in b:
            if ch == 0x5c:
                out.append('\\\\')
            elif ch == 0x22:
                out.append('\\"')
            elif 32 <= ch < 127:
                out.append(chr(ch))
            else:
                out.append('\\u%04x' % ch if ch not in (10, 9, 13) else {10: '\\n', 9: '\\t', 13: '\\r'}[ch])
        return '"' + ''.join(out) + '"'

    def string_bytes(self, c):
        """bytes of a string literal cursor (concatenated, escapes decoded)"""
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
        out = bytearray(); i = 0
        esc = {'n': 10, 't': 9, 'r': 13, '0': 0, '\\': 92, '"': 34, "'": 39, 'a': 7, 'b': 8, 'f': 12, 'v': 11, '?': 63}
        while i < len(s):
            ch = s[i]
            if ch == '\\':
                n = s[i + 1]
                if n == 'x':
                    m = re.match(r'[0-9a-fA-F]+', s[i + 2:]); out.append(int(m.group(0), 16) & 255); i += 2 + len(m.group(0)); continue
                if n in '01234567':
                    m = re.match(r'[0-7]{1,3}', s[i + 1:]); out.append(int(m.group(0), 8) & 255); i += 1 + len(m.group(0)); continue
                out.append(esc[n]); i += 2; continue
            out += ch.encode('latin-1'); i += 1
        return bytes(out)

    # ================================================================== expressions
    def val(self, c):
        """C value of expression c, converted from our tag to c's C type"""
        e = self.ex(c)
        return self.to_ctype(e, c.type)

    def to_ctype(self, e, t):
        want = ctag(t)
        if e.tag == 'b' and want in NUMTAGS:
            return Ex('(%s ? 1 : 0)' % e.code, want)
        return e

    def cond(self, c):
        e = self.ex(c)
        return self.as_bool(e)

    def as_bool(self, e):
        if e.tag == 'b':
            return e.code
        if e.tag in ('i', 'u', 'l', 'ul'):
            return '(%s != 0)' % e.code
        if e.tag in ('d', 'f'):
            return '(%s != 0.0)' % e.code
        if e.tag == 'c':
            return '!(%s).IsNull' % e.code
        return '(%s != null)' % e.code

    def conv(self, e, src_t, dst_t):
        """implicit/explicit C conversion src -> dst"""
        s, d = ctag(src_t), ctag(dst_t)
        if e.tag == 'b' and d in NUMTAGS:
            e = Ex('(%s ? 1 : 0)' % e.code, 'i'); s = 'i'
        if s == d or d in ('v', '?'):
            if d == 'rec':
                return e
            return Ex(e.code, d if d != '?' else e.tag)
        if d == 'i':
            if s in ('d', 'f'):
                return Ex('R.D2I(%s)' % e.code, 'i')
            if s in ('l', 'u', 'ul'):
                return Ex('(int)(%s)' % e.code, 'i')
            return Ex(e.code, 'i')
        if d == 'l':
            if s in ('d', 'f'):
                return Ex('R.D2L(%s)' % e.code, 'l')
            if s == 'ul':
                return Ex('(long)(%s)' % e.code, 'l')
            return Ex(e.code, 'l')
        if d == 'u':
            if s in ('d', 'f'):
                return Ex('(uint)R.D2L(%s)' % e.code, 'u')
            return Ex('unchecked((uint)(%s))' % e.code, 'u')
        if d == 'ul':
            if s in ('d', 'f'):
                return Ex('(ulong)R.D2L(%s)' % e.code, 'ul')
            return Ex('unchecked((ulong)(%s))' % e.code, 'ul')
        if d == 'd':
            return Ex('(double)(%s)' % e.code if s == 'ul' else e.code, 'd')
        if d == 'f':
            return Ex('(float)(%s)' % e.code, 'f')
        if d == 'c':
            if e.tag == 'n' or is_null(e.code):
                return Ex('CPtr.Null', 'c')
            return Ex(e.code, 'c')
        if d == 'o':
            if e.tag == 'n':
                return Ex('null', 'o')
            return Ex(e.code, 'o')
        return e

    def ex(self, c):
        k = c.kind
        m = getattr(self, 'x_' + k.name, None)
        if m is None:
            self.problem(c, 'unhandled expression ' + k.name)
            return Ex('/*?%s*/default' % k.name, '?')
        return m(c)

    def problem(self, c, msg):
        loc = '%s:%s' % (os.path.basename(c.location.file.name) if c.location.file else '?', c.location.line)
        self.problems.append('%s %s' % (loc, msg))

    # --- leaves
    def x_INTEGER_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'\d+[uUlL]*', toks[0]):
            s = re.sub(r'[uUlL]+$', '', toks[0])
            if tg == 'l':
                s += 'L'
            elif tg == 'u':
                s += 'U'
            elif tg == 'ul':
                s += 'UL'
            return Ex(s, tg)
        if len(toks) == 1 and self.macro_name(toks[0]):
            return Ex(self.macro_name(toks[0]), tg)
        v = evaluate(c)
        return Ex(str(v[1]) if v else '0', tg)

    def macro_name(self, n):
        for b, m in self.F.macros.items():
            if n in m and m[n][0] in ('int', 'float'):
                if n in self.macro_global:
                    return 'S.' + ident(n)
        return None

    def x_FLOATING_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?[fFlL]?', toks[0]):
            return Ex(self.cs_float(toks[0], tg), tg)
        if len(toks) == 1 and self.macro_name(toks[0]):
            return Ex(self.macro_name(toks[0]), tg)
        v = evaluate(c)
        return Ex(repr(v[1]) + ('f' if tg == 'f' else ''), tg)

    @staticmethod
    def cs_float(s, tg):
        f = s[-1] in 'fF'
        s = s.rstrip('fFlL')
        if s.startswith('.'):
            s = '0' + s
        s = re.sub(r'\.([eE])', r'.0\1', s)
        if s.endswith('.'):
            s += '0'
        if '.' not in s and 'e' not in s.lower():
            s += '.0'
        return s + ('f' if (f or tg == 'f') else '')

    def x_CHARACTER_LITERAL(self, c):
        v = evaluate(c)
        n = v[1] if v else 0
        ch = chr(n) if 32 <= n < 127 and chr(n) not in "\\'" else None
        return Ex("'%s'" % ch if ch else str(n), 'i')

    def x_STRING_LITERAL(self, c):
        return Ex(self.lit(self.string_bytes(c)), 'c')

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return Ex(ident(c.spelling), '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return Ex('%d/*%s*/' % (d.enum_value, d.spelling), 'i')
            return Ex('S.' + ident(d.spelling), 'i')
        if d.kind == K.FUNCTION_DECL:
            n = self.func_ref(d, self.cur_file)
            if n is None:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex(ident(d.spelling), 'o')
            self.func_values.add(n)
            return Ex('S.' + n, 'o')
        if d.kind == K.PARM_DECL or (d.kind == K.VAR_DECL and d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL and d.storage_class != front.ci.StorageClass.STATIC):
            return Ex(self.local_name(d), ctag(d.type))
        if d.kind == K.VAR_DECL:
            if d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL:
                return Ex('S.' + self.static_local_name(d), ctag(d.type))
            return Ex('S.' + self.global_ref(d), ctag(d.type))
        return Ex(ident(c.spelling), ctag(c.type))

    def x_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        return Ex('(%s)' % e.code, e.tag)

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                # e.g. implicit value initialisation
                return Ex(self.zero(c.type), ctag(c.type))
            self.problem(c, 'unexposed with %d children' % len(ch))
            return self.ex(ch[0])
        e = self.ex(ch[0])
        src_t = ch[0].type
        # null pointer constant
        if canon(c.type).kind == T.POINTER and e.tag in ('i',) and e.code in ('0',):
            return Ex('CPtr.Null' if ctag(c.type) == 'c' else 'null', ctag(c.type))
        return self.conv(e, src_t, c.type)

    def zero(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0U', 'l': '0L', 'ul': '0UL', 'd': '0.0', 'f': '0.0f', 'c': 'CPtr.Null'}.get(tg, 'null')

    def x_CSTYLE_CAST_EXPR(self, c):
        ch = kids(c)
        inner = ch[-1]
        if ctag(c.type) == 'v':
            return self.ex(inner)
        s = strip(inner)
        if s.kind == K.CALL_EXPR and s.spelling in ('malloc', 'calloc', 'realloc'):
            return self.alloc(s, c.type)
        e = self.ex(inner)
        if e.tag == 'n' or (e.tag == 'i' and e.code == '0' and canon(c.type).kind == T.POINTER):
            return Ex('CPtr.Null' if ctag(c.type) == 'c' else 'null', ctag(c.type))
        if ctag(c.type) == 'o' and ctag(inner.type) == 'o' and canon(c.type).kind == T.POINTER:
            # pointer casts: void* -> T*
            if ptr_category(inner.type) == 'void' and ptr_category(c.type) == 'record':
                return Ex('((%s)%s)' % (self.rec(canon(c.type).get_pointee()), e.code), 'o')
            return e
        r = self.conv(e, inner.type, c.type)
        tgt = ctag(c.type)
        if tgt in ('d',) and ctag(inner.type) in ('i', 'l', 'u'):
            return Ex('(double)(%s)' % e.code, 'd')
        if tgt == 'f' and not r.code.startswith('(float)'):
            return Ex('(float)(%s)' % e.code, 'f')
        return r

    def x_CXX_UNARY_EXPR(self, c):
        # sizeof
        toks = [t.spelling for t in c.get_tokens()]
        v = evaluate(c)
        return Ex(str(v[1]) if v else '8', 'ul')

    # --- operators
    def x_UNARY_OPERATOR(self, c):
        op = unop(c)
        a = kids(c)[0]
        if op == '&':
            return self.addr_of(a, c)
        if op == '*':
            return self.deref(a)
        if op == '!':
            return Ex('!%s' % self.paren(self.cond(a)), 'b')
        e = self.val(a)
        if op in ('pre++', 'pre--', 'post++', 'post--'):
            o = '++' if '++' in op else '--'
            if e.tag == 'c' and op.startswith('post'):
                return Ex('%s%s' % (e.code, o), 'c')
            return Ex(('%s%s' % (o, e.code)) if op.startswith('pre') else ('%s%s' % (e.code, o)), e.tag)
        if op == '-':
            return Ex('-%s' % self.paren(e.code), e.tag)
        if op == '+':
            return e
        if op == '~':
            return Ex('~%s' % self.paren(e.code), e.tag)
        self.problem(c, 'unary ' + op)
        return e

    @staticmethod
    def paren(s):
        if re.fullmatch(r'[\w.\[\]@]+', s) or (s.startswith('(') and s.endswith(')') and s.count('(') == 1):
            return s
        return '(' + s + ')'

    def deref(self, a):
        """*a"""
        e = self.ex(a)
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            return Ex('%s[0]' % self.paren(e.code), 'i')
        if cat == 'record':
            return Ex(e.code, 'rec')
        mode = self.mode_of_expr(sa)
        if mode == 'ref':
            return Ex(e.code, ctag(canon(a.type).get_pointee()))
        if sa.kind == K.BINARY_OPERATOR:
            # *(p + i)
            l, r = kids(sa)
            return Ex('%s[%s]' % (self.ex(l).code, self.val(r).code), ctag(canon(a.type).get_pointee()))
        return Ex('%s[0]' % self.paren(e.code), ctag(canon(a.type).get_pointee()))

    def mode_of_expr(self, e):
        e = strip(e)
        if e.kind in (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR) and e.referenced is not None:
            return self.P.mode_of(e.referenced)
        return None

    def addr_of(self, a, c):
        """&a as a value (arguments are handled in call())"""
        sa = strip(a)
        if canon(sa.type).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return self.ex(sa)
        if ctag(sa.type) == 'rec':
            return Ex(self.ex(sa).code, 'o')
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sa)
            if ptr_category(base.type) == 'char':
                b = self.ex(base).code; i = self.val(idx).code
                return Ex(b if i == '0' else '(%s + %s)' % (b, i), 'c')
            if ctag(sa.type) == 'rec':
                return Ex(self.ex(sa).code, 'o')
            i = self.val(idx).code
            if i == '0':
                return Ex(self.ex(base).code, 'o')
        # &scalar where a pointer value is needed: only legal as a ref argument
        return Ex('ref ' + self.ex(sa).code, 'ref')

    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            return self.assign(c, l, r)
        if op in ('&&', '||'):
            return Ex('%s %s %s' % (self.paren(self.cond(l)), op, self.paren(self.cond(r))), 'b')
        if op == ',':
            self.problem(c, 'comma operator')
            return Ex('R.Comma(%s, %s)' % (self.val(l).code, self.val(r).code), ctag(c.type))
        lt, rt = canon(l.type), canon(r.type)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            le, re_ = self.val(l), self.val(r)
            if le.tag in ('c', 'o', 'n') or re_.tag in ('c', 'o', 'n'):
                return Ex(self.ptr_compare(le, re_, op, l, r), 'b')
            return Ex('%s %s %s' % (le.code, op, re_.code), 'b')
        le, re_ = self.val(l), self.val(r)
        tg = ctag(c.type)
        if tg == 'c':
            # pointer arithmetic on char*
            return Ex('(%s %s %s)' % (le.code, op, re_.code), 'c')
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            return Ex('CPtr.Diff(%s, %s)' % (le.code, re_.code), 'l')
        code = '%s %s %s' % (le.code, op, re_.code)
        if tg in ('u', 'ul') and (le.tag != tg or re_.tag != tg) and op not in ('<<', '>>'):
            code = 'unchecked((%s)(%s))' % ('uint' if tg == 'u' else 'ulong', code)
        if tg in ('u',) and op in ('<<', '>>'):
            code = 'unchecked((uint)(%s))' % code
        if tg == 'i' and (le.tag in ('l', 'u', 'ul') or re_.tag in ('l', 'u', 'ul')):
            code = '(int)(%s)' % code
        return Ex(code, tg)

    def ptr_compare(self, le, re_, op, l, r):
        if op not in ('==', '!='):
            return '%s %s %s' % (le.code, op, re_.code)
        isc = le.tag == 'c' or re_.tag == 'c' or ptr_category(l.type) == 'char' or ptr_category(r.type) == 'char'
        nl = le.tag == 'n' or is_null(le.code)
        nr = re_.tag == 'n' or is_null(re_.code)
        if isc:
            if nr:
                return ('%s.IsNull' if op == '==' else '!%s.IsNull') % self.paren(le.code)
            if nl:
                return ('%s.IsNull' if op == '==' else '!%s.IsNull') % self.paren(re_.code)
            return '%s %s %s' % (le.code, op, re_.code)
        return '%s %s %s' % (le.code if not nl else 'null', op, re_.code if not nr else 'null')

    def assign(self, c, l, r):
        le = self.lvalue(l)
        if ctag(l.type) == 'rec':
            re_ = self.ex(r)
            return Ex('%s = %s.Clone()' % (le, re_.code), 'rec')
        re_ = self.val(r)
        re_ = self.conv(re_, r.type, l.type)
        return Ex('%s = %s' % (le, re_.code), ctag(l.type))

    def lvalue(self, l):
        e = self.ex(l)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        return code

    @staticmethod
    def _balanced(s):
        d = 0
        for ch in s:
            if ch == '(':
                d += 1
            elif ch == ')':
                d -= 1
                if d < 0:
                    return False
        return d == 0

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        le = self.lvalue(l)
        re_ = self.val(r)
        if lt == 'c':
            return Ex('%s %s %s' % (le, op, re_.code), 'c')
        implicit = {('d', 'i'), ('d', 'f'), ('d', 'l'), ('d', 'u'), ('f', 'i'), ('l', 'i'), ('l', 'u'), ('i', 'i'), ('u', 'u'),
                    ('d', 'd'), ('f', 'f'), ('l', 'l'), ('ul', 'ul'), ('ul', 'u')}
        if (lt, rt) in implicit:
            return Ex('%s %s %s' % (le, op, re_.code), lt)
        bop = op[:-1]
        inner = Ex('%s %s %s' % (le, bop, self.paren(re_.code)), rt if rt in ('d', 'f') and lt not in ('d',) else lt)
        # C: compute in the common type, convert back to the left type
        common = 'd' if 'd' in (lt, rt) else ('f' if 'f' in (lt, rt) else lt)
        src = {'d': 'double', 'f': 'float'}.get(common)
        if common in ('d', 'f') and lt in ('i', 'l', 'u', 'ul'):
            conv = {'i': 'R.D2I', 'l': 'R.D2L', 'u': '(uint)R.D2L', 'ul': '(ulong)R.D2L'}[lt]
            return Ex('%s = %s(%s)' % (le, conv, inner.code), lt)
        if lt == 'f':
            return Ex('%s = (float)(%s)' % (le, inner.code), lt)
        cast = {'i': 'int', 'u': 'uint', 'l': 'long', 'ul': 'ulong'}.get(lt, '')
        return Ex('%s = unchecked((%s)(%s))' % (le, cast, inner.code), lt)

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        ea, eb = self.val(a), self.val(b)
        tg = ctag(c.type)
        ea, eb = self.conv(ea, a.type, c.type), self.conv(eb, b.type, c.type)
        if tg == 'c':
            ea = Ex('CPtr.Null', 'c') if is_null(ea.code) else ea
            eb = Ex('CPtr.Null', 'c') if is_null(eb.code) else eb
        elif tg == 'o' and (is_null(ea.code) or is_null(eb.code)):
            ty = self.cs_type(c.type)
            if is_null(ea.code):
                ea = Ex('(%s)null' % ty, 'o')
            if is_null(eb.code):
                eb = Ex('(%s)null' % ty, 'o')
        return Ex('(%s ? %s : %s)' % (self.cond(cc), ea.code, eb.code), tg)

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, idx = kids(c)
        b = self.ex(base)
        i = self.val(idx)
        if i.tag in ('l', 'ul', 'u'):
            i = Ex('(int)(%s)' % i.code, 'i')
        tg = ctag(c.type)
        return Ex('%s[%s]' % (self.paren(b.code), i.code), tg)

    def x_MEMBER_REF_EXPR(self, c):
        ch = kids(c)
        base = ch[0]
        b = self.ex(base)
        f = c.referenced
        return Ex('%s.%s' % (self.paren(b.code), ident(f.spelling)), ctag(c.type))

    def x_INIT_LIST_EXPR(self, c):
        return self.init_list(c, c.type)

    def init_list(self, c, t):
        t = canon(t)
        items = kids(c)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            et = canon(t.element_type)
            n = t.element_count if t.kind == T.CONSTANTARRAY else len(items)
            if (canon(t.element_type).kind == T.POINTER and front.is_char(canon(t.element_type).get_pointee()) and items
                    and strip(items[-1]).kind == K.STRING_LITERAL and len(items) == n):
                # string table with no NULL sentinel: C's findmatch() reads past the end; EPA's build
                # finds a zero word there, so the C# table gets the NULL the C source forgot
                self.defects.append('%s:%d string table without NULL sentinel' % (os.path.basename(c.location.file.name), c.location.line))
                n += 1
            vals = []
            for it in items:
                if strip(it).kind == K.INIT_LIST_EXPR:
                    vals.append(self.init_list(strip(it), et).code)
                elif ctag(et) == 'c' and strip(it).kind == K.STRING_LITERAL and canon(et).kind == T.CONSTANTARRAY:
                    vals.append('R.BufFrom(%s, %d)' % (self.lit(self.string_bytes(strip(it))), canon(et).element_count))
                else:
                    vals.append(self.conv(self.val(it), it.type, et).code)
            while len(vals) < n:
                vals.append(self.zero(et) if ctag(et) != 'rec' else 'new %s()' % self.rec(et))
            if canon(et).kind == T.CONSTANTARRAY:
                return Ex('new %s[] { %s }' % (self.cs_type(et), ', '.join(vals)), 'o')
            return Ex('new %s[] { %s }' % (self.cs_type(et), ', '.join(vals)), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                parts.append('%s = %s' % (ident(f.spelling), self.conv(self.val(it), it.type, f.type).code))
            return Ex('new %s { %s }' % (self.rec(t), ', '.join(parts)), 'rec')
        if len(items) == 1:
            return self.val(items[0])
        self.problem(c, 'init list for %s' % t.spelling)
        return Ex('default', '?')

    # --- calls
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
            # &scalar passed where an array parameter is expected: run on a 1-element array and copy back
            wrap = None
            for i, (a, p) in enumerate(zip(args, params)):
                sa = strip(a)
                if (ptr_category(p.type) == 'scalar' and self.P.mode_of(p) == 'array' and sa.kind == K.UNARY_OPERATOR
                        and unop(sa) == '&' and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    wrap = i
            for i, (a, p) in enumerate(zip(args, params)):
                sa = strip(a)
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    codes = [self.arg(x, q) if j != i else '__c' for j, (x, q) in enumerate(zip(args, params))]
                    lv = self.lvalue(kids(sa)[0])
                    return Ex('R.Chr1(ref %s, __c => S.%s(%s))' % (lv, n, ', '.join(codes)), ctag(c.type))
            if wrap is not None:
                codes = [self.arg(a, p) if i != wrap else '__a' for i, (a, p) in enumerate(zip(args, params))]
                lv = self.lvalue(kids(strip(args[wrap]))[0])
                return Ex('R.Arr1(ref %s, __a => S.%s(%s))' % (lv, n, ', '.join(codes)), ctag(c.type))
            return Ex('S.%s(%s)' % (n, ', '.join(self.arg(a, p) for a, p in zip(args, params))), ctag(c.type))
        # call through a function pointer
        fe = self.ex(callee)
        ft = canon(callee.type)
        if ft.kind == T.POINTER:
            ft = canon(ft.get_pointee())
        argcodes = []
        dname = self.delegate(canon(strip(callee).type)) if canon(strip(callee).type).kind == T.POINTER else None
        for i, a in enumerate(args):
            argcodes.append(self.arg_ptr_generic(a, dname, i))
        return Ex('%s(%s)' % (self.paren(fe.code), ', '.join(argcodes)), ctag(c.type))

    def arg_ptr_generic(self, a, dname, i):
        sa = strip(a)
        if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and ctag(strip(kids(sa)[0]).type) in NUMTAGS:
            self.delegate_ref[(dname, i)] = True
            return 'ref ' + self.ex(kids(sa)[0]).code
        if ptr_category(a.type) == 'scalar' and self.mode_of_expr(sa) == 'ref':
            self.delegate_ref[(dname, i)] = True
            return 'ref ' + self.ex(sa).code
        return self.val(a).code

    def arg(self, a, p):
        """argument a passed to parameter p (definition)"""
        pmode = self.P.mode_of(p)
        cat = ptr_category(p.type)
        sa = strip(a)
        if cat == 'scalar' and pmode == 'ref' or (cat == 'ptrptr' and pmode == 'ref'):
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return 'ref ' + self.lvalue(kids(sa)[0])
            if self.mode_of_expr(sa) == 'ref':
                return 'ref ' + self.ex(sa).code
            if sa.kind == K.CSTYLE_CAST_EXPR or (sa.kind == K.INTEGER_LITERAL):
                self.problem(a, 'NULL passed to ref parameter %s' % p.spelling)
                return 'ref R.Dummy' + self.cs_type(canon(p.type).get_pointee()).capitalize()
            # array element pointer / array passed to a ref param: pass element 0
            e = self.ex(sa)
            return 'ref %s[0]' % self.paren(e.code)
        if cat == 'scalar' and pmode == 'array':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = strip(kids(sa)[0])
                if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                    base, idx = kids(o)
                    i = self.val(idx).code
                    if i != '0':
                        self.problem(a, 'array offset &x[%s] passed to array param %s' % (i, p.spelling))
                    return self.ex(base).code
        e = self.val(a)
        e = self.conv(e, a.type, p.type)
        if e.tag == 'ref':
            self.problem(a, 'address passed where %s (%s) expected' % (p.spelling, pmode))
        if cat == 'char' and is_null(e.code):
            return 'CPtr.Null'
        return e.code

    # --- C library
    MATH1 = {'fabs': 'Math.Abs', 'sqrt': 'Math.Sqrt', 'floor': 'Math.Floor', 'exp': 'Math.Exp', 'log10': 'Math.Log10',
             'sin': 'Math.Sin', 'cos': 'Math.Cos', 'acos': 'Math.Acos', 'log': 'Math.Log', 'tan': 'Math.Tan',
             'asin': 'Math.Asin', 'atan': 'Math.Atan', 'ceil': 'Math.Ceiling'}

    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name in self.MATH1:
            return Ex('%s(%s)' % (self.MATH1[name], A(0)), 'd')
        if name == 'pow':
            return Ex('Math.Pow(%s, %s)' % (A(0), A(1)), 'd')
        if name in ('fprintf', 'snprintf', 'sscanf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}[name]
            head = [A(i) for i in range(fixed)]
            rest = []
            back = []
            for a in args[fixed:]:
                sa = strip(a)
                if name == 'sscanf' and ptr_category(a.type) == 'scalar' and self.mode_of_expr(sa) == 'ref':
                    # pointer parameter: C# lambdas cannot capture ref parameters -> stash and copy back
                    rest.append('R.Slot')
                    back.append('ref ' + self.ex(sa).code)
                else:
                    rest.append(self.vararg(a, name == 'sscanf'))
            call = 'R.%s(%s)' % (name, ', '.join(head + rest))
            if back:
                call = 'R.Back(%s, %s)' % (call, ', '.join(back))
            return Ex(call, 'i')
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
                return Ex('R.strtod(%s, ref %s)' % (A(0), self.lvalue(kids(ep)[0])), 'd')
            return Ex('R.strtod(%s)' % A(0), 'd')
        if name == 'time':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                return Ex('(%s = R.time())' % self.lvalue(kids(a0)[0]), 'l')
            return Ex('R.time()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('R.ctime(%s)' % (self.ex(kids(a0)[0]).code if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('(double)(%s - %s)' % (A(0), A(1)), 'd')
        if name == 'mkstemp':
            return Ex('R.mkstemp(%s)' % A(0), 'i')
        if name == 'fseeko':
            return Ex('R.fseek(%s)' % ', '.join(A(i) for i in range(len(args))), 'i')
        simple = {'strcpy', 'strlen', 'strcmp', 'atoi', 'fopen', 'feof', 'fclose', 'strtok', 'atof', 'ftell', 'strstr',
                  'rewind', 'strchr', 'strcat', 'fseek', 'remove', 'strcspn', 'toupper', 'strrchr', 'fflush', 'fgets', 'realpath'}
        if name in simple:
            rt = {'strlen': 'ul', 'atoi': 'i', 'strcmp': 'i', 'feof': 'i', 'fclose': 'i', 'atof': 'd', 'ftell': 'l',
                  'strcspn': 'ul', 'toupper': 'i', 'fseek': 'i', 'remove': 'i', 'fflush': 'i', 'rewind': 'v'}.get(name, tg)
            return Ex('R.%s(%s)' % (name, ', '.join(A(i) for i in range(len(args)))), rt)
        self.problem(c, 'libc ' + name)
        return Ex('R.%s(%s)' % (name, ', '.join(A(i) for i in range(len(args)))), tg)

    def vararg(self, a, scanf):
        """printf/scanf variadic argument"""
        sa = strip(a)
        if scanf:
            # pointers: &int, &double, &float, char buffer
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = kids(sa)[0]
                lv = self.lvalue(o)
                t = ctag(strip(o).type)
                return {'i': 'R.RefI(__v => %s = __v)', 'd': 'R.RefD(__v => %s = __v)', 'f': 'R.RefF(__v => %s = __v)',
                        'l': 'R.RefL(__v => %s = __v)'}.get(t, 'R.RefI(__v => %s = __v)') % lv
            return self.val(a).code
        e = self.val(a)
        return e.code

    def alloc(self, call, t):
        """malloc/calloc/realloc(n, sizeof(T)) -> new T[n]"""
        args = list(call.get_arguments())
        t = canon(t)
        if t.kind != T.POINTER:
            self.problem(call, 'alloc into non-pointer')
            return Ex('null', 'o')
        et = canon(t.get_pointee())
        name = call.spelling
        # element count expression
        if name == 'calloc':
            n = self.count_expr(args[0], args[1], et, mul=True)
        elif name == 'malloc':
            n = self.count_expr(args[0], None, et, mul=False)
        else:
            n = self.count_expr(args[1], None, et, mul=False)
            return Ex('R.Realloc(%s, %s)' % (self.val(args[0]).code, n), 'o' if ctag(t) != 'c' else 'c')
        if ctag(t) == 'c':
            return Ex('R.Buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('new %s()' % self.rec(et), 'o')
            return Ex('R.NewArray<%s>(%s)' % (self.rec(et), n), 'o')
        if et.kind == T.POINTER:
            inner = self.cs_type(et, mode='array') if ptr_category(et) != 'record' else self.rec(canon(et.get_pointee()))
            if ptr_category(et) == 'char':
                inner = 'CPtr'
            return Ex('new %s[%s]' % (inner, n), 'o')
        return Ex('new %s[%s]' % (self.cs_type(et), n), 'o')

    def count_expr(self, a, b, et, mul):
        """number of elements from calloc(a, b) / malloc(a)"""
        size = self.sizeof_type(et)
        def is_sizeof(x):
            return strip(x).kind == K.CXX_UNARY_EXPR
        if mul:
            if is_sizeof(b):
                return self.int_code(a)
            if is_sizeof(a):
                return self.int_code(b)
            return '(%s * %s) / %d' % (self.int_code(a), self.int_code(b), size)
        sa = strip(a)
        if is_sizeof(sa):
            return '1'
        if sa.kind == K.BINARY_OPERATOR and binop(sa) == '*':
            l, r = kids(sa)
            if is_sizeof(l):
                return self.int_code(r)
            if is_sizeof(r):
                return self.int_code(l)
        return '(%s) / %d' % (self.int_code(a), size)

    def int_code(self, x):
        e = self.val(x)
        if e.tag in ('ul', 'l', 'u'):
            return '(int)(%s)' % e.code
        return e.code

    def sizeof_type(self, t):
        t = canon(t)
        return max(t.get_size(), 1)

    def freadwrite(self, c, name, args):
        buf, size, cnt, f = args
        sb = strip(buf)
        et = None
        if sb.kind == K.UNARY_OPERATOR and unop(sb) == '&':
            o = strip(kids(sb)[0])
            if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                base, idx = kids(o)
                et = canon(o.type)
                target = '%s, %s' % (self.ex(base).code, self.val(idx).code)
                kind = 'Arr'
            else:
                et = canon(o.type)
                kind = 'Ref'
                target = ('ref ' if name == 'fread' else '') + self.lvalue(o)
        elif self.mode_of_expr(sb) == 'ref':
            et = canon(canon(sb.type).get_pointee())
            kind = 'Ref'
            target = ('ref ' if name == 'fread' else '') + self.ex(sb).code
        else:
            bt = canon(sb.type)
            et = canon(bt.get_pointee()) if bt.kind == T.POINTER else canon(bt.element_type)
            kind = 'Arr'
            target = '%s, 0' % self.ex(sb).code
        sz = evaluate(strip(size))
        if sz and sz[0] == 'int' and kind == 'Ref' and sz[1] != self.sizeof_type(et) and et.kind in (T.LONG, T.INT, T.ULONG, T.UINT):
            # e.g. an 8-byte off_t written with sizeof(INT4): only the low bytes go to the file
            if name == 'fwrite':
                return Ex('R.fwriteN1((long)(%s), %d, %s)' % (target, sz[1], self.val(f).code), 'ul')
            return Ex('R.freadN1(%s, %d, %s)' % (target, sz[1], self.val(f).code), 'ul')
        tn = {T.DOUBLE: 'D', T.FLOAT: 'F', T.INT: 'I', T.LONG: 'L', T.CHAR_S: 'C', T.SCHAR: 'C', T.UINT: 'I', T.ENUM: 'I'}.get(et.kind, None)
        if tn is None:
            self.problem(c, '%s of %s' % (name, et.spelling))
            tn = 'X'
        if kind == 'Ref':
            return Ex('R.%s%s1(%s, %s)' % (name, tn, target, self.val(f).code), 'ul')
        return Ex('R.%s%s(%s, %s, %s)' % (name, tn, target, self.int_code(cnt), self.val(f).code), 'ul')

    # ================================================================== statements
    def local_name(self, d):
        k = decl_key(d)
        return self.locals.get(k, ident(d.spelling))

    def static_local_name(self, d):
        return ident('%s_%s' % (d.semantic_parent.spelling, d.spelling))

    def stmt(self, c, ind):
        k = c.kind
        p = '    ' * ind
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
            e = self.val(ch[0])
            e = self.conv(e, ch[0].type, self.cur_ret)
            if ctag(self.cur_ret) == 'c' and is_null(e.code):
                e = Ex('CPtr.Null', 'c')
            return [p + 'return %s;' % e.code]
        if k == K.NULL_STMT:
            return [p + ';']
        if k in (K.CASE_STMT, K.DEFAULT_STMT):
            self.problem(c, 'case outside switch body')
            return []
        if k == K.LABEL_STMT or k == K.GOTO_STMT:
            self.problem(c, 'goto/label')
            return []
        # expression statement
        e = self.ex(c)
        code = e.code
        if e.tag == 'b' or re.fullmatch(r'\(.*\)', code) and not re.match(r'\(.*\)\(', code):
            code = 'R.Discard(%s)' % code if not re.search(r'(\+\+|--|=|\bS\.\w+\(|R\.\w+\()', code) else code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        return [p + code + ';']

    def block(self, c, ind):
        if c.kind == K.COMPOUND_STMT:
            return self.stmt(c, ind)
        return ['    ' * ind + '{'] + self.stmt(c, ind + 1) + ['    ' * ind + '}']

    def for_stmt(self, c, ind):
        p = '    ' * ind
        # libclang gives children in order init, cond, inc, body but omits missing parts; use tokens to place them
        ch = kids(c)
        body = ch[-1]
        parts = ch[:-1]
        toks = list(c.get_tokens())
        # positions of the two ';' inside the for header (depth 1 parens)
        depth = 0; semis = []
        for t in toks[1:]:
            if t.spelling == '(':
                depth += 1
            elif t.spelling == ')':
                depth -= 1
                if depth == 0:
                    close = t.extent.start.offset; break
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
        if init is not None:
            if init.kind == K.DECL_STMT:
                pre = []
                for d in kids(init):
                    pre += self.local_decl(d, ind + 1)
                init_s = ''
            else:
                init_s = self.expr_stmt_code(init)
        else:
            init_s = ''
        cond_s = self.cond(cond) if cond is not None else ''
        inc_s = self.expr_stmt_code(inc) if inc is not None else ''
        head = p + 'for (%s; %s; %s)' % (init_s, cond_s, inc_s)
        if pre:
            return [p + '{'] + pre + ['    ' + head] + self.block(body, ind + 1) + [p + '}']
        return [head] + self.block(body, ind)

    def expr_stmt_code(self, c):
        s = strip(c) if c.kind == K.PAREN_EXPR else c
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmt_code(l) + ', ' + self.expr_stmt_code(r)
        return self.ex(c).code

    def switch(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        e = self.val(ch[0])
        body = ch[-1]
        items = kids(body) if body.kind == K.COMPOUND_STMT else [body]
        sections = []   # [labels, stmts]
        for it in items:
            if it.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                labels = []
                x = it
                while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                    xc = kids(x)
                    if x.kind == K.CASE_STMT:
                        labels.append('case %s:' % self.val(xc[0]).code)
                        x = xc[1]
                    else:
                        labels.append('default:')
                        x = xc[0]
                if sections and not sections[-1][1]:
                    sections[-1][0].extend(labels)
                else:
                    sections.append([labels, []])
                sections[-1][1].append(x)
            else:
                if not sections:
                    continue
                sections[-1][1].append(it)
        out = [p + 'switch (%s)' % (e.code if e.tag != 'b' else '(%s ? 1 : 0)' % e.code), p + '{']
        for si, (labels, stmts) in enumerate(sections):
            for lab in labels:
                out.append(p + '    ' + lab)
            body_lines = []
            for s in stmts:
                body_lines += self.stmt(s, ind + 2)
            out += [p + '        {'] if False else []
            out += body_lines
            if not self.terminates(stmts):
                if si + 1 < len(sections):
                    nxt = sections[si + 1][0][0]
                    out.append(p + '        ' + ('goto default;' if nxt == 'default:' else 'goto ' + nxt[:-1] + ';'))
                else:
                    out.append(p + '        break;')
        out.append(p + '}')
        return out

    def terminates(self, stmts):
        if not stmts:
            return False
        last = stmts[-1]
        if last.kind in (K.BREAK_STMT, K.RETURN_STMT, K.CONTINUE_STMT, K.GOTO_STMT):
            return True
        if last.kind == K.COMPOUND_STMT:
            return self.terminates(kids(last))
        if last.kind == K.IF_STMT:
            ch = kids(last)
            return len(ch) == 3 and self.terminates([ch[1]]) and self.terminates([ch[2]])
        return False

    def local_decl(self, d, ind):
        p = '    ' * ind
        if d.kind != K.VAR_DECL:
            return []
        if d.storage_class == front.ci.StorageClass.EXTERN:
            return []            # block-scope extern: refers to the global
        if d.storage_class == front.ci.StorageClass.STATIC:
            self.static_locals.append((d, self.cur_file))
            return []
        name = self.declare_local(d)
        init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        t = canon(d.type)
        if t.kind == T.CONSTANTARRAY:
            et = canon(t.element_type)
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                if ctag(et) == 'c' or et.kind == T.CONSTANTARRAY:
                    pass
                return [p + '%s %s = %s;' % (self.cs_type(d.type, d), name, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return [p + 'CPtr %s = R.BufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return [p + 'CPtr %s = R.Buf(%d);' % (name, t.element_count)]
            return [p + '%s %s = %s;' % (self.cs_type(d.type, d), name, self.new_array(t))]
        ty = self.cs_type(d.type, d)
        if ctag(t) == 'rec':
            if init:
                ie = self.ex(init[-1])
                return [p + '%s %s = %s.Clone();' % (ty, name, ie.code)]
            return [p + '%s %s = new %s();' % (ty, name, ty)]
        if init:
            ie = self.val(init[-1])
            ie = self.conv(ie, init[-1].type, d.type)
            code = ie.code
            if ctag(t) == 'c' and is_null(code):
                code = 'CPtr.Null'
            return [p + '%s %s = %s;' % (ty, name, code)]
        return [p + '%s %s = %s;' % (ty, name, self.zero(d.type) if ctag(t) != 'o' else 'null')]

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return 'R.NewArray<%s>(%d)' % (self.rec(et), n)
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return 'R.NewBufs(%d, %d)' % (n, et.element_count)
        if et.kind == T.CONSTANTARRAY:
            inner = canon(et.element_type)
            return 'R.Jagged<%s>(%d, %d)' % (self.cs_type(inner), n, et.element_count)
        ety = self.cs_type(et)
        if ety.endswith('[]'):
            i = ety.index('[')
            return 'new %s[%d]%s' % (ety[:i], n, ety[i:])
        return 'new %s[%d]' % (self.cs_type(et), n)

    def declare_local(self, d):
        n = d.spelling
        k = decl_key(d)
        if n in self.used_names:
            i = 2
            while '%s_%d' % (n, i) in self.used_names:
                i += 1
            nn = '%s_%d' % (n, i)
        else:
            nn = n
        self.used_names.add(nn)
        self.locals[k] = ident(nn)
        return ident(nn)

    # ================================================================== functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.cur_ret = c.result_type
        params = list(c.get_arguments())
        ps = []
        for prm in params:
            nm = self.declare_local(prm)
            ps.append('%s %s' % (self.cs_type(prm.type, prm), nm))
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        out = ['    // %s:%d' % (b, c.location.line),
               '    public static %s %s(%s)' % (self.cs_type(c.result_type), self.fname[key], ', '.join(ps))]
        out += self.stmt(body, 1)
        return out

    # ================================================================== records
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        out = ['public sealed class %s' % ident(name), '{']
        ctor = []
        clone = ['    public %s Clone()' % ident(name), '    {', '        var c = (%s)MemberwiseClone();' % ident(name)]
        for f in fields:
            t = canon(f.type)
            fn = ident(f.spelling)
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                ty = self.cs_type(f.type, f)
                if ctag(t) == 'c':
                    out.append('    public CPtr %s = R.Buf(%d);' % (fn, t.element_count))
                    clone.append('        c.%s = R.CopyBuf(%s);' % (fn, fn))
                else:
                    out.append('    public %s %s = %s;' % (ty, fn, self.new_array(t)))
                    if et.kind == T.RECORD:
                        clone.append('        c.%s = R.CloneArray(%s);' % (fn, fn))
                    elif et.kind == T.CONSTANTARRAY:
                        clone.append('        c.%s = R.CloneJagged(%s);' % (fn, fn))
                    else:
                        clone.append('        c.%s = (%s)%s.Clone();' % (fn, ty, fn))
            elif t.kind == T.RECORD:
                out.append('    public %s %s = new %s();' % (self.rec(t), fn, self.rec(t)))
                clone.append('        c.%s = %s.Clone();' % (fn, fn))
            else:
                ty = self.cs_type(f.type, f)
                if ty.startswith('ref '):
                    self.problem(f, 'ref field')
                    ty = ty[4:]
                z = self.zero(f.type) if ctag(t) not in ('o',) else 'null'
                out.append('    public %s %s = %s;' % (ty, fn, z))
        clone += ['        return c;', '    }']
        out += clone
        out.append('}')
        return out

    # ================================================================== globals
    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        t = canon(c.type)
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        ty = self.cs_type(c.type, c)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return '    public static %s %s = %s;' % (ty, name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return '    public static CPtr %s = R.BufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return '    public static CPtr %s = R.Buf(%d);' % (name, t.element_count)
            return '    public static %s %s = %s;' % (ty, name, self.new_array(t))
        if t.kind == T.RECORD:
            return '    public static %s %s = new %s();' % (ty, name, ty)
        if init:
            e = self.conv(self.val(init[-1]), init[-1].type, c.type)
            return '    public static %s %s = %s;' % (ty, name, e.code if not (ctag(t) == 'c' and is_null(e.code)) else 'CPtr.Null')
        return '    public static %s %s = %s;' % (ty, name, self.zero(c.type) if ctag(t) != 'o' else 'null')

    # ================================================================== driver
    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        for f in os.listdir(outdir):
            if f.endswith('.cs'):
                os.remove(os.path.join(outdir, f))
        self.func_values = set()
        self.delegate_ref = {}
        self.static_locals = []
        self.cur_file = None
        files = collections.defaultdict(list)
        for key, c in self.F.funcs.items():
            if key[0] in SKIP_FILES or key in OVERRIDES:
                continue
            try:
                files[key[0]] += self.function(key, c) + ['']
            except Exception as ex:
                import traceback; traceback.print_exc()
                self.problems.append('%s:%s CRASH %s' % (key[0], key[1], ex))
        glob_lines = collections.defaultdict(list)
        for k, c in self.F.globals.items():
            b = self.F.global_owner[k]
            if b in SKIP_FILES:
                continue
            glob_lines[b].append(self.global_decl(k, c))
        # static locals hoisted to the class
        for d, b in self.static_locals:
            self.cur_file = b
            t = canon(d.type)
            init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
            name = self.static_local_name(d)
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                glob_lines[b].append('    public static %s %s = %s;' % (self.cs_type(d.type, d), name, self.init_list(strip(init[-1]), t).code))
            elif ctag(t) == 'c' and t.kind == T.CONSTANTARRAY:
                glob_lines[b].append('    public static CPtr %s = R.BufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count))
            elif init:
                glob_lines[b].append('    public static %s %s = %s;' % (self.cs_type(d.type, d), name, self.val(init[-1]).code))
            else:
                glob_lines[b].append('    public static %s %s;' % (self.cs_type(d.type, d), name))
        hdr = ['// Generated from EPA SWMM 5.2.4 (%s) by tools/c2x/emit_cs.py. Do not edit by hand;',
               '// fix the translator or runtime/ instead.',
               'using System;', 'namespace Swmm5', '{', 'public static partial class S', '{']
        for b in sorted(set(files) | set(glob_lines)):
            lines = [l % b if i == 0 else l for i, l in enumerate(hdr)]
            lines += glob_lines.get(b, [])
            if glob_lines.get(b):
                lines.append('')
            lines += files.get(b, [])
            lines += ['}', '}']
            open(os.path.join(outdir, b[:-2] + '.cs'), 'w').write('\n'.join(lines) + '\n')
        # records, enums, macros, literals, delegates
        out = ['// Generated by tools/c2x/emit_cs.py from EPA SWMM 5.2.4 headers.', 'using System;', 'namespace Swmm5', '{']
        for name, c in self.F.records.items():
            out += self.record(name, c)
        for sig, (name, ft) in self.delegates.items():
            out.append(self.delegate_decl_auto(name, ft))
        out += ['public static partial class S', '{']
        for n, v in self.F.enum_consts.items():
            out.append('    public const int %s = %d;' % (ident(n), v))
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, s) in m.items():
                if n in self.macro_global and n not in done and kind in ('int', 'float') and n not in self.F.enum_consts:
                    done.add(n)
                    if kind == 'int':
                        out.append('    public const int %s = %s;' % (ident(n), re.sub(r'[uUlL]+$', '', s)))
                    else:
                        out.append('    public const double %s = %s;' % (ident(n), self.cs_float(s, 'd')))
        for bts, name in self.lits.items():
            out.append('    public static readonly CPtr %s = R.Lit(%s);' % (name, self.cs_bytes(bts)))
        out += ['}', '}']
        open(os.path.join(outdir, '_types.cs'), 'w').write('\n'.join(out) + '\n')
        return self.problems

    def delegate_decl_auto(self, name, ft):
        """delegate whose pointer params are ref when the functions bound to it dereference them"""
        ps = []
        for i, a in enumerate(ft.argument_types()):
            a = canon(a)
            cat = ptr_category(a)
            if cat == 'scalar':
                isref = self.delegate_ref.get((name, i))
                if isref is None:
                    isref = self.bound_param_mode(ft, i) == 'ref'
                base = self.cs_type(a.get_pointee())
                ps.append(('ref %s' % base if isref else base + '[]') + ' a%d' % i)
            else:
                ps.append(self.cs_type(a, mode='obj' if cat == 'record' else None) + ' a%d' % i)
        return 'public delegate %s %s(%s);' % (self.cs_type(ft.get_result()), name, ', '.join(ps))

    def bound_param_mode(self, ft, i):
        sp = ft.spelling
        for key, c in self.F.funcs.items():
            if canon(c.type).spelling == sp:
                prm = list(c.get_arguments())
                if i < len(prm):
                    m = self.P.mode_of(prm[i])
                    if m:
                        return m
        return None


if __name__ == '__main__':
    F = front.Front()
    em = CSEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_cs')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
