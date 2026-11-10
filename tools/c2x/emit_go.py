"""
emit_go.py - EPA SWMM 5.2.4 C  ->  Go 1.22+ (package main in go/swmm5: one file per C file, records and
function types in types.go, enums/macros/string literals in consts.go; the C runtime is package
swmm5go/crt, imported as R, and glibc's math is package swmm5go/glibm, imported as M).

Derived from the Java back end (same front end, same pointer analysis), but Go has real pointers, so
nothing is boxed:
  int/unsigned/long/size_t/double/float -> int32/uint32/int64/uint64/float64/float32 (Go wraps like x86)
  every implicit C conversion            -> an explicit Go conversion (Go has none of its own)
  double -> int                          -> R.D2I / R.D2L (x86-64 cvttsd2si: NaN or out of range -> INT_MIN)
  every float + - * /                    -> float64(a op b): the Go spec lets a compiler fuse x*y + z unless
                                            the product is explicitly converted; float literals are typed
                                            float64(...) so constant expressions round like C's
  char* / char[]                         -> R.CPtr (byte slice + offset); struct char arrays are [N]byte
                                            seen through R.CP(x.f[:])
  struct                                 -> Go struct value (C value copy is Go assignment)
  T* used with ->                        -> *T ; T* indexed -> []T ; &x passed as an array -> R.One(&x)
  fixed arrays                           -> Go arrays [N]T (decay is x[:])
  ?: , = ++ as expressions               -> if/else at statement level; R.If, closures, R.Set, R.PostInc
  do-while / switch fall-through         -> for __dw := true; __dw || cond; __dw = false / fallthrough
  locals                                 -> hoisted to the top of the function (C's scopes cannot clash:
                                            the front end gives every local a unique name)
Written by Claude (Anthropic); see AI-USE.md.
"""
import os, re, sys, collections, struct, subprocess
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES
from emit_java import JavaEmitter

GO_KEYWORDS = set('''break case chan const continue default defer else fallthrough for func go goto if import interface
map package range return select struct switch type var'''.split())
GO_PREDECLARED = set('''any bool byte comparable complex64 complex128 error float32 float64 int int8 int16 int32 int64 rune
string uint uint8 uint16 uint32 uint64 uintptr true false iota nil append cap clear close complex copy delete imag len make
max min new panic print println real recover'''.split())
GO_RESERVED = GO_KEYWORDS | GO_PREDECLARED | {'R', 'M', 'unsafe', 'main', 'init', 'math', 'os', 'fmt'}
HAND_NAMES = {'OdeDerivs', 'MAXFNAME_'}       # declared in overrides.go / main.go

GT = {'i': 'int32', 'u': 'uint32', 'l': 'int64', 'ul': 'uint64', 'd': 'float64', 'f': 'float32'}
INTTAGS = ('i', 'u', 'l', 'ul')
BITS = {'i': 32, 'u': 32, 'l': 64, 'ul': 64}
MATH = {'fabs': 'M.Fabs', 'sqrt': 'M.Sqrt', 'floor': 'M.Floor', 'ceil': 'M.Ceil', 'exp': 'M.Exp', 'log': 'M.Log',
        'log10': 'M.Log10', 'sin': 'M.Sin', 'cos': 'M.Cos', 'tan': 'M.Tan', 'asin': 'M.Asin', 'acos': 'M.Acos',
        'atan': 'M.Atan'}
LIBC = {'strcpy': 'Strcpy', 'strlen': 'Strlen', 'strcmp': 'Strcmp', 'atoi': 'Atoi', 'fopen': 'Fopen', 'feof': 'Feof',
        'fclose': 'Fclose', 'strtok': 'Strtok', 'atof': 'Atof', 'ftell': 'Ftell', 'strstr': 'Strstr', 'rewind': 'Rewind',
        'strchr': 'Strchr', 'strcat': 'Strcat', 'fseek': 'Fseek', 'fseeko': 'Fseek', 'remove': 'Remove', 'strcspn': 'Strcspn',
        'toupper': 'Toupper', 'strrchr': 'Strrchr', 'fflush': 'Fflush', 'fgets': 'Fgets', 'realpath': 'Realpath',
        'mkstemp': 'Mkstemp'}
LIBC_TAG = {'strlen': 'ul', 'atoi': 'i', 'strcmp': 'i', 'feof': 'i', 'fclose': 'i', 'atof': 'd', 'ftell': 'l',
            'strcspn': 'ul', 'toupper': 'i', 'fseek': 'i', 'fseeko': 'i', 'remove': 'i', 'fflush': 'i', 'rewind': 'v',
            'mkstemp': 'i'}
NULLC = '(R.CPtr{})'
PCATS = ('record', 'scalar', 'ptrptr')


def gid(n):
    return n + '_' if n in GO_RESERVED else n


def go_string(b):
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


def int_lit(code):
    """value of a code string that is a plain (possibly negative, parenthesised) integer literal, else None"""
    if not re.fullmatch(r'[()\s\-\d]+', code):
        return None
    s = re.sub(r'[()\s]', '', code)
    if not re.fullmatch(r'-?\d+', s):
        return None
    return int(s)


def wrap(v, tg):
    b = BITS[tg]
    v &= (1 << b) - 1
    if tg in ('i', 'l') and v >= 1 << (b - 1):
        v -= 1 << b
    return v


def is_gnull(code):
    code = code.strip()
    while code.startswith('(') and code.endswith(')') and JavaEmitter._balanced(code[1:-1]):
        code = code[1:-1].strip()
    return code in ('nil', 'R.CPtr{}')


class GoEmitter(JavaEmitter):
    def __init__(self, F):
        super().__init__(F)
        self._go_names()

    # ================================================================== naming
    def _go_names(self):
        F = self.F
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        taken = set(HAND_NAMES) | GO_RESERVED
        self.fname = {}
        for (b, n), c in F.funcs.items():
            self.fname[(b, n)] = gid(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.gname = {}
        for k, c in F.globals.items():
            n = c.spelling
            b = F.global_owner[k]
            self.gname[k] = gid(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        clash = [n for n, m in collections.Counter(list(self.fname.values()) + list(self.gname.values())).items() if m > 1]
        if clash:
            raise SystemExit('function/global name clash: %s' % clash)
        taken |= set(self.fname.values()) | set(self.gname.values())

        def fresh(n, suffix):
            nn = gid(n)
            while nn in taken:
                nn += suffix
            taken.add(nn)
            return nn
        # static locals become package variables <function>_<name>
        self.slname = {}
        for (b, n), c in F.funcs.items():
            def walk(x):
                for y in x.get_children():
                    if y.kind == K.VAR_DECL and y.storage_class == front.ci.StorageClass.STATIC:
                        self.slname[decl_key(y)] = fresh('%s_%s' % (self.fname[(b, n)], y.spelling), '_')
                    walk(y)
            walk(c)
        self.recname = {}
        for name in F.records:
            self.recname[name] = fresh(name, '_T')
        self.ename = {}
        for n in F.enum_consts:
            self.ename[n] = fresh(n, '_E')
        self.mname = {}
        for n in sorted(self.macro_global):
            if n not in F.enum_consts:
                self.mname[n] = fresh(n, '_M')
        if any(re.fullmatch(r'(L|FP)\d+', n) for n in taken):
            raise SystemExit('generated-name clash with L#/FP#')
        self.pkg_names = taken

    def global_ref(self, d):
        k = self.global_key(d)
        if k is not None:
            return self.gname[k]
        if d.spelling in ('stdout', 'stderr'):
            return 'R.Stdout'
        return gid(d.spelling)

    def macro_name(self, n):
        return self.mname.get(n)

    def static_local_name(self, d):
        return self.slname[decl_key(d)]

    def local_name(self, d):
        return self.locals.get(decl_key(d), gid(d.spelling))

    def declare_local(self, d, gt=None):
        n = d.spelling
        nn, i = n, 2
        while nn in self.used_names or nn in self.pkg_names:
            nn = '%s_%d' % (n, i)
            i += 1
        self.used_names.add(nn)
        self.locals[decl_key(d)] = nn
        return nn

    def field(self, n):
        return n + '_' if n in GO_KEYWORDS else n

    def rec(self, t):
        n = record_name(t)
        return self.recname.get(n, gid(n))

    # ================================================================== types
    def gtype(self, t, decl=None, mode=None, field=False):
        t = canon(t)
        tg = ctag(t)
        if tg in GT:
            return GT[tg]
        if tg == 'v':
            return ''
        if tg == 'rec':
            return self.rec(t)
        is_param = decl is not None and decl.kind == K.PARM_DECL
        if t.kind == T.CONSTANTARRAY and not is_param and mode is None:
            return self.fixed_type(t, field)
        cat = ptr_category(t)
        if mode is None and decl is not None:
            mode = self.P.mode_of(decl)
        if cat == 'char':
            return 'R.CPtr'
        if cat == 'file':
            return '*R.CFile'
        if cat == 'void':
            return 'any'
        if cat == 'func':
            return self.delegate(t)
        e = canon(t.element_type if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) else t.get_pointee())
        if cat == 'record':
            if (mode in (None, 'array') and t.kind != T.POINTER) or mode == 'array':
                return '[]' + self.rec(e)
            return '*' + self.rec(e)
        if cat == 'scalar':
            return ('*' if mode == 'ref' else '[]') + GT[ctag(e)]
        if cat == 'ptrptr':
            if e.kind == T.CONSTANTARRAY:          # pointer to rows of a 2-D array
                inner = self.fixed_type(e)
            else:
                inner = self.gtype(e, mode='obj' if ptr_category(e) == 'record' else 'array')
            return ('*' if mode == 'ref' else '[]') + inner
        return 'any'

    def fixed_type(self, t, field=False):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if ctag(t) == 'c':
            return '[%d]byte' % n if field else 'R.CPtr'
        if et.kind == T.CONSTANTARRAY:
            if ctag(et) == 'c':
                return '[]R.CPtr'
            return '[%d]%s' % (n, self.fixed_type(et, field))
        if et.kind == T.RECORD:
            return '[%d]%s' % (n, self.rec(et))
        if et.kind == T.POINTER:
            return '[%d]%s' % (n, self.gtype(et, mode='obj' if ptr_category(et) == 'record' else 'array'))
        return '[%d]%s' % (n, self.gtype(et))

    def cs_type(self, t, decl=None, mode=None):
        return self.gtype(t, decl, mode)

    jtype = cs_type

    def gzero(self, gt):
        if gt in GT.values():
            return '0'
        if gt == 'R.CPtr':
            return NULLC
        if gt.startswith(('[]', '*')) or gt == 'any' or re.fullmatch(r'FP\d+|OdeDerivs', gt):
            return 'nil'
        return '(%s{})' % gt

    def zero(self, t):
        return self.gzero(self.gtype(t))

    # ---------------------------------------------------------------- pointer shapes
    def pcat(self, t):
        c = ptr_category(t)
        return c if c in PCATS else None

    def natural_shape(self, t):
        return 'ptr' if ptr_category(t) == 'record' else 'slice'

    def want_of(self, d):
        t = canon(d.type)
        if t.kind == T.CONSTANTARRAY and d.kind != K.PARM_DECL:
            return 'fixed'
        return 'ptr' if self.gtype(d.type, d).startswith('*') else 'slice'

    def want_of_type(self, gt):
        return 'ptr' if gt.startswith('*') else 'slice'

    def shape_of(self, c):
        s = c
        while True:
            if s.kind == K.PAREN_EXPR:
                s = kids(s)[0]
                continue
            if s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1:
                ch = kids(s)[0]
                if canon(ch.type).kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) and canon(s.type).kind == T.POINTER:
                    return 'slice'
                s = ch
                continue
            break
        k = s.kind
        t = canon(s.type)
        if t.kind == T.CONSTANTARRAY:
            return 'fixed'
        if k in (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR) and s.referenced is not None and \
                s.referenced.kind in (K.VAR_DECL, K.PARM_DECL, K.FIELD_DECL):
            return self.want_of(s.referenced)
        if k == K.UNARY_OPERATOR and unop(s) == '&':
            return 'ptr'
        if k == K.UNARY_OPERATOR and unop(s) in ('post++', 'post--', 'pre++', 'pre--'):
            return self.shape_of(kids(s)[0])
        if k == K.BINARY_OPERATOR and binop(s) in ('+', '-'):
            return 'slice'
        if k in (K.BINARY_OPERATOR, K.COMPOUND_ASSIGNMENT_OPERATOR) and binop(s) in ('=', '+=', '-='):
            return self.shape_of(kids(s)[0])
        if k == K.CONDITIONAL_OPERATOR:
            for b in kids(s)[1:]:
                if not self.is_null_c(b):
                    return self.shape_of(b)
            return self.natural_shape(t)
        if k == K.CSTYLE_CAST_EXPR:
            inner = kids(s)[-1]
            si = strip(inner)
            if si.kind == K.CALL_EXPR and si.spelling in ('malloc', 'calloc', 'realloc'):
                return self.alloc_shape(si, t)
            if ptr_category(inner.type) == 'void':
                return self.natural_shape(t)
            return self.shape_of(inner)
        if k == K.CALL_EXPR and s.spelling in ('malloc', 'calloc', 'realloc'):
            return self.alloc_shape(s, t)
        return self.natural_shape(t)

    def alloc_shape(self, call, t):
        et = canon(canon(t).get_pointee())
        if call.spelling != 'realloc' and et.kind == T.RECORD and front.alloc_count_is_one(call):
            return 'ptr'
        return 'slice'

    def is_null_c(self, c):
        s = strip(c)
        if s.kind == K.CSTYLE_CAST_EXPR:
            s = strip(kids(s)[-1])
        if s.kind == K.INTEGER_LITERAL:
            v = evaluate(s)
            return v is not None and v[1] == 0 and canon(c.type).kind == T.POINTER
        if s.kind == K.GNU_NULL_EXPR:
            return True
        return False

    def adapt(self, code, sh, want):
        if want is None or sh == want or is_gnull(code):
            return code
        if sh == 'fixed':
            return '%s[:]' % self.paren(code) if want == 'slice' else '&%s[0]' % self.paren(code)
        if sh == 'slice' and want == 'ptr':
            return 'R.First(%s)' % code
        if sh == 'ptr' and want == 'slice':
            return 'R.One(%s)' % code
        return code

    def ptr_val(self, c, want):
        """Go code for the pointer-valued C expression c (record/scalar/ptrptr) in the Go shape want"""
        if self.is_null_c(c):
            return 'nil'
        s = strip(c)
        if s.kind == K.UNARY_OPERATOR and unop(s) == '&':
            o = strip(kids(s)[0])
            if o.kind == K.ARRAY_SUBSCRIPT_EXPR and ptr_category(kids(o)[0].type) != 'char':
                base, ix = kids(o)
                b = self.array_base(base)
                i = self.val(ix).code
                if want == 'slice':
                    return '%s[%s:]' % (self.paren(b), i)
                return '&%s[%s]' % (self.paren(b), i)
            if canon(o.type).kind == T.CONSTANTARRAY:          # &array: pointer to its first element
                return self.adapt(self.ex(o).code, 'fixed', want)
            r = self.ref_of(o)
            return r if want == 'ptr' else 'R.One(%s)' % r
        call = s
        if call.kind == K.CSTYLE_CAST_EXPR:
            call = strip(kids(call)[-1])
        if call.kind == K.CALL_EXPR and call.spelling in ('malloc', 'calloc', 'realloc'):
            return self.alloc(call, c.type, want).code
        if s.kind == K.CONDITIONAL_OPERATOR:
            cc, a, b = kids(s)
            gt = self.gtype(c.type, mode='ref' if want == 'ptr' and ptr_category(c.type) != 'record' else
                            ('obj' if want == 'ptr' else 'array'))
            return self.ternary_code(self.cond(cc), self.ptr_val(a, want), self.ptr_val(b, want), gt, a, b)
        return self.adapt(self.ex(c).code, self.shape_of(c), want)

    def value_for(self, r, lt, want=None):
        """C value r converted to C type lt (the type of what receives it)"""
        if self.pcat(lt) and canon(lt).kind != T.CONSTANTARRAY:
            return self.ptr_val(r, want or self.natural_shape(lt))
        if ctag(lt) == 'rec':
            return self.ex(r).code
        return self.conv(self.val(r), r.type, lt).code

    # ================================================================== conversions
    def to_ctype(self, e, t):
        want = ctag(t)
        if e.tag == 'b' and want in NUMTAGS:
            return self.conv_tags(Ex('R.B2I(%s)' % e.code, 'i'), 'i', want)
        return e

    def as_bool(self, e):
        if e.tag == 'b':
            return e.code
        if e.tag in INTTAGS or e.tag in ('d', 'f'):
            return '(%s != 0)' % e.code
        if e.tag == 'c':
            return '!%s.IsNull()' % self.paren(e.code)
        return '(%s != nil)' % e.code

    def conv(self, e, src_t, dst_t):
        return self.conv_tags(e, ctag(src_t), ctag(dst_t))

    def conv_tags(self, e, s, d):
        if e.tag == 'b' and d in NUMTAGS:
            e = Ex('R.B2I(%s)' % e.code, 'i')
            s = 'i'
        if s == d or d in ('v', '?'):
            return Ex(e.code, d if d != '?' else e.tag)
        if d == 'rec':
            return e
        if d in INTTAGS:
            if s in ('d', 'f'):
                x = e.code if s == 'd' else 'float64(%s)' % e.code
                return Ex({'i': 'R.D2I(%s)', 'l': 'R.D2L(%s)', 'u': 'uint32(R.D2L(%s))', 'ul': 'uint64(R.D2L(%s))'}[d] % x, d)
            v = int_lit(e.code)
            if v is not None:
                return Ex(str(wrap(v, d)), d)
            return Ex('%s(%s)' % (GT[d], e.code), d)
        if d == 'd':
            return Ex('float64(%s)' % e.code, 'd')
        if d == 'f':
            if s == 'd':
                return Ex('float32(float64(%s))' % e.code, 'f')
            return Ex('float32(%s)' % e.code, 'f')
        if d == 'c':
            if is_gnull(e.code) or (e.tag in INTTAGS and int_lit(e.code) == 0):
                return Ex(NULLC, 'c')
            return Ex(e.code, 'c')
        if d == 'o':
            if is_gnull(e.code) or (e.tag in INTTAGS and int_lit(e.code) == 0):
                return Ex('nil', 'o')
            return Ex(e.code, 'o')
        return e

    def idx(self, e):
        """an int32 index for R.CPtr methods"""
        if e.tag in ('u', 'l', 'ul'):
            v = int_lit(e.code)
            return str(v) if v is not None else 'int32(%s)' % e.code
        return e.code

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
        return Ex(str(v[1] if v else 0), tg)

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
            return Ex('float64(%s)' % s, tg)
        if len(toks) == 1 and self.macro_name(toks[0]) and tg != 'f':
            return Ex(self.macro_name(toks[0]), tg)
        v = evaluate(c)
        x = v[1] if v else 0.0
        if tg == 'f':
            x = struct.unpack('<f', struct.pack('<f', x))[0]
        if x != x:
            return Ex('R.QNaN' if tg != 'f' else 'float32(R.QNaN)', tg)
        if abs(x) == float('inf'):
            s = 'R.Inf' if x > 0 else '(-R.Inf)'
            return Ex(s if tg != 'f' else 'float32(%s)' % s, tg)
        return Ex('%s(%r)' % ('float32' if tg == 'f' else 'float64', x), tg)

    def x_CHARACTER_LITERAL(self, c):
        v = evaluate(c)
        return Ex(str(v[1] if v else 0), 'i')

    def x_STRING_LITERAL(self, c):
        return Ex(self.lit(self.string_bytes(c)), 'c')

    def x_GNU_NULL_EXPR(self, c):
        return Ex('nil', 'o')

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return Ex(gid(c.spelling), '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return Ex(str(d.enum_value), 'i')
            return Ex(self.ename[d.spelling], 'i')
        if d.kind == K.FUNCTION_DECL:
            keys = self.F.func_by_decl.get(d.spelling) or []
            cand = [k for k in keys if k[0] == self.cur_file] or \
                   [k for k in keys if self.F.funcs[k].storage_class != front.ci.StorageClass.STATIC]
            if not cand:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex(gid(d.spelling), 'o')
            return Ex(self.fname[cand[0]], 'o')
        if d.kind == K.PARM_DECL or (d.kind == K.VAR_DECL and d.semantic_parent is not None and
                                     d.semantic_parent.kind == K.FUNCTION_DECL and
                                     d.storage_class != front.ci.StorageClass.STATIC):
            return Ex(self.local_name(d), ctag(d.type))
        if d.kind == K.VAR_DECL:
            if d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL:
                return Ex(self.static_local_name(d), ctag(d.type))
            return Ex(self.global_ref(d), ctag(d.type))
        return Ex(gid(c.spelling), ctag(c.type))

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                return Ex(self.zero(c.type), ctag(c.type))
            return self.ex(ch[0])
        inner = ch[0]
        it, ct = canon(inner.type), canon(c.type)
        if it.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) and ct.kind == T.POINTER:       # array-to-pointer decay
            e = self.ex(inner)
            if ctag(c.type) == 'c':
                return Ex(e.code, 'c')
            return Ex('%s[:]' % self.paren(e.code), 'o')
        e = self.ex(inner)
        if ct.kind == T.POINTER and e.tag in INTTAGS and int_lit(e.code) == 0:
            return Ex(NULLC if ctag(c.type) == 'c' else 'nil', ctag(c.type))
        return self.conv(e, inner.type, c.type)

    def x_CSTYLE_CAST_EXPR(self, c):
        inner = kids(c)[-1]
        if ctag(c.type) == 'v':
            return self.ex(inner)
        s = strip(inner)
        if s.kind == K.CALL_EXPR and s.spelling in ('malloc', 'calloc', 'realloc'):
            return self.alloc(s, c.type)
        e = self.ex(inner)
        if canon(c.type).kind == T.POINTER and (is_gnull(e.code) or (e.tag in INTTAGS and int_lit(e.code) == 0)):
            return Ex(NULLC if ctag(c.type) == 'c' else 'nil', ctag(c.type))
        if ctag(c.type) == 'o' and ctag(inner.type) == 'o':
            if ptr_category(inner.type) == 'void' and ptr_category(c.type) in PCATS:
                gt = self.gtype(c.type, mode='obj' if ptr_category(c.type) == 'record' else 'array')
                return Ex('%s.(%s)' % (self.paren(e.code), gt), 'o')
            return e
        e = self.to_ctype(e, inner.type)
        r = self.conv(e, inner.type, c.type)
        k = canon(c.type).kind
        small = {T.UCHAR: 'uint8', T.CHAR_U: 'uint8', T.CHAR_S: 'int8', T.SCHAR: 'int8', T.SHORT: 'int16',
                 T.USHORT: 'uint16'}.get(k)
        if small and canon(inner.type).kind != k:
            v = int_lit(r.code)
            if v is not None:
                b = 8 if '8' in small else 16
                v &= (1 << b) - 1
                if small.startswith('int') and v >= 1 << (b - 1):
                    v -= 1 << b
                return Ex(str(v), 'i')
            return Ex('int32(%s(%s))' % (small, r.code), 'i')
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
    def array_base(self, base):
        """indexable Go code for the base of a subscript (a fixed array is indexed directly, not decayed)"""
        s = base
        while s.kind in (K.PAREN_EXPR, K.UNEXPOSED_EXPR) and len(kids(s)) == 1:
            ch = kids(s)[0]
            if canon(ch.type).kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
                return self.ex(ch).code
            s = ch
        e = self.ex(base)
        sh = self.shape_of(base) if self.pcat(base.type) else 'slice'
        if sh == 'ptr':
            self.problem(base, 'indexing a pointer that is not an array')
            return 'R.One(%s)' % e.code
        return e.code

    def lv_kind(self, l):
        sl = strip(l)
        if sl.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ix = kids(sl)
            if ptr_category(base.type) == 'char':
                return ('char', self.ex(base).code, self.idx(self.val(ix)))
        if sl.kind == K.UNARY_OPERATOR and unop(sl) == '*':
            a = kids(sl)[0]
            sa = strip(a)
            pc = ptr_category(a.type)
            if pc == 'char':
                if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                    x, y = kids(sa)
                    if ptr_category(x.type) == 'char':
                        i = self.idx(self.val(y))
                        return ('char', self.ex(x).code, i if binop(sa) == '+' else '-(%s)' % i)
                return ('char', self.ex(a).code, '0')
            if pc in PCATS:
                if self.shape_of(a) == 'ptr':
                    return ('ref', self.ex(a).code, ctag(canon(a.type).get_pointee()))
                if sa.kind == K.BINARY_OPERATOR and binop(sa) == '+':
                    x, y = kids(sa)
                    if self.pcat(x.type):
                        return ('plain', '%s[%s]' % (self.paren(self.array_base(x)), self.val(y).code))
                return ('plain', '%s[0]' % self.paren(self.ex(a).code))
        return ('plain', self.lvalue(l))

    def assign_code(self, l, rhs):
        k = self.lv_kind(l)
        if k[0] == 'char':
            return '%s.S(%s, %s)' % (self.paren(k[1]), k[2], rhs)
        if k[0] == 'ref':
            return '*%s = %s' % (self.paren(k[1]), rhs)
        return '%s = %s' % (k[1], rhs)

    def ref_of(self, a):
        k = self.lv_kind(a)
        if k[0] == 'char':
            self.problem(a, 'address of a char element')
            return 'nil'
        if k[0] == 'ref':
            return k[1]
        return '&' + k[1]

    def read_lv(self, a):
        k = self.lv_kind(a)
        if k[0] == 'char':
            return '%s.G(%s)' % (self.paren(k[1]), k[2])
        if k[0] == 'ref':
            return '(*%s)' % self.paren(k[1])
        return k[1]

    def set_expr(self, l, rhs, tg):
        """assignment used as a value"""
        k = self.lv_kind(l)
        if k[0] == 'char':
            return Ex('%s.S(%s, %s)' % (self.paren(k[1]), k[2], rhs), 'i')
        if k[0] == 'ref':
            return Ex('R.Set(%s, %s)' % (k[1], rhs), tg)
        return Ex('R.Set(&%s, %s)' % (k[1], rhs), tg)

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
            if e.tag in ('d', 'f'):
                v = evaluate(strip(a))
                if v is not None and v[0] in ('float', 'int') and v[1] == 0:
                    return Ex('R.NegZero' if e.tag == 'd' else 'float32(R.NegZero)', e.tag)
            if e.tag in ('u', 'ul') and int_lit(e.code) is not None:
                return Ex(str(wrap(-int_lit(e.code), e.tag)), e.tag)
            return Ex('(-%s)' % self.paren(e.code), e.tag)
        if op == '+':
            return e
        if op == '~':
            if e.tag in ('u', 'ul') and int_lit(e.code) is not None:
                return Ex(str(wrap(~int_lit(e.code), e.tag)), e.tag)
            return Ex('(^%s)' % self.paren(e.code), e.tag)
        self.problem(c, 'unary ' + op)
        return e

    def incdec_expr(self, a, op):
        d = '+' if '++' in op else '-'
        tg = ctag(a.type)
        pre = op.startswith('pre')
        k = self.lv_kind(a)
        if k[0] == 'char':
            nv = '%s.S(%s, %s.G(%s) %s 1)' % (self.paren(k[1]), k[2], self.paren(k[1]), k[2], d)
            return Ex(nv if pre else '(%s %s 1)' % (nv, '-' if d == '+' else '+'), 'i')
        p = k[1] if k[0] == 'ref' else '&' + k[1]
        if tg == 'c':
            return Ex('R.C%s(%s, %s1)' % ('Pre' if pre else 'Post', p, '' if d == '+' else '-'), 'c')
        if tg == 'o':
            self.problem(a, 'pointer ++ on a slice')
            return Ex(k[1], 'o')
        return Ex('R.%s%s(%s)' % ('Pre' if pre else 'Post', 'Inc' if d == '+' else 'Dec', p), tg)

    def deref(self, a):
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                x, y = kids(sa)
                if ptr_category(x.type) == 'char':
                    i = self.idx(self.val(y))
                    return Ex('%s.G(%s)' % (self.paren(self.ex(x).code), i if binop(sa) == '+' else '-(%s)' % i), 'i')
            return Ex('%s.G(0)' % self.paren(self.ex(a).code), 'i')
        if cat == 'func':
            return self.ex(a)
        pt = canon(a.type).get_pointee()
        tg = 'rec' if cat == 'record' else ctag(pt)
        if self.shape_of(a) == 'ptr':
            return Ex('(*%s)' % self.paren(self.ex(a).code), tg)
        if sa.kind == K.BINARY_OPERATOR and binop(sa) == '+':
            x, y = kids(sa)
            if self.pcat(x.type):
                return Ex('%s[%s]' % (self.paren(self.array_base(x)), self.val(y).code), tg)
        return Ex('%s[0]' % self.paren(self.ex(a).code), tg)

    def addr_of(self, a, c):
        sa = strip(a)
        if canon(sa.type).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return self.ex(sa)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ix = kids(sa)
            if ptr_category(base.type) == 'char':
                b = self.ex(base).code
                i = self.idx(self.val(ix))
                return Ex(b if i == '0' else '%s.Add(%s)' % (self.paren(b), i), 'c')
        if ptr_category(c.type) in PCATS:
            return Ex(self.ptr_val(c, 'ptr'), 'o')
        if ctag(sa.type) == 'c' and canon(sa.type).kind == T.CONSTANTARRAY:
            return self.ex(sa)
        return Ex(self.ref_of(sa), 'o')

    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            if ctag(l.type) == 'rec':
                return self.set_expr(l, self.ex(r).code, 'rec')
            return self.set_expr(l, self.value_for(r, l.type, self.want_lv(l)), ctag(l.type))
        if op in ('&&', '||'):
            return Ex('(%s %s %s)' % (self.paren(self.cond(l)), op, self.paren(self.cond(r))), 'b')
        if op == ',':
            gt = self.expr_gtype(c)
            body = self.expr_stmts(l)
            return Ex('(func() %s { %s; return %s }())' % (gt, '; '.join(body), self.val(r).code), ctag(c.type))
        lt, rt = canon(l.type), canon(r.type)
        if op in ('==', '!=', '<', '>', '<=', '>=') and (lt.kind in (T.POINTER, T.CONSTANTARRAY) or
                                                          rt.kind in (T.POINTER, T.CONSTANTARRAY)):
            return self.ptr_compare(c, op, l, r)
        le, re_ = self.val(l), self.val(r)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
        tg = ctag(c.type)
        if tg == 'c':
            if op == '+':
                if ptr_category(l.type) == 'char':
                    return Ex('%s.Add(%s)' % (self.paren(le.code), self.idx(re_)), 'c')
                return Ex('%s.Add(%s)' % (self.paren(re_.code), self.idx(le)), 'c')
            return Ex('%s.Add(-%s)' % (self.paren(le.code), self.paren(self.idx(re_))), 'c')
        if lt.kind in (T.POINTER, T.CONSTANTARRAY) and rt.kind in (T.POINTER, T.CONSTANTARRAY) and op == '-':
            if ptr_category(l.type) == 'char':
                return Ex('int64(%s.O - %s.O)' % (self.paren(le.code), self.paren(re_.code)), 'l')
            self.problem(c, 'difference of non-char pointers')
            return Ex('0', 'l')
        if tg == 'o':
            p, n = (l, r) if self.pcat(l.type) else (r, l)
            if op == '+':
                return Ex('%s[%s:]' % (self.paren(self.array_base(p)), self.val(n).code), 'o')
            self.problem(c, 'pointer minus integer')
            return Ex(le.code, 'o')
        return Ex(self.arith(op, le.code, re_.code, tg), tg)

    def ptr_compare(self, c, op, l, r):
        nl, nr = self.is_null_c(l), self.is_null_c(r)
        cat = ptr_category(l.type) or ptr_category(r.type)
        if nl or nr:
            x = r if nl else l
            if op not in ('==', '!='):
                self.problem(c, 'pointer order against NULL')
            if ptr_category(x.type) == 'char':
                return Ex(('%s.IsNull()' if op == '==' else '!%s.IsNull()') % self.paren(self.ex(x).code), 'b')
            if self.pcat(x.type):
                return Ex('(%s %s nil)' % (self.ptr_val(x, self.shape_of(x)), op), 'b')
            return Ex('(%s %s nil)' % (self.ex(x).code, op), 'b')
        le, re_ = self.ex(l), self.ex(r)
        if cat == 'char':
            if op in ('==', '!='):
                return Ex('%sR.Peq(%s, %s)' % ('' if op == '==' else '!', le.code, re_.code), 'b')
            return Ex('(%s.O %s %s.O)' % (self.paren(le.code), op, self.paren(re_.code)), 'b')
        if self.pcat(l.type):
            sl, sr = self.shape_of(l), self.shape_of(r)
            if sl == 'ptr' and sr == 'ptr' and op in ('==', '!='):
                return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
            if op in ('==', '!='):
                return Ex('%sR.SameAddr(%s, %s)' % ('' if op == '==' else '!', self.ptr_val(l, 'slice'), self.ptr_val(r, 'slice')), 'b')
            self.problem(c, 'pointer order comparison')
        return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')

    def arith(self, op, a, b, tg, rnode=None):
        if tg in ('d', 'f'):
            if op in ('+', '-', '*', '/'):
                return '%s(%s %s %s)' % (GT[tg], a, op, b)
            return '(%s %s %s)' % (a, op, b)
        if op in ('<<', '>>') and int_lit(a) is not None:
            a = '%s(%s)' % (GT.get(tg, 'int32'), a)
        return '(%s %s %s)' % (a, op, b)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        l, r = kids(c)
        lt = ctag(l.type)
        v = self.compound_value(c)
        if v is None:   # pointer arithmetic
            return Ex('R.Set(%s, %s)' % (self.ref_of(l), self.compound_ptr(c)), lt)
        return self.set_expr(l, v, lt)

    def compound_ptr(self, c):
        op = binop(c)[:-1]
        l, r = kids(c)
        re_ = self.val(r)
        cur = self.read_lv(l)
        if ctag(l.type) == 'c':
            return '%s.Add(%s%s)' % (self.paren(cur), '' if op == '+' else '-', self.paren(self.idx(re_)))
        if op == '+':
            return '%s[%s:]' % (self.paren(cur), re_.code)
        self.problem(c, 'pointer -= on a slice')
        return cur

    def compound_value(self, c):
        """new value of the left side of a compound assignment (None for pointer arithmetic)"""
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        if lt in ('c', 'o'):
            return None
        re_ = self.val(r)
        if op in ('<<', '>>'):
            common = lt
        else:
            order = ['d', 'f', 'ul', 'l', 'u', 'i']
            common = next(t for t in order if t in (lt, rt))
            if common == 'u' and 'l' in (lt, rt):
                common = 'l'
        cur = Ex(self.read_lv(l), lt)
        a = self.conv_tags(cur, lt, common).code
        b = re_.code if op in ('<<', '>>') else self.conv_tags(re_, rt, common).code
        v = Ex(self.arith(op, a, self.paren(b), common), common)
        return self.conv_tags(v, common, lt).code

    def compound_code(self, c):
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        v = self.compound_value(c)
        if v is None:
            k = self.lv_kind(l)
            return '%s = %s' % (k[1] if k[0] == 'plain' else '*' + self.paren(k[1]), self.compound_ptr(c))
        k = self.lv_kind(l)
        if k[0] == 'plain' and lt == rt and lt in INTTAGS and op in ('+', '-', '*', '/', '%', '&', '|', '^'):
            return '%s %s= %s' % (k[1], op, self.paren(self.val(r).code))
        if k[0] == 'plain' and lt in INTTAGS and op in ('<<', '>>'):
            return '%s %s= %s' % (k[1], op, self.paren(self.val(r).code))
        return self.assign_code(l, v)

    # ---------------------------------------------------------------- ?:
    def safe(self, c):
        """True if evaluating C expression c eagerly can neither fail nor have side effects"""
        s = c
        k = s.kind
        if k in (K.INTEGER_LITERAL, K.FLOATING_LITERAL, K.CHARACTER_LITERAL):
            return True
        if k in (K.PAREN_EXPR, K.UNEXPOSED_EXPR, K.CSTYLE_CAST_EXPR):
            ch = kids(s)
            if len(ch) != 1 and k != K.CSTYLE_CAST_EXPR:
                return False
            x = ch[-1]
            if canon(x.type).kind == T.CONSTANTARRAY:
                return False
            return self.safe(x)
        if k == K.DECL_REF_EXPR:
            d = s.referenced
            return d is not None and (d.kind == K.ENUM_CONSTANT_DECL or
                                      (d.kind in (K.VAR_DECL, K.PARM_DECL) and ctag(d.type) in NUMTAGS))
        if k == K.UNARY_OPERATOR:
            return unop(s) in ('-', '+', '!', '~') and self.safe(kids(s)[0])
        if k == K.BINARY_OPERATOR:
            op = binop(s)
            l, r = kids(s)
            if op in ('/', '%') and ctag(s.type) not in ('d', 'f'):
                return False
            if op in ('=', ','):
                return False
            if ctag(l.type) not in NUMTAGS or ctag(r.type) not in NUMTAGS:
                return False
            return self.safe(l) and self.safe(r)
        if k == K.CALL_EXPR and s.spelling in ('fabs',) and s.referenced is not None and \
                self.func_def(s.referenced, self.cur_file) is None:
            return all(self.safe(a) for a in s.get_arguments())
        return False

    def ternary_code(self, cond, a, b, gt, ca=None, cb=None):
        if ca is not None and cb is not None and self.safe(ca) and self.safe(cb) and gt in GT.values():
            return 'R.If[%s](%s, %s, %s)' % (gt, cond, a, b)
        return '(func() %s { if %s { return %s }; return %s }())' % (gt, cond, a, b)

    def expr_gtype(self, c):
        t = c.type
        tg = ctag(t)
        if tg in GT:
            return GT[tg]
        if tg == 'rec':
            return self.rec(t)
        if self.pcat(t):
            sh = self.shape_of(c)
            if sh == 'ptr':
                return self.gtype(t, mode='obj' if ptr_category(t) == 'record' else 'ref')
            return self.gtype(t, mode='array')
        return self.gtype(t)

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        tg = ctag(c.type)
        if self.pcat(c.type):
            return Ex(self.ptr_val(c, self.shape_of(c)), 'o')
        if tg == 'rec':
            ea, eb = self.ex(a), self.ex(b)
        else:
            ea = self.conv(self.val(a), a.type, c.type)
            eb = self.conv(self.val(b), b.type, c.type)
        return Ex(self.ternary_code(self.cond(cc), ea.code, eb.code, self.expr_gtype(c), a, b), tg)

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, ix = kids(c)
        if ptr_category(base.type) == 'char':
            return Ex('%s.G(%s)' % (self.paren(self.ex(base).code), self.idx(self.val(ix))), 'i')
        b = self.array_base(base)
        return Ex('%s[%s]' % (self.paren(b), self.val(ix).code), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        f = c.referenced
        fn = self.field(f.spelling)
        if canon(base.type).kind == T.POINTER:
            b = self.ex(base).code
            if self.shape_of(base) == 'slice':
                b = '%s[0]' % self.paren(b)
            code = '%s.%s' % (self.paren(b), fn)
        else:
            code = '%s.%s' % (self.paren(self.ex(base).code), fn)
        ft = canon(f.type)
        if ft.kind == T.CONSTANTARRAY and ctag(ft) == 'c':
            return Ex('R.CP(%s[:])' % code, 'c')
        return Ex(code, ctag(c.type))

    # ================================================================== init lists
    def init_list(self, c, t, field=False):
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
                return Ex('R.BufOf(%d, %s)' % (n, ', '.join(self.val(it).code for it in items)), 'c')
            vals = []
            for it in items:
                if strip(it).kind == K.INIT_LIST_EXPR:
                    vals.append(self.init_list(strip(it), et).code)
                elif ctag(et) == 'c' and strip(it).kind == K.STRING_LITERAL and et.kind == T.CONSTANTARRAY:
                    vals.append('R.BufFrom(%s, %d)' % (self.lit(self.string_bytes(strip(it))), et.element_count))
                elif self.pcat(et):
                    vals.append(self.ptr_val(it, self.natural_shape(et)))
                else:
                    vals.append(self.conv(self.val(it), it.type, et).code)
            if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
                while len(vals) < n:
                    vals.append('R.Buf(%d)' % et.element_count)
                return Ex('[]R.CPtr{%s}' % ', '.join(vals), 'o')
            ety = self.fixed_type(t, field)
            ety = ety[ety.index(']') + 1:]
            return Ex('[%d]%s{%s}' % (n, ety, ', '.join(vals)), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                if strip(it).kind == K.INIT_LIST_EXPR:
                    parts.append('%s: %s' % (self.field(f.spelling), self.init_list(strip(it), f.type, True).code))
                else:
                    parts.append('%s: %s' % (self.field(f.spelling), self.value_for(it, f.type, self.want_of(f))))
            return Ex('%s{%s}' % (self.rec(t), ', '.join(parts)), 'rec')
        if len(items) == 1:
            return self.val(items[0])
        self.problem(c, 'init list for %s' % t.spelling)
        return Ex('nil', '?')

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
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    # &c (a char variable) passed as a string: a two-byte buffer, copied back after the call
                    o = kids(sa)[0]
                    t = self.temp('__c', 'R.CPtr')
                    self.pre.append('%s = R.Buf(2)' % t)
                    self.pre.append('%s.S(0, %s)' % (t, self.read_lv(o)))
                    self.post.append(self.assign_code(o, '%s.G(0)' % t))
                    codes.append(t)
                    continue
                codes.append(self.arg(a, p))
            return Ex('%s(%s)' % (n, ', '.join(codes)), ctag(c.type))
        fe = self.ex(callee)
        dname = self.delegate(canon(strip(callee).type)) if canon(strip(callee).type).kind == T.POINTER else None
        ft = canon(canon(strip(callee).type).get_pointee()) if dname else None
        argcodes = []
        for i, a in enumerate(args):
            sa = strip(a)
            pt = canon(list(ft.argument_types())[i]) if ft is not None else canon(a.type)
            if ptr_category(pt) == 'scalar':
                isref = self.delegate_ref.get((dname, i))
                if isref is None:
                    isref = (sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and
                             strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR) or self.shape_of(a) == 'ptr'
                    if self.bound_param_mode(ft, i) == 'array':
                        isref = False
                    self.delegate_ref[(dname, i)] = isref
                argcodes.append(self.ptr_val(a, 'ptr' if isref else 'slice'))
            elif self.pcat(pt):
                argcodes.append(self.ptr_val(a, self.natural_shape(pt)))
            else:
                argcodes.append(self.conv(self.val(a), a.type, pt).code)
        return Ex('%s(%s)' % (self.paren(fe.code), ', '.join(argcodes)), ctag(c.type))

    def temp(self, prefix, gt):
        self.tmp += 1
        n = '%s%d' % (prefix, self.tmp)
        self.hoisted.append((n, gt))
        return n

    def arg(self, a, p):
        cat = ptr_category(p.type)
        if cat in PCATS:
            return self.ptr_val(a, self.want_of(p) if canon(p.type).kind != T.CONSTANTARRAY else 'slice')
        e = self.conv(self.val(a), a.type, p.type)
        if cat == 'char' and (is_gnull(e.code) or int_lit(e.code) == 0):
            return NULLC
        if cat in ('void', 'func', 'file') and (is_gnull(e.code) or int_lit(e.code) == 0):
            return 'nil'
        return e.code

    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name in MATH:
            return Ex('%s(%s)' % (MATH[name], A(0)), 'd')
        if name == 'pow':
            return Ex('M.Pow(%s, %s)' % (A(0), A(1)), 'd')
        if name in ('fprintf', 'snprintf', 'sscanf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}[name]
            head = [A(i) for i in range(fixed)]
            rest = [self.vararg(a, name == 'sscanf') for a in args[fixed:]]
            return Ex('R.%s(%s)' % (name.capitalize(), ', '.join(head + rest)), 'i')
        if name == 'free':
            return Ex('R.Free(%s)' % self.ex(self.nv(args[0])).code, 'v')
        if name in ('calloc', 'malloc', 'realloc'):
            return self.alloc(c, c.type)
        if name in ('fwrite', 'fread'):
            return self.freadwrite(c, name, args)
        if name == 'memset':
            args = [self.nv(args[0])] + args[1:]
            dst = strip(args[0])
            if dst.kind == K.UNARY_OPERATOR and unop(dst) == '&' and ctag(strip(kids(dst)[0]).type) == 'rec':
                o = strip(kids(dst)[0])
                return Ex('%s = %s' % (self.lvalue(o), self.gzero(self.rec(o.type))), 'v')
            if ptr_category(args[0].type) == 'char':
                return Ex('R.MemsetC(%s, %s, %s)' % (A(0), A(1), A(2)), 'v')
            return Ex('R.Memset(%s, %s, %s)' % (self.ptr_val(args[0], 'slice'), A(1), A(2)), 'v')
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return Ex('R.Strtod(%s, %s)' % (A(0), self.ref_of(kids(ep)[0])), 'd')
            return Ex('R.Strtod(%s, nil)' % A(0), 'd')
        if name == 'time':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                return Ex('R.Set(%s, R.Time())' % self.ref_of(kids(a0)[0]), 'l')
            return Ex('R.Time()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('R.Ctime(%s)' % (self.read_lv(kids(a0)[0]) if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('float64(%s - %s)' % (A(0), A(1)), 'd')
        if name in LIBC:
            return Ex('R.%s(%s)' % (LIBC[name], ', '.join(A(i) for i in range(len(args)))), LIBC_TAG.get(name, tg))
        self.problem(c, 'libc ' + name)
        return Ex('R.%s(%s)' % (name.capitalize(), ', '.join(A(i) for i in range(len(args)))), tg)

    def vararg(self, a, scanf):
        sa = strip(a)
        if scanf:
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return self.ref_of(kids(sa)[0])
            if ptr_category(a.type) == 'scalar':
                return self.ptr_val(a, 'ptr')
            return self.val(a).code
        e = self.val(a)
        return e.code

    def alloc(self, call, t, want=None):
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
            old = self.ex(args[0]).code
            if ctag(t) == 'c':
                return Ex('R.ReallocC(%s, %s)' % (old, n), 'c')
            return Ex('R.Realloc(%s, %s)' % (old, n), 'o')
        if ctag(t) == 'c':
            return Ex('R.Buf(%s)' % n, 'c')
        if want is None:
            want = self.alloc_shape(call, t)
        if want == 'ptr':
            return Ex('new(%s)' % self.gtype(et, mode='obj' if ptr_category(et) == 'record' else 'array'), 'o')
        return Ex('make(%s, %s)' % (self.gtype(t, mode='array'), n), 'o')

    def int_code(self, x):
        e = self.val(x)
        if e.tag in ('ul', 'l', 'u'):
            v = int_lit(e.code)
            return str(v) if v is not None else 'int(%s)' % e.code
        v = int_lit(e.code)
        return str(v) if v is not None else 'int(%s)' % e.code

    def nv(self, c):
        """c without its implicit conversion to void*"""
        s = c
        while s.kind in (K.UNEXPOSED_EXPR, K.PAREN_EXPR) and len(kids(s)) == 1 and ptr_category(s.type) == 'void' \
                and ptr_category(kids(s)[0].type) != 'void':
            s = kids(s)[0]
        return s

    def freadwrite(self, c, name, args):
        buf, size, cnt, f = args
        buf = self.nv(buf)
        sb = strip(buf)
        fc = self.val(f).code
        sz = evaluate(strip(size))
        sz = sz[1] if sz and sz[0] == 'int' else None
        n = self.val(cnt).code
        W = name == 'fwrite'
        if sb.kind == K.UNARY_OPERATOR and unop(sb) == '&':
            o = strip(kids(sb)[0])
            if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                base, ix = kids(o)
                if ptr_category(base.type) == 'char':
                    return Ex('R.%sC(%s.Add(%s), %s, %s)' % ('Fwrite' if W else 'Fread', self.paren(self.ex(base).code),
                                                           self.idx(self.val(ix)), n, fc), 'ul')
                return Ex('R.%s(%s[%s:], %s, %s)' % ('Fwrite' if W else 'Fread', self.paren(self.array_base(base)),
                                                     self.val(ix).code, n, fc), 'ul')
            nat = self.sizeof_type(o.type)
            if W:
                return Ex('R.Fwrite1(%s, %d, %s)' % (self.read_lv(o), sz or nat, fc), 'ul')
            return Ex('R.Fread1(%s, %d, %s)' % (self.ref_of(o), sz or nat, fc), 'ul')
        if ptr_category(buf.type) == 'char':
            return Ex('R.%sC(%s, %s, %s)' % ('Fwrite' if W else 'Fread', self.val(buf).code, n, fc), 'ul')
        if self.shape_of(buf) == 'ptr':
            et = canon(canon(sb.type).get_pointee())
            nat = self.sizeof_type(et)
            p = self.ex(buf).code
            if W:
                return Ex('R.Fwrite1(*%s, %d, %s)' % (self.paren(p), sz or nat, fc), 'ul')
            return Ex('R.Fread1(%s, %d, %s)' % (p, sz or nat, fc), 'ul')
        return Ex('R.%s(%s, %s, %s)' % ('Fwrite' if W else 'Fread', self.ptr_val(buf, 'slice'), n, fc), 'ul')

    # ================================================================== statements
    def stmt(self, c, ind):
        k = c.kind
        p = '\t' * ind
        if k == K.COMPOUND_STMT:
            out = [p + '{']
            for ch in kids(c):
                out += self.stmt(ch, ind + 1)
            out.append(p + '}')
            return out
        if k == K.DECL_STMT:
            out = []
            for d in kids(c):
                out += self.flush(self.local_decl(d, ind), ind)
            return out
        if k == K.IF_STMT:
            return self.if_stmt(c, ind)
        if k == K.WHILE_STMT:
            ch = kids(c)
            cond = self.cond(ch[0])
            pre, post = self.take()
            if pre or post:
                return [p + 'for {'] + [p + '\t' + x for x in pre] + \
                       [p + '\t' + '%s = %s' % (self.temp('__b', 'bool'), cond)] + \
                       [p + '\t' + x for x in post] + [p + '\tif !__b%d {' % self.tmp, p + '\t\tbreak', p + '\t}'] + \
                       self.body(ch[1], ind + 1) + [p + '}']
            return [p + 'for %s {' % self.hdr(cond)] + self.body(ch[1], ind + 1) + [p + '}']
        if k == K.DO_STMT:
            ch = kids(c)
            body = self.body(ch[0], ind + 1)
            cond = self.cond(ch[1])
            pre, post = self.take()
            if pre or post:
                self.problem(c, 'call set-up in a do-while condition')
            self.tmp += 1
            v = '__dw%d' % self.tmp
            return [p + 'for %s := true; %s || %s; %s = false {' % (v, v, self.paren(cond), v)] + body + [p + '}']
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            return [p + 'break']
        if k == K.CONTINUE_STMT:
            return [p + 'continue']
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'return']
            return self.return_stmt(ch[0], ind)
        if k == K.NULL_STMT:
            return []
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unhandled statement %s' % k.name)
            return []
        return self.flush([p + x for x in self.expr_stmts(c)], ind)

    def hdr(self, cond):
        """a condition in an if/for/switch header"""
        return cond

    def take(self):
        pre, post = self.pre, self.post
        self.pre, self.post = [], []
        return pre, post

    def flush(self, lines, ind):
        """put the set-up and copy-back statements of call arguments around a statement"""
        pre, post = self.take()
        if not pre and not post:
            return lines
        p = '\t' * ind
        if post and any(l.strip().startswith(('return', 'if', 'for', 'switch')) for l in lines):
            self.problems.append('copy-back after %s' % lines[0].strip())
        return [p + x for x in pre] + lines + [p + x for x in post]

    def body(self, c, ind):
        """statements of a block, without the braces"""
        if c.kind == K.COMPOUND_STMT:
            out = []
            for ch in kids(c):
                out += self.stmt(ch, ind)
            return out
        return self.stmt(c, ind)

    def if_stmt(self, c, ind):
        p = '\t' * ind
        ch = kids(c)
        cond = self.cond(ch[0])
        pre, post = self.take()
        out = [p + x for x in pre]
        if post:
            t = self.temp('__b', 'bool')
            out += [p + '%s = %s' % (t, cond)] + [p + x for x in post]
            cond = t
        out.append(p + 'if %s {' % cond)
        out += self.body(ch[1], ind + 1)
        if len(ch) > 2:
            if ch[2].kind == K.IF_STMT:
                sub = self.if_stmt(ch[2], ind)
                if sub[0].lstrip().startswith('if '):
                    out.append(p + '} else ' + sub[0].lstrip())
                    out += sub[1:]
                    return out
                out.append(p + '} else {')
                out += ['\t' + x for x in sub]
            else:
                out.append(p + '} else {')
                out += self.body(ch[2], ind + 1)
        out.append(p + '}')
        return out

    def cond_chain(self, r):
        """(conditional cursor, [C types it is converted through]) if r is a ?: under casts, else (None, None)"""
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
            if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) in NUMTAGS:
                types.append(s.type)
                s = kids(s)[-1]
                continue
            break
        if s.kind == K.CONDITIONAL_OPERATOR:
            return s, list(reversed(types))
        return None, None

    def branch_value(self, b, cnode, types, lt, want):
        """value of one ?: branch converted like C: to the ?: type, through the casts, to lt"""
        cc, chain = self.cond_chain(b)
        if self.pcat(lt) and canon(lt).kind != T.CONSTANTARRAY:
            return self.ptr_val(b, want)
        if ctag(lt) == 'rec':
            return self.ex(b).code
        e = self.conv(self.val(b), b.type, cnode.type)
        prev = cnode.type
        for t in types:
            e = self.conv(e, prev, t)
            prev = t
        return self.conv(e, prev, lt).code

    def assign_stmts(self, l, r, target=None):
        """statements for l = r (target: Go lvalue code for a hoisted local, else derived from l)"""
        cnode, types = self.cond_chain(r)
        lt = l.type if target is None else target[1]
        want = (self.want_lv(l) if target is None else target[2])
        if cnode is not None and not (self.pcat(lt) and self.is_null_c(r)):
            cc, a, b = kids(cnode)
            cond = self.cond(cc)
            sa = self.branch_assign(l, a, cnode, types, lt, want, target)
            sb = self.branch_assign(l, b, cnode, types, lt, want, target)
            return ['if %s {' % cond] + ['\t' + x for x in sa] + ['} else {'] + ['\t' + x for x in sb] + ['}']
        rhs = self.value_for(r, lt, want)
        if target is not None:
            return ['%s = %s' % (target[0], rhs)]
        return [self.assign_code(l, rhs)]

    def branch_assign(self, l, b, cnode, types, lt, want, target):
        c2, t2 = self.cond_chain(b)
        if c2 is not None and not types:
            return self.assign_stmts(l, b, target)
        v = self.branch_value(b, cnode, types, lt, want)
        if target is not None:
            return ['%s = %s' % (target[0], v)]
        return [self.assign_code(l, v)]

    def want_lv(self, l):
        """Go shape wanted by the pointer-typed lvalue l"""
        if not self.pcat(l.type):
            return None
        sl = strip(l)
        if sl.kind in (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR) and sl.referenced is not None and \
                sl.referenced.kind in (K.VAR_DECL, K.PARM_DECL, K.FIELD_DECL):
            return self.want_of(sl.referenced)
        return self.natural_shape(l.type)

    def return_stmt(self, e, ind):
        p = '\t' * ind
        rt = self.cur_ret
        cnode, types = self.cond_chain(e)
        want = self.want_of_type(self.gtype(rt)) if self.pcat(rt) else None
        if cnode is not None and not (self.pcat(rt) and self.is_null_c(e)):
            cc, a, b = kids(cnode)
            cond = self.cond(cc)
            pre, post = self.take()
            va = self.branch_value(a, cnode, types, rt, want)
            vb = self.branch_value(b, cnode, types, rt, want)
            pre2, post2 = self.take()
            if post or post2:
                self.problem(e, 'copy-back in a returned ?:')
            out = [p + x for x in pre] + [p + 'if %s {' % cond] + [p + '\t' + x for x in pre2] + \
                  [p + '\treturn ' + va, p + '}']
            return out + [p + 'return ' + vb]
        v = self.value_for(e, rt, want)
        pre, post = self.take()
        if post:
            t = self.temp('__r', self.gtype(rt))
            return [p + x for x in pre] + [p + '%s = %s' % (t, v)] + [p + x for x in post] + [p + 'return ' + t]
        return [p + x for x in pre] + [p + 'return ' + v]

    def expr_stmts(self, c):
        """Go statements for a C expression statement"""
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) == 'v':
            return self.expr_stmts(kids(s)[-1])
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            if ctag(l.type) == 'rec':
                return [self.assign_code(l, self.ex(r).code)]
            return self.assign_stmts(l, r)
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmts(l) + self.expr_stmts(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            return [self.compound_code(s)]
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            d = '+' if '++' in unop(s) else '-'
            k = self.lv_kind(a)
            if k[0] == 'char':
                return ['%s.S(%s, %s.G(%s) %s 1)' % (self.paren(k[1]), k[2], self.paren(k[1]), k[2], d)]
            if k[0] == 'ref':
                return ['(*%s)%s%s' % (self.paren(k[1]), d, d)]
            tg = ctag(a.type)
            if tg == 'c':
                return ['%s = %s.Add(%s1)' % (k[1], self.paren(k[1]), '' if d == '+' else '-')]
            if tg == 'o':
                if d == '+':
                    return ['%s = %s[1:]' % (k[1], self.paren(k[1]))]
                self.problem(a, 'pointer -- on a slice')
            return ['%s%s%s' % (k[1], d, d)]
        if s.kind == K.CONDITIONAL_OPERATOR:
            cc, a, b = kids(s)
            return ['if %s {' % self.cond(cc)] + ['\t' + x for x in self.expr_stmts(a)] + ['} else {'] + \
                   ['\t' + x for x in self.expr_stmts(b)] + ['}']
        e = self.ex(c)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        if s.kind == K.CALL_EXPR and not re.match(r'^(int32|int64|uint32|uint64|float64|float32)\(', code):
            if code.startswith('R.Free('):
                return ['_ = ' + code[7:-1]]
            return [code]
        if re.match(r'^[\w.\[\]()*]+ = ', code):
            return [code]
        if code.startswith(('R.Set(', 'R.Pre', 'R.Post', 'R.CPre', 'R.CPost')) or re.match(r'^[\w.\[\]()]+\.S\(', code):
            return [code]
        return ['_ = ' + code]

    def for_stmt(self, c, ind):
        p = '\t' * ind
        ch = kids(c)
        body = ch[-1]
        parts = ch[:-1]
        toks = list(c.get_tokens())
        depth = 0
        semis = []
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
        out = []
        init_s = []
        if init is not None:
            if init.kind == K.DECL_STMT:
                for d in kids(init):
                    init_s += [l.strip() for l in self.local_decl(d, 0)]
            else:
                init_s = self.expr_stmts(init)
        pre, post = self.take()
        if pre or post:
            init_s = pre + init_s + post
        cond_s = self.cond(cond) if cond is not None else ''
        pre, post = self.take()
        if pre or post:
            self.problem(c, 'call set-up in a for condition')
        inc_s = self.expr_stmts(inc) if inc is not None else []
        pre, post = self.take()
        if pre or post:
            inc_s = pre + inc_s + post
        simple = lambda xs: len(xs) == 1 and '\n' not in xs[0] and not xs[0].startswith(('if ', '}'))
        if init_s and not simple(init_s):
            out += [p + x for x in init_s]
            init_s = []
        if len(inc_s) > 1 or (inc_s and not simple(inc_s)):
            inc_s = ['func() { %s }()' % '; '.join(inc_s)] if all(simple([x]) for x in inc_s) else None
            if inc_s is None:
                self.problem(c, 'complex for increment')
                inc_s = []
        i0 = init_s[0] if init_s else ''
        n0 = inc_s[0] if inc_s else ''
        if not i0 and not n0:
            head = 'for %s {' % cond_s if cond_s else 'for {'
        else:
            head = 'for %s; %s; %s {' % (i0, cond_s, n0)
        return out + [p + head] + self.body(body, ind + 1) + [p + '}']

    def switch(self, c, ind):
        p = '\t' * ind
        ch = kids(c)
        e = self.val(ch[0])
        code = e.code if e.tag != 'b' else 'R.B2I(%s)' % e.code
        out = self.flush([], ind)
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
                        labels.append(self.val(xc[0]).code)
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
        out.append(p + 'switch %s {' % code)
        for si, (labels, stmts) in enumerate(sections):
            cases = [x for x in labels if x is not None]
            has_default = None in labels
            if cases and has_default:
                out.append(p + 'case %s:' % ', '.join(cases))
                out.append(p + '\tfallthrough')
                out.append(p + 'default:')
            elif has_default:
                out.append(p + 'default:')
            else:
                out.append(p + 'case %s:' % ', '.join(cases))
            for s in stmts:
                out += self.stmt(s, ind + 1)
            if not self.terminates(stmts) and si + 1 < len(sections):
                out.append(p + '\tfallthrough')
        out.append(p + '}')
        return out

    def local_decl(self, d, ind):
        p = '\t' * ind
        if d.kind != K.VAR_DECL:
            return []
        if d.storage_class == front.ci.StorageClass.EXTERN:
            return []
        if d.storage_class == front.ci.StorageClass.STATIC:
            self.static_locals.append((d, self.cur_file))
            return []
        name = self.declare_local(d)
        gt = self.gtype(d.type, d)
        self.hoisted.append((name, gt))
        init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        t = canon(d.type)
        if t.kind == T.CONSTANTARRAY:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return [p + '%s = %s' % (name, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return [p + '%s = R.BufFrom(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return [p + '%s = R.Buf(%d)' % (name, t.element_count)]
            return [p + '%s = %s' % (name, self.new_array(t))]
        if not init:
            return [p + '%s = %s' % (name, self.gzero(gt))]
        return [p + x for x in self.assign_stmts(None, init[-1], (name, d.type, self.want_of(d)))]

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return 'R.Bufs(%d, %d)' % (t.element_count, et.element_count)
        return self.gzero(self.fixed_type(t))

    # ================================================================== functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.cur_ret = c.result_type
        self.tmp = 0
        self.hoisted = []
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        ps = []
        for prm in params:
            nm = self.declare_local(prm)
            ps.append('%s %s' % (nm, self.gtype(prm.type, prm)))
        lines = self.body(body, 1)
        rt = self.gtype(c.result_type)
        out = ['// %s:%d' % (b, c.location.line), 'func %s(%s)%s {' % (self.fname[key], ', '.join(ps), (' ' + rt) if rt else '')]
        if self.hoisted:
            seen = set()
            hv = [(nm, gt) for nm, gt in self.hoisted if not (nm in seen or seen.add(nm))]
            out.append('\tvar (')
            out += ['\t\t%s %s' % (nm, gt) for nm, gt in hv]
            out.append('\t)')
            for i in range(0, len(hv), 12):
                chunk = [nm for nm, _ in hv[i:i + 12]]
                out.append('\t%s = %s' % (', '.join('_' for _ in chunk), ', '.join(chunk)))
        out += lines
        if rt and not (lines and lines[-1].strip().startswith('return ')):
            out.append('\treturn %s' % self.gzero(rt))
        out.append('}')
        return out

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        out = ['type %s struct {' % self.recname.get(name, gid(name))]
        for f in fields:
            out.append('\t%s %s' % (self.field(f.spelling), self.gtype(f.type, f, field=True)))
        out.append('}')
        return out + ['']

    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        self.locals = {}
        self.hoisted = []
        self.tmp = 0
        t = canon(c.type)
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        return self.var_decl(name, c, t, init)

    def var_decl(self, name, d, t, init):
        gt = self.gtype(d.type, d)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return 'var %s = %s' % (name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return 'var %s = R.BufFrom(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return 'var %s = R.Buf(%d)' % (name, t.element_count)
            if ctag(canon(t.element_type)) == 'c' and canon(t.element_type).kind == T.CONSTANTARRAY:
                return 'var %s = %s' % (name, self.new_array(t))
            return 'var %s %s' % (name, gt)
        if not init:
            return 'var %s %s' % (name, gt)
        if t.kind == T.RECORD and strip(init[-1]).kind == K.INIT_LIST_EXPR:
            return 'var %s = %s' % (name, self.init_list(strip(init[-1]), t).code)
        return 'var %s %s = %s' % (name, gt, self.value_for(init[-1], d.type, self.want_of(d)))

    def delegate_decl_auto(self, name, ft):
        ps = []
        for i, a in enumerate(ft.argument_types()):
            a = canon(a)
            cat = ptr_category(a)
            if cat == 'scalar':
                isref = self.delegate_ref.get((name, i))
                if isref is None:
                    isref = self.bound_param_mode(ft, i) == 'ref'
                ps.append(('*' if isref else '[]') + GT[ctag(canon(a.get_pointee()))])
            else:
                ps.append(self.gtype(a, mode='obj' if cat == 'record' else None))
        rt = self.gtype(ft.get_result())
        return 'type %s func(%s)%s' % (name, ', '.join(ps), (' ' + rt) if rt else '')

    @staticmethod
    def file_text(header, body):
        text = '\n'.join(body)
        code = re.sub(r'"(?:[^"\\]|\\.)*"', '""', text)
        imports = []
        if re.search(r'\bR\.', code):
            imports.append('R "swmm5go/crt"')
        if re.search(r'\bM\.', code):
            imports.append('M "swmm5go/glibm"')
        out = header + ['', 'package main', '']
        if imports:
            out += ['import ('] + ['\t' + x for x in imports] + [')', '']
        return '\n'.join(out) + text + '\n'

    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        for f in os.listdir(outdir):
            if f.startswith('f_') and f.endswith('.go') or f in ('types.go', 'consts.go'):
                os.remove(os.path.join(outdir, f))
        self.delegate_ref = {}
        self.static_locals = []
        self.cur_file = None
        self.tmp = 0
        self.hoisted = []
        files = collections.defaultdict(list)
        for key, c in self.F.funcs.items():
            if key[0] in SKIP_FILES or key in OVERRIDES:
                continue
            try:
                files[key[0]] += self.function(key, c) + ['']
            except Exception as ex:
                import traceback
                traceback.print_exc()
                self.problems.append('%s:%s CRASH %s' % (key[0], key[1], ex))
        glob = collections.defaultdict(list)
        for k, c in self.F.globals.items():
            b = self.F.global_owner[k]
            if b in SKIP_FILES:
                continue
            glob[b].append(self.global_decl(k, c))
        for d, b in self.static_locals:
            self.cur_file = b
            self.locals = {}
            t = canon(d.type)
            init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
            glob[b].append(self.var_decl(self.static_local_name(d), d, t, init))
        hdr = lambda b: ['// Generated from EPA SWMM 5.2.4 (%s) by tools/c2x/emit_go.py. Do not edit by hand;' % b,
                         '// fix the translator, go/crt or overrides.go instead.']
        for b in sorted(set(files) | set(glob)):
            body = glob.get(b, []) + ([''] if glob.get(b) else []) + files.get(b, [])
            open(os.path.join(outdir, 'f_' + re.sub(r'\W', '_', b[:-2]) + '.go'), 'w').write(self.file_text(hdr(b), body))
        body = []
        for name, c in self.F.records.items():
            body += self.record(name, c)
        for sig, (name, ft) in self.delegates.items():
            body.append(self.delegate_decl_auto(name, ft))
        open(os.path.join(outdir, 'types.go'), 'w').write(
            self.file_text(['// Generated by tools/c2x/emit_go.py from EPA SWMM 5.2.4 headers.'], body))
        body = ['const (']
        for n, v in self.F.enum_consts.items():
            body.append('\t%s = %d' % (self.ename[n], v))
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, s) in m.items():
                if n in self.mname and n not in done and kind in ('int', 'float'):
                    done.add(n)
                    if kind == 'int':
                        v = re.sub(r'[uUlL]+$', '', s)
                        if len(v.lstrip('-')) > 1 and v.lstrip('-').startswith('0'):
                            v = str(int(v, 8))
                        body.append('\t%s = %s' % (self.mname[n], v))
                    else:
                        body.append('\t%s float64 = %s' % (self.mname[n], self.cs_float(s, 'd')))
        body.append(')')
        body.append('')
        for bts, name in self.lits.items():
            body.append('var %s = R.Lit(%s)' % (name, go_string(bts)))
        open(os.path.join(outdir, 'consts.go'), 'w').write(
            self.file_text(['// Generated by tools/c2x/emit_go.py from EPA SWMM 5.2.4 headers and string literals.'], body))
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = GoEmitter(F)
    out = sys.argv[1] if len(sys.argv) > 1 else 'out_go'
    probs = em.emit(out)
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
