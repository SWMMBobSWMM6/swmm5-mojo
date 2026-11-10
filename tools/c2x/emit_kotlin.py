"""
emit_kotlin.py - EPA SWMM 5.2.4 C  ->  Kotlin/JVM (package swmm5: one file F_<file>.kt of top-level functions
and properties per C file; records and function-pointer interfaces in Types.kt; enums, macros and string
literals in Consts.kt).

The Java back end (emit_java.py) supplies the analysis this one reuses unchanged: the front end's pointer
modes, which locals and globals live in boxes, names, Java's reachability rules. Its type model carries over
because Kotlin runs on the same JVM: char* -> CPtr, scalar pointer parameters -> DRef/IRef/LRef/FRef,
unsigned int -> Long masked to 32 bits, double -> int through R.D2I (x86's rule, not the JVM's saturating
one), glibc's math translated to Kotlin (Glibm.kt). What Kotlin changes:

  * no implicit numeric conversion anywhere: every C conversion (clang's implicit casts included) is
    written out (.toDouble(), .toInt(), ...); integer literals are typed where they stand
  * bitwise operators and shifts are infix functions (and, or, xor, shl, shr, ushr, inv())
  * null safety: every reference type is declared nullable and dereferenced with !!, which is what C does
    (a null pointer faults where it is used)
  * assignments are statements: an assignment, ++ or += used as a value becomes (v).also { __v -> x = __v }
  * parameters are read-only: a parameter the C code assigns is copied into a local of the same name
  * no C for loop: init; while (cond) { body; inc }, and a continue runs inc first
  * no switch: when, with C's fall-through written out by appending the following case bodies, inside a
    labelled do { } while (false) when a break leaves the switch early; every loop is labelled and every
    break and continue names its target
  * a bare { } block is a lambda, so nested C blocks are flattened (local names are unique per function)
  * `if` is the conditional expression; ref identity is ===; `$` in strings is escaped

Written by Claude (Anthropic) for Robert Dickinson; see kotlin/README.md.
"""
import os, re, sys, collections, struct
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null
from emit_java import JavaEmitter, fclass

KOTLIN_RESERVED = set('''as break class continue do else false for fun if in interface is null object package return super
this throw true try typealias typeof val var when while R CPtr CFile Glibm GlibmRt Overrides Main Int Long Double Float
Unit Any Array String Boolean Byte Short Char Nothing Math System IntArray LongArray DoubleArray FloatArray ByteArray
DRef IRef LRef FRef ORef DBox IBox LBox FBox OBox DElem IElem LElem FElem OElem DField IField LField FField OField
DAcc IAcc LAcc FAcc OAcc CharRef OdeDerivs it field value'''.split())

KT = {'i': 'Int', 'u': 'Long', 'l': 'Long', 'ul': 'Long', 'd': 'Double', 'f': 'Float'}
ARR = {'i': 'IntArray', 'u': 'LongArray', 'l': 'LongArray', 'ul': 'LongArray', 'd': 'DoubleArray', 'f': 'FloatArray'}
ARROF = {'i': 'intArrayOf', 'u': 'longArrayOf', 'l': 'longArrayOf', 'ul': 'longArrayOf', 'd': 'doubleArrayOf', 'f': 'floatArrayOf'}
REFT = {'d': 'DRef', 'f': 'FRef', 'i': 'IRef', 'u': 'LRef', 'l': 'LRef', 'ul': 'LRef'}
BOXT = {'d': 'DBox', 'f': 'FBox', 'i': 'IBox', 'u': 'LBox', 'l': 'LBox', 'ul': 'LBox'}
ZERO = {'i': '0', 'u': '0L', 'l': '0L', 'ul': '0L', 'd': '0.0', 'f': '0.0f'}
MATH = {'fabs': 'abs', 'sqrt': 'sqrt', 'floor': 'floor', 'ceil': 'ceil',
        'exp': 'Glibm.exp', 'log': 'Glibm.log', 'log10': 'Glibm.log10', 'sin': 'Glibm.sin', 'cos': 'Glibm.cos',
        'tan': 'Glibm.tan', 'asin': 'Glibm.asin', 'acos': 'Glibm.acos', 'atan': 'Glibm.atan'}
MASK = '0xFFFFFFFFL'
INT_LIT = re.compile(r'^\d+$')
LONG_LIT = re.compile(r'^\d+L$')
FILE_HEAD = ('@file:Suppress("UNUSED_VARIABLE", "UNUSED_VALUE", "UNUSED_PARAMETER", "NAME_SHADOWING", "UNREACHABLE_CODE",\n'
             '               "VARIABLE_WITH_REDUNDANT_INITIALIZER", "UNNECESSARY_NOT_NULL_ASSERTION", "UNUSED_EXPRESSION",\n'
             '               "ASSIGNED_BUT_NEVER_ACCESSED_VARIABLE", "UNCHECKED_CAST", "USELESS_CAST", "LocalVariableName",\n'
             '               "FunctionName", "PropertyName", "ObjectPropertyName", "ClassName", "KotlinConstantConditions",\n'
             '               "ReplaceWithOperatorAssignment", "CascadeIf", "LiftReturnOrAssignment", "RedundantExplicitType")\n')


def kident(n):
    return n + '_' if n in KOTLIN_RESERVED else n


def kt_string(b):
    out = []
    for ch in b:
        if ch == 0x5c:
            out.append('\\\\')
        elif ch == 0x22:
            out.append('\\"')
        elif ch == 0x24:
            out.append('\\$')
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


def long_lit(x):
    if x == -(1 << 63):
        return 'Long.MIN_VALUE'
    return '(%dL)' % x if x < 0 else '%dL' % x


def int_lit(x):
    if x == -(1 << 31):
        return 'Int.MIN_VALUE'
    return '(%d)' % x if x < 0 else '%d' % x


def fkt(b):
    return 'F_' + re.sub(r'\W', '_', b[:-2])


class KotlinEmitter(JavaEmitter):
    def __init__(self, F):
        super().__init__(F)
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        for (b, n), c in F.funcs.items():
            self.fname[(b, n)] = kident(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        for k, c in F.globals.items():
            n = c.spelling
            b = F.global_owner[k]
            self.gname[k] = kident(b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n)
        self.jumps = []          # innermost last: ['loop', label, inc_code] | ['switch', label, used]
        self.nlabel = 0
        # odesolve.c is hand-ported (Overrides.kt); its callback type gets a fixed name so the port can use it
        for key, c in F.funcs.items():
            if key == ('odesolve.c', 'odesolve_integrate'):
                pt = list(c.get_arguments())[-1].type
                ft = canon(canon(pt).get_pointee())
                sig = (ft.get_result().spelling,) + tuple(a.spelling for a in ft.argument_types())
                self.delegates[sig] = ('OdeDerivs', ft)

    # ================================================================== naming
    def global_ref(self, d):
        k = self.global_key(d)
        if k is not None:
            return self.gname[k]
        if d.spelling in ('stdout', 'stderr'):
            return 'R.stdout'
        return kident(d.spelling)

    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = '__L%d' % len(self.lits)
        return self.lits[b]

    def macro_name(self, n):
        for b, m in self.F.macros.items():
            if n in m and m[n][0] in ('int', 'float') and n in self.macro_global:
                return kident(n)
        return None

    def static_local_name(self, d):
        return kident('%s_%s' % (d.semantic_parent.spelling, d.spelling))

    def local_name(self, d):
        return self.locals.get(decl_key(d), kident(d.spelling))

    def declare_local(self, d):
        n = d.spelling
        nn = n
        if n in self.used_names:
            i = 2
            while '%s_%d' % (n, i) in self.used_names:
                i += 1
            nn = '%s_%d' % (n, i)
        self.used_names.add(nn)
        self.locals[decl_key(d)] = kident(nn)
        return kident(nn)

    def field(self, n):
        return kident(n)

    def rec(self, t):
        return kident(record_name(t))

    def nn(self, code):
        """a reference used as a receiver (C would fault on null; so does !!)"""
        return self.paren(code) + '!!'

    def paren(self, s):
        if re.fullmatch(r'[\w.\[\]!]+', s) or (s.startswith('(') and s.endswith(')') and self._balanced(s[1:-1])):
            return s
        return '(' + s + ')'

    # ================================================================== types
    def ktype(self, t, decl=None, mode=None):
        """Kotlin type of a C type; every reference type is nullable"""
        t = canon(t)
        tg = ctag(t)
        if tg in KT:
            return KT[tg]
        if tg == 'v':
            return 'Unit'
        if tg == 'rec':
            return self.rec(t) + '?'
        if tg == 'c':
            return 'CPtr?'
        cat = ptr_category(t)
        if mode is None and decl is not None:
            mode = self.P.mode_of(decl)
        if cat == 'file':
            return 'CFile?'
        if cat == 'void':
            return 'Any?'
        if cat == 'func':
            return self.delegate(t) + '?'
        e = canon(t.element_type if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) else t.get_pointee())
        if cat == 'record':
            if (mode in (None, 'array') and t.kind != T.POINTER) or mode == 'array':
                return 'Array<%s?>?' % self.rec(e)
            return self.rec(e) + '?'
        if cat == 'scalar':
            if mode == 'ref':
                return REFT[ctag(e)] + '?'
            return ARR[ctag(e)] + '?'
        if cat == 'ptrptr':
            inner = self.ktype(e, mode='obj' if ptr_category(e) == 'record' else 'array')
            if mode == 'ref':
                return 'ORef<%s>?' % inner
            return 'Array<%s>?' % inner
        return 'Any?'

    def jtype(self, t, decl=None, mode=None):
        return self.ktype(t, decl, mode)

    def cs_type(self, t, decl=None, mode=None):
        return self.ktype(t, decl, mode)

    def zero(self, t):
        return ZERO.get(ctag(t), 'null')

    def delegate_of_function(self, ft):
        ft = canon(ft)
        sig = (ft.get_result().spelling,) + tuple(a.spelling for a in ft.argument_types())
        if sig not in self.delegates:
            self.delegates[sig] = ('FP%d' % len(self.delegates), ft)
        return self.delegates[sig][0]

    # ================================================================== conversions
    def to_ctype(self, e, t):
        want = ctag(t)
        if e.tag == 'b' and want in NUMTAGS:
            return self.conv(Ex('(if (%s) 1 else 0)' % e.code, 'i'), None, t, src_tag='i')
        return e

    def as_bool(self, e):
        if e.tag == 'b':
            return e.code
        if e.tag == 'i':
            return '(%s != 0)' % e.code
        if e.tag in ('u', 'l', 'ul'):
            return '(%s != 0L)' % e.code
        if e.tag == 'd':
            return '(%s != 0.0)' % e.code
        if e.tag == 'f':
            return '(%s != 0.0f)' % e.code
        return '(%s != null)' % e.code

    def conv(self, e, src_t, dst_t, src_tag=None):
        s = src_tag or (ctag(src_t) if src_t is not None else e.tag)
        d = ctag(dst_t)
        if e.tag == 'b' and d in NUMTAGS:
            e = Ex('(if (%s) 1 else 0)' % e.code, 'i'); s = 'i'
        if s == d or d in ('v', '?'):
            return Ex(e.code, d if d != '?' else e.tag)
        if d == 'rec':
            return e
        if d in NUMTAGS and s in NUMTAGS:
            return Ex(self.numconv(e.code, s, d), d)
        if d in ('c', 'o'):
            if is_null(e.code) or e.code == 'null' or e.tag == 'n' or (e.tag in ('i', 'l') and e.code in ('0', '0L')):
                return Ex('null', d)
            return Ex(e.code, d)
        return e

    def numconv(self, code, s, d):
        """C conversion of a numeric value from tag s to tag d"""
        if s == d:
            return code
        lit = INT_LIT.match(code) and s == 'i'
        if d == 'i':
            if s in ('d', 'f'):
                return 'R.D2I(%s)' % (code if s == 'd' else '(%s).toDouble()' % code)
            return '(%s).toInt()' % code
        if d in ('l', 'ul'):
            if s in ('d', 'f'):
                return 'R.D2L(%s)' % (code if s == 'd' else '(%s).toDouble()' % code)
            if s == 'i':
                return code + 'L' if lit else '(%s).toLong()' % code
            return code
        if d == 'u':
            if s in ('d', 'f'):
                return '(R.D2L(%s) and %s)' % (code if s == 'd' else '(%s).toDouble()' % code, MASK)
            if s == 'i':
                return code + 'L' if lit else '((%s).toLong() and %s)' % (code, MASK)
            return '(%s and %s)' % (self.paren(code), MASK)
        if d == 'd':
            if lit:
                return code + '.0'
            return '(%s).toDouble()' % code
        if d == 'f':
            if lit:
                return code + '.0f'
            return '(%s).toFloat()' % code
        raise ValueError('numconv %s -> %s' % (s, d))

    def idx(self, e):
        """an array index (an Int)"""
        if e.tag in ('l', 'u', 'ul'):
            return '(%s).toInt()' % e.code
        if e.tag == 'b':
            return '(if (%s) 1 else 0)' % e.code
        return e.code

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
        return Ex(long_lit(x) if suf else int_lit(x), tg)

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
            return Ex('Double.NaN' if tg != 'f' else 'Float.NaN', tg)
        if abs(x) == float('inf'):
            n = 'Float' if tg == 'f' else 'Double'
            return Ex('%s.POSITIVE_INFINITY' % n if x > 0 else '%s.NEGATIVE_INFINITY' % n, tg)
        s = repr(x) + ('f' if tg == 'f' else '')
        return Ex('(%s)' % s if s.startswith('-') else s, tg)

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return Ex(kident(c.spelling), '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return Ex(int_lit(d.enum_value), 'i')
            return Ex(kident(d.spelling), 'i')
        if d.kind == K.FUNCTION_DECL:
            keys = self.F.func_by_decl.get(d.spelling) or []
            cand = [k for k in keys if k[0] == self.cur_file] or [k for k in keys if self.F.funcs[k].storage_class != front.ci.StorageClass.STATIC]
            if not cand:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex(kident(d.spelling), 'o')
            fd = self.F.funcs[cand[0]]
            return Ex('%s(::%s)' % (self.delegate_of_function(fd.type), self.fname[cand[0]]), 'o')
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
        return Ex(kident(c.spelling), ctag(c.type))

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
                return Ex('(%s as %s)' % (self.paren(e.code), self.ktype(c.type, mode='obj' if ptr_category(c.type) == 'record' else 'array')), 'o')
            return e
        e = self.to_ctype(e, inner.type)
        r = self.conv(e, inner.type, c.type)
        k = canon(c.type).kind
        if k in (T.UCHAR, T.CHAR_U):
            return Ex('(%s and 255)' % self.paren(r.code), 'i')
        if k in (T.CHAR_S, T.SCHAR) and canon(inner.type).kind not in (T.CHAR_S, T.SCHAR):
            return Ex('(%s).toByte().toInt()' % r.code, 'i')
        if k == T.SHORT:
            return Ex('(%s).toShort().toInt()' % r.code, 'i')
        if k == T.USHORT:
            return Ex('(%s and 65535)' % self.paren(r.code), 'i')
        return r

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

    def assign_stmt(self, l, rhs):
        k = self.lv_kind(l)
        if k[0] == 'char':
            return '%s.s(%s, %s)' % (self.nn(k[1]), k[2], rhs)
        if k[0] == 'ref':
            return '%s.set(%s)' % (self.nn(k[1]), rhs)
        return '%s = %s' % (k[1], rhs)

    def assign_value(self, l, rhs):
        """an assignment used as a value: its value is rhs (already of the left side's type)"""
        k = self.lv_kind(l)
        if k[0] == 'char':
            return '%s.s(%s, %s)' % (self.nn(k[1]), k[2], rhs)
        if k[0] == 'ref':
            return '%s.set(%s)' % (self.nn(k[1]), rhs)
        return '(%s).also { __v -> %s = __v }' % (rhs, k[1])

    def assign_code(self, l, rhs):
        return self.assign_stmt(l, rhs)

    def ref_of(self, a):
        """a reference object (DRef, ...) for lvalue a"""
        sa = strip(a)
        k = self.lv_kind(a)
        if k[0] == 'char':
            return 'CharRef(%s, %s)' % (self.nn(k[1]), k[2])
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
                return '%sField<%s>(%s, { __o -> __o.%s }, { __o, __x -> __o.%s = __x })' % (REFT[tg][0], rt, obj, attr, attr)
            return 'OField<%s, %s>(%s, { __o -> __o.%s }, { __o, __x -> __o.%s = __x })' % (rt, self.ktype(sa.type), obj, attr, attr)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ix = kids(sa)
            if tg in REFT:
                return '%sElem(%s, %s)' % (REFT[tg][0], self.nn(self.ex(base).code), self.idx(self.val(ix)))
            return 'OElem<%s>(%s, %s)' % (self.ktype(sa.type), self.nn(self.ex(base).code), self.idx(self.val(ix)))
        if sa.kind == K.DECL_REF_EXPR:
            if tg in REFT:
                return '%sAcc({ %s }, { __x -> %s = __x })' % (REFT[tg][0], lv, lv)
            return 'OAcc<%s>({ %s }, { __x -> %s = __x })' % (self.ktype(sa.type), lv, lv)
        self.problem(a, 'reference to %s' % lv)
        return 'null'

    def read_lv(self, a):
        k = self.lv_kind(a)
        if k[0] == 'char':
            return '%s.g(%s)' % (self.nn(k[1]), k[2])
        if k[0] == 'ref':
            return '%s.get()' % self.nn(k[1])
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
                return Ex('((-%s) and %s)' % (self.paren(e.code), MASK), 'u')
            return Ex('(-%s)' % self.paren(e.code), e.tag)
        if op == '+':
            return e
        if op == '~':
            if e.tag == 'u':
                return Ex('(%s.inv() and %s)' % (self.paren(e.code), MASK), 'u')
            return Ex('%s.inv()' % self.paren(e.code), e.tag)
        self.problem(c, 'unary ' + op)
        return e

    def incdec_expr(self, a, op):
        d = '+' if '++' in op else '-'
        tg = ctag(a.type)
        pre = op.startswith('pre')
        k = self.lv_kind(a)
        if k[0] == 'char':
            b = self.nn(k[1])
            nv = '%s.s(%s, %s.g(%s) %s 1)' % (b, k[2], b, k[2], d)
            return Ex(nv if pre else '(%s %s 1)' % (nv, '-' if d == '+' else '+'), 'i')
        if k[0] == 'ref':
            r = self.nn(k[1])
            nv = '%s.set(%s.get() %s 1)' % (r, r, d)
            if pre:
                return Ex(nv, tg)
            if tg in ('i', 'l', 'ul'):
                return Ex('(%s %s 1)' % (nv, '-' if d == '+' else '+'), tg)
            return Ex('R.post(%s, %s1)' % (k[1], d), tg)
        lv = k[1]
        if tg == 'c':
            step = '1' if d == '+' else '-1'
            if pre:
                return Ex('(%s.add(%s)).also { __v -> %s = __v }' % (self.nn(lv), step, lv), 'c')
            return Ex('%s.also { __v -> %s = __v!!.add(%s) }' % (self.paren(lv), lv, step), 'c')
        if tg == 'u':
            if pre:
                return Ex('((%s %s 1) and %s).also { __v -> %s = __v }' % (lv, d, MASK, lv), 'u')
            return Ex('%s.also { __v -> %s = (__v %s 1) and %s }' % (self.paren(lv), lv, d, MASK), 'u')
        return Ex(('(%s%s%s)' % (d, d, lv)) if pre else ('(%s%s%s)' % (lv, d, d)), tg)

    def deref(self, a):
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-'):
                x, y = kids(sa)
                if ptr_category(x.type) == 'char':
                    i = self.idx(self.val(y))
                    return Ex('%s.g(%s)' % (self.nn(self.ex(x).code), i if binop(sa) == '+' else '-(%s)' % i), 'i')
            return Ex('%s.g(0)' % self.nn(self.ex(a).code), 'i')
        e = self.ex(a)
        if cat == 'record':
            return Ex(e.code, 'rec')
        mode = self.mode_of_expr(sa)
        pt = ctag(canon(a.type).get_pointee())
        if mode == 'ref':
            return Ex(self.nn(e.code) + '.get()', pt)
        if sa.kind == K.BINARY_OPERATOR:
            l, r = kids(sa)
            return Ex('%s[%s]' % (self.nn(self.ex(l).code), self.idx(self.val(r))), pt)
        return Ex('%s[0]' % self.nn(e.code), pt)

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
                return Ex(b if i == '0' else '%s.add(%s)' % (self.nn(b), i), 'c')
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
                return Ex(self.assign_value(l, '%s.copy()' % self.nn(self.ex(r).code)), 'rec')
            re_ = self.conv(self.val(r), r.type, l.type)
            return Ex(self.assign_value(l, re_.code), ctag(l.type))
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
                    return Ex('(%s.o %s %s.o)' % (self.nn(le.code), op, self.nn(re_.code)), 'b')
                return Ex('(%s %s %s)' % (le.code, {'==': '===', '!=': '!=='}.get(op, op), re_.code), 'b')
            if le.tag != re_.tag and le.tag in NUMTAGS and re_.tag in NUMTAGS:
                self.problem(c, 'comparison of %s with %s' % (le.tag, re_.tag))
            return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
        tg = ctag(c.type)
        if tg == 'c':
            if op == '+':
                if ptr_category(l.type) == 'char':
                    return Ex('%s.add(%s)' % (self.nn(le.code), self.idx(re_)), 'c')
                return Ex('%s.add(%s)' % (self.nn(re_.code), self.idx(le)), 'c')
            return Ex('%s.add(-%s)' % (self.nn(le.code), self.paren(self.idx(re_))), 'c')
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            return Ex('(%s.o - %s.o).toLong()' % (self.nn(le.code), self.nn(re_.code)), 'l')
        if op in ('<<', '>>') and re_.tag in ('l', 'u', 'ul'):
            re_ = Ex('(%s).toInt()' % re_.code, 'i')
        return Ex(self.arith(op, le.code, re_.code, tg), tg)

    def arith(self, op, a, b, tg):
        if op in ('&', '|', '^'):
            v = '(%s %s %s)' % (a, {'&': 'and', '|': 'or', '^': 'xor'}[op], b)
            return v
        if op == '<<':
            v = '(%s shl %s)' % (a, b)
        elif op == '>>':
            v = '(%s %s %s)' % (a, 'ushr' if tg == 'ul' else 'shr', b)
        else:
            v = '(%s %s %s)' % (a, op, b)
        if tg == 'u' and op in ('+', '-', '*', '<<'):
            return '(%s and %s)' % (v, MASK)
        return v

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        l = kids(c)[0]
        k, v, lt = self.compound_parts(c)
        if k[0] == 'char':
            return Ex('%s.s(%s, %s)' % (self.nn(k[1]), k[2], v), 'i')
        if k[0] == 'ref':
            return Ex('%s.set(%s)' % (self.nn(k[1]), v), lt)
        return Ex('(%s).also { __v -> %s = __v }' % (v, k[1]), lt)

    def compound_parts(self, c):
        """(lvalue kind, new value of the left side, its tag)"""
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        re_ = self.val(r)
        k = self.lv_kind(l)
        if lt == 'c':
            lv = k[1]
            if op == '+':
                return k, '%s.add(%s)' % (self.nn(lv), self.idx(re_)), 'c'
            return k, '%s.add(-%s)' % (self.nn(lv), self.paren(self.idx(re_))), 'c'
        common = 'd' if 'd' in (lt, rt) else ('f' if 'f' in (lt, rt) else ('ul' if 'ul' in (lt, rt) else
                  ('l' if 'l' in (lt, rt) else ('u' if 'u' in (lt, rt) else 'i'))))
        if op in ('<<', '>>'):
            common = lt
            rcode = self.idx(re_)
        else:
            rcode = self.numconv(re_.code, re_.tag, common) if re_.tag in NUMTAGS else re_.code
        cur = self.numconv(self.read_lv(l), lt, common) if lt in NUMTAGS else self.read_lv(l)
        v = self.arith(op, cur, self.paren(rcode), common)
        if lt in NUMTAGS and common != lt:
            v = self.numconv(v, common, lt)
        return k, v, lt

    def compound_code(self, c):
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        k, v, _ = self.compound_parts(c)
        if k[0] == 'char':
            return '%s.s(%s, %s)' % (self.nn(k[1]), k[2], v)
        if k[0] == 'ref':
            return '%s.set(%s)' % (self.nn(k[1]), v)
        re_ = self.val(r)
        if lt in ('d', 'f', 'i', 'l', 'ul') and re_.tag == lt and op in ('+', '-', '*', '/'):
            return '%s %s= %s' % (k[1], op, self.paren(re_.code))
        return '%s = %s' % (k[1], v)

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        tg = ctag(c.type)
        ea = self.conv(self.val(a), a.type, c.type)
        eb = self.conv(self.val(b), b.type, c.type)
        return Ex('(if (%s) %s else %s)' % (self.cond(cc), ea.code, eb.code), tg)

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, ix = kids(c)
        if ptr_category(base.type) == 'char':
            return Ex('%s.g(%s)' % (self.nn(self.ex(base).code), self.idx(self.val(ix))), 'i')
        b = self.ex(base)
        return Ex('%s[%s]' % (self.nn(b.code), self.idx(self.val(ix))), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        b = self.ex(base)
        return Ex('%s.%s' % (self.nn(b.code), self.field(c.referenced.spelling)), ctag(c.type))

    # ================================================================== init lists
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
                return Ex('R.bufOf(%d, intArrayOf(%s))' % (n, ', '.join(self.val(it).code for it in items)), 'c')
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
                    vals.append('%s()' % self.rec(et))
                elif et.kind == T.CONSTANTARRAY:
                    vals.append(self.new_array(et))
                else:
                    vals.append(self.zero(et))
            etg = ctag(et)
            if etg in ARROF:
                return Ex('%s(%s)' % (ARROF[etg], ', '.join(vals)), 'o')
            elt = self.ktype(et, mode='obj' if ptr_category(et) == 'record' else 'array')
            if etg == 'rec' or et.kind == T.CONSTANTARRAY:
                elt = elt if elt.endswith('?') else elt + '?'
            return Ex('arrayOf<%s>(%s)' % (elt, ', '.join(vals)), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                if strip(it).kind == K.INIT_LIST_EXPR:
                    parts.append('__r.%s = %s' % (self.field(f.spelling), self.init_list(strip(it), f.type).code))
                else:
                    parts.append('__r.%s = %s' % (self.field(f.spelling), self.conv(self.val(it), it.type, f.type).code))
            return Ex('%s().also { __r -> %s }' % (self.rec(t), '; '.join(parts)), 'rec')
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
                    et = ctag(pt.get_pointee() if pt.kind == T.POINTER else pt.element_type)
                    self.pre.append('val %s = %s(%s)' % (t, ARROF[et], self.read_lv(o)))
                    self.post.append(self.assign_stmt(o, '%s[0]' % t))
                    codes.append(t)
                    continue
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    o = kids(sa)[0]
                    self.tmp += 1
                    t = '__c%d' % self.tmp
                    self.pre.append('val %s = R.buf(2); %s.s(0, %s)' % (t, t, self.read_lv(o)))
                    self.post.append(self.assign_stmt(o, '%s.g(0)' % t))
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
        return Ex('%s.call(%s)' % (self.nn(fe.code), ', '.join(argcodes)), ctag(c.type))

    def func_ref(self, d, cur_file):
        return super().func_ref(d, cur_file)

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
                return '%sElem(%s, 0)' % (REFT[pt][0], self.nn(e.code))
            return 'OElem(%s, 0)' % self.nn(e.code)
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
        if cat in ('char', 'record', 'void', 'func', 'file') and is_null(e.code):
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
                head[1] = self.idx(self.val(args[1]))
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
                return Ex('%s = %s()' % (self.lvalue(o), self.rec(o.type)), 'v')
            return Ex('R.memset(%s, %s, %s)' % (A(0), A(1), A(2)), 'v')
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return Ex('R.strtod(%s, %s)' % (A(0), self.ref_of(kids(ep)[0])), 'd')
            return Ex('R.strtod(%s, null)' % A(0), 'd')
        if name == 'time':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                return Ex(self.assign_value(kids(a0)[0], 'R.time()'), 'l')
            return Ex('R.time()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('R.ctime(%s)' % (self.ex(kids(a0)[0]).code if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('(%s - %s).toDouble()' % (A(0), A(1)), 'd')
        if name == 'fseeko':
            name = 'fseek'
        rt = {'strlen': 'ul', 'atoi': 'i', 'strcmp': 'i', 'feof': 'i', 'fclose': 'i', 'atof': 'd', 'ftell': 'l',
              'strcspn': 'ul', 'toupper': 'i', 'fseek': 'i', 'remove': 'i', 'fflush': 'i', 'rewind': 'v'}.get(name, tg)
        al = [A(i) for i in range(len(args))]
        if name == 'fgets':
            al[1] = self.idx(self.val(args[1]))
        return Ex('R.%s(%s)' % (name, ', '.join(al)), rt)

    def vararg(self, a, scanf):
        sa = strip(a)
        if scanf:
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return self.ref_of(kids(sa)[0])
            return self.val(a).code
        return self.val(a).code

    def int_code(self, x):
        e = self.val(x)
        if e.tag in ('ul', 'l', 'u'):
            return '(%s).toInt()' % e.code
        return e.code

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
                return Ex('R.realloc(%s, %s) { %s() }' % (old, n, self.rec(et)), 'o')
            return Ex('R.realloc(%s, %s)' % (old, n), 'o')
        if ctag(t) == 'c':
            return Ex('R.buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('%s()' % self.rec(et), 'o')
            return Ex('Array<%s?>(%s) { %s() }' % (self.rec(et), n, self.rec(et)), 'o')
        if et.kind == T.POINTER:
            inner = self.ktype(et, mode='obj' if ptr_category(et) == 'record' else 'array')
            return Ex('arrayOfNulls<%s>(%s)' % (inner.rstrip('?'), n), 'o')
        tg = ctag(et)
        if tg in ARR:
            return Ex('%s(%s)' % (ARR[tg], n), 'o')
        self.problem(call, 'allocation of %s' % et.spelling)
        return Ex('null', 'o')

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
                return Ex('R.fwrite1(%s.get(), %d, %s)' % (self.nn(self.ex(sb).code), sz or nat, fc), 'ul')
            return Ex('R.fread1(%s, %d, %s)' % (self.ex(sb).code, sz or nat, fc), 'ul')
        return Ex('R.%s(%s, 0, %s, %s)' % (name, self.ex(sb).code, self.int_code(cnt), fc), 'ul')

    # ================================================================== statements
    def new_label(self, kind):
        self.nlabel += 1
        return '%s%d' % (kind, self.nlabel)

    def stmt(self, c, ind):
        k = c.kind
        p = '    ' * ind
        if k == K.COMPOUND_STMT:
            # a nested C block: its statements, without braces (in Kotlin a bare { } is a lambda)
            out = []
            for ch in kids(c):
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
            out = self.flush([p + 'if (%s) {' % self.cond(ch[0])], ind)
            out += self.body(ch[1], ind)
            x = c
            while len(kids(x)) > 2:
                e = kids(x)[2]
                if e.kind == K.IF_STMT:
                    ec = kids(e)
                    cond = self.cond(ec[0])
                    if self.pre or self.post:
                        # set-up statements for the else-if condition: nest it instead
                        self.pre, self.post = [], []
                        out.append(p + '} else {')
                        out += self.stmt(e, ind + 1)
                        out.append(p + '}')
                        return out
                    out.append(p + '} else if (%s) {' % cond)
                    out += self.body(ec[1], ind)
                    x = e
                else:
                    out.append(p + '} else {')
                    out += self.body(e, ind)
                    break
            out.append(p + '}')
            return out
        if k == K.WHILE_STMT:
            ch = kids(c)
            lab = self.new_label('w')
            head = self.flush([p + '%s@ while (%s) {' % (lab, self.cond(ch[0]))], ind)
            self.jumps.append(['loop', lab, None])
            body = self.body(ch[1], ind)
            self.jumps.pop()
            return head + body + [p + '}']
        if k == K.DO_STMT:
            ch = kids(c)
            lab = self.new_label('d')
            self.jumps.append(['loop', lab, None])
            body = self.body(ch[0], ind)
            self.jumps.pop()
            tail = self.flush([p + '} while (%s)' % self.cond(ch[1])], ind)
            return [p + '%s@ do {' % lab] + body + tail
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            j = self.jumps[-1]
            if j[0] == 'switch':
                j[2] = True
            return [p + 'break@%s' % j[1]]
        if k == K.CONTINUE_STMT:
            for j in reversed(self.jumps):
                if j[0] == 'loop':
                    if j[2]:
                        return [p + x for x in j[2]] + [p + 'continue@%s' % j[1]]
                    return [p + 'continue@%s' % j[1]]
            self.problem(c, 'continue outside a loop')
            return []
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'return']
            if ctag(self.cur_ret) == 'rec':
                return self.flush([p + 'return %s.copy()' % self.nn(self.ex(ch[0]).code)], ind)
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            if ctag(self.cur_ret) in ('c', 'o') and is_null(e.code):
                e = Ex('null', 'o')
            if self.post:
                self.tmp += 1
                t = '__r%d' % self.tmp
                return self.flush([p + 'val %s = %s' % (t, e.code)], ind) + [p + 'return %s' % t]
            return self.flush([p + 'return %s' % e.code], ind)
        if k == K.NULL_STMT:
            return []
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unhandled statement %s' % k.name)
            return []
        return self.flush([p + self.expr_stmt_code(c)], ind)

    def flush(self, lines, ind):
        """put the set-up and copy-back statements a call's arguments needed around a statement"""
        if not self.pre and not self.post:
            return lines
        p = '    ' * ind
        pre, post = self.pre, self.post
        self.pre, self.post = [], []
        if post and any(re.match(r'^(return|if |\w+@ |\} while)', l.strip()) for l in lines):
            self.problems.append('copy-back after %s' % lines[0].strip())
        return [p + x for x in pre] + lines + [p + x for x in post]

    def body(self, c, ind):
        """the statements of a loop or if body, one level in (the caller writes the braces)"""
        return self.stmt(c, ind + 1)

    def block(self, c, ind):
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
                return self.assign_stmt(l, '%s.copy()' % self.nn(self.ex(r).code))
            return self.assign_stmt(l, self.conv(self.val(r), r.type, l.type).code)
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
                b = self.nn(k[1])
                return '%s.s(%s, %s.g(%s) %s 1)' % (b, k[2], b, k[2], d)
            if k[0] == 'ref':
                r = self.nn(k[1])
                return '%s.set(%s.get() %s 1)' % (r, r, d)
            lv = k[1]
            tg = ctag(a.type)
            if tg == 'c':
                return '%s = %s.add(%s1)' % (lv, self.nn(lv), '' if d == '+' else '-')
            if tg == 'u':
                return '%s = (%s %s 1) and %s' % (lv, lv, d, MASK)
            return '%s%s%s' % (lv, d, d)
        if s.kind == K.CONDITIONAL_OPERATOR:
            cc, a, b = kids(s)
            return 'if (%s) { %s } else { %s }' % (self.cond(cc), self.expr_stmt_code(a), self.expr_stmt_code(b))
        e = self.ex(c)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        return code

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
        p = '    ' * ind
        init, cond, inc, body = self.for_parts(c)
        out = []
        if init is not None:
            if init.kind == K.DECL_STMT:
                for d in kids(init):
                    out += self.flush(self.local_decl(d, ind), ind)
            else:
                out += self.flush([p + self.expr_stmt_code(init)], ind)
        cond_s = self.cond(cond) if cond is not None else 'true'
        if self.pre or self.post:
            self.problems.append('call set-up inside a for condition')
        inc_lines = []
        if inc is not None:
            inc_lines = [self.expr_stmt_code(inc)]
            if self.pre or self.post:
                self.problems.append('call set-up inside a for increment')
        lab = self.new_label('f')
        self.jumps.append(['loop', lab, inc_lines or None])
        b = self.body(body, ind)
        self.jumps.pop()
        out.append(p + '%s@ while (%s) {' % (lab, cond_s))
        out += b
        if inc_lines and self.completes(body):
            out += [p + '    ' + x for x in inc_lines]
        out.append(p + '}')
        return out

    def switch(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        e = self.val(ch[0])
        code = e.code if e.tag != 'b' else '(if (%s) 1 else 0)' % e.code
        if e.tag in ('l', 'u', 'ul'):
            code = '(%s).toInt()' % code
        body = ch[-1]
        items = kids(body) if body.kind == K.COMPOUND_STMT else [body]
        # groups: (labels, statements) in source order
        groups = []
        for it in items:
            x = it
            labels = []
            while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                xc = kids(x)
                if x.kind == K.CASE_STMT:
                    labels.append(self.val(xc[0]).code)
                    x = xc[1]
                else:
                    labels.append(None)
                    x = xc[0]
            if labels or not groups:
                groups.append((labels, []))
            if x.kind not in (K.CASE_STMT, K.DEFAULT_STMT):
                groups[-1][1].append(x)
        lab = self.new_label('s')
        jump = ['switch', lab, False]
        self.jumps.append(jump)
        head = self.flush([], ind)
        branches, default = [], None
        for gi, (labels, _) in enumerate(groups):
            if not labels:
                continue           # statements before the first label are unreachable
            # this group's statements, then (C falls through) the following groups' until a group's
            # statements cannot complete normally
            stmts = []
            for g2 in groups[gi:]:
                stmts += g2[1]
                if not self.seq_completes(g2[1]):
                    break
            # a break that ends the case body just leaves the when
            if stmts and stmts[-1].kind == K.BREAK_STMT:
                stmts = stmts[:-1]
            lines = []
            for s in stmts:
                lines += self.stmt(s, ind + 2)
                if not self.completes(s):
                    break
            if None in labels:
                # C's case labels sharing the default's body need no branch of their own: else catches
                # them (case values are distinct), and Kotlin wants else last
                default = lines
            else:
                branches.append((labels, lines))
        self.jumps.pop()
        out_when = [p + 'when (%s) {' % code]
        for labels, lines in branches:
            out_when.append(p + '    %s -> {' % ', '.join(labels))
            out_when += lines
            out_when.append(p + '    }')
        if default is not None:
            out_when.append(p + '    else -> {')
            out_when += default
            out_when.append(p + '    }')
        out_when.append(p + '}')
        if jump[2]:
            # a break before the end of a case body: the when sits in a labelled one-pass loop
            return head + [p + '%s@ do {' % lab] + ['    ' + l for l in out_when] + [p + '} while (false)']
        return head + out_when

    def seq_completes(self, stmts):
        for s in stmts:
            if not self.completes(s):
                return False
        return True

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
        ty = self.ktype(d.type, d)
        if t.kind == T.CONSTANTARRAY:
            aty = self.ktype(d.type, mode='array')
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return [p + 'var %s: %s = %s' % (name, aty, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return [p + 'var %s: CPtr? = R.bufFrom(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return [p + 'var %s: CPtr? = R.buf(%d)' % (name, t.element_count)]
            return [p + 'var %s: %s = %s' % (name, aty, self.new_array(t))]
        if ctag(t) == 'rec':
            if init:
                if strip(init[-1]).kind == K.INIT_LIST_EXPR:
                    return [p + 'var %s: %s = %s' % (name, ty, self.init_list(strip(init[-1]), t).code)]
                return [p + 'var %s: %s = %s.copy()' % (name, ty, self.nn(self.ex(init[-1]).code))]
            return [p + 'var %s: %s = %s()' % (name, ty, self.rec(t))]
        v = self.conv(self.val(init[-1]), init[-1].type, d.type).code if init else self.zero(d.type)
        if boxed:
            tg = ctag(d.type)
            bt = BOXT.get(tg, 'OBox<%s>' % ty)
            return [p + 'val %s = %s(%s)' % (name, bt, v)]
        return [p + 'var %s: %s = %s' % (name, ty, v)]

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return 'Array<%s?>(%d) { %s() }' % (self.rec(et), n, self.rec(et))
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return 'R.bufs(%d, %d)' % (n, et.element_count)
        if et.kind == T.CONSTANTARRAY:
            inner = canon(et.element_type)
            if ctag(inner) in ARR:
                return 'Array<%s?>(%d) { %s(%d) }' % (ARR[ctag(inner)], n, ARR[ctag(inner)], et.element_count)
            self.problems.append('array of arrays of %s' % inner.spelling)
            return 'null'
        if et.kind == T.POINTER:
            inner = self.ktype(et, mode='obj' if ptr_category(et) == 'record' else 'array')
            return 'arrayOfNulls<%s>(%d)' % (inner.rstrip('?'), n)
        return '%s(%d)' % (ARR[ctag(et)], n)

    # ================================================================== functions
    def assigned_params(self, body, params):
        keys = {decl_key(p) for p in params}
        out = set()

        def lhs_param(x):
            x = strip(x)
            if x.kind == K.DECL_REF_EXPR and x.referenced is not None and x.referenced.kind == K.PARM_DECL:
                k = decl_key(x.referenced)
                if k in keys:
                    out.add(k)

        def scan(x):
            if x.kind == K.BINARY_OPERATOR and binop(x) == '=':
                lhs_param(kids(x)[0])
            elif x.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
                lhs_param(kids(x)[0])
            elif x.kind == K.UNARY_OPERATOR and unop(x) in ('pre++', 'pre--', 'post++', 'post--'):
                lhs_param(kids(x)[0])
            for y in x.get_children():
                scan(y)
        scan(body)
        return out

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
        changed = self.assigned_params(body, params)
        ps, pre = [], []
        for prm in params:
            nm = self.declare_local(prm)
            ty = self.ktype(prm.type, prm)
            if decl_key(prm) in self.boxed_locals:
                bt = BOXT.get(ctag(prm.type), 'OBox<%s>' % ty)
                ps.append('__%s: %s' % (nm, ty))
                pre.append('    val %s = %s(__%s)' % (nm, bt, nm))
            elif decl_key(prm) in changed:
                ps.append('__%s: %s' % (nm, ty))
                pre.append('    var %s: %s = __%s' % (nm, ty, nm))
            else:
                ps.append('%s: %s' % (nm, ty))
        lines = self.stmt(body, 1)
        rt = self.ktype(c.result_type)
        head = 'fun %s(%s)%s {' % (self.fname[key], ', '.join(ps), '' if rt == 'Unit' else ': ' + rt)
        out = ['// %s:%d' % (b, c.location.line), head] + pre + lines
        if rt != 'Unit' and not (lines and re.match(r'^    return\b', lines[-1])):
            out.append('    throw IllegalStateException("%s: no return")' % n)
        out.append('}')
        return out

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = kident(name)
        out = ['class %s {' % nm]
        cp = ['    fun copy(): %s {' % nm, '        val c = %s()' % nm]
        for f in fields:
            t = canon(f.type)
            fn = self.field(f.spelling)
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    out.append('    @JvmField var %s: CPtr? = R.buf(%d)' % (fn, t.element_count))
                    cp.append('        c.%s = R.copyBuf(%s)' % (fn, fn))
                else:
                    ty = self.ktype(f.type, mode='array')
                    out.append('    @JvmField var %s: %s = %s' % (fn, ty, self.new_array(t)))
                    if et.kind == T.RECORD:
                        cp.append('        c.%s = Array<%s?>(%s!!.size) { __i -> %s!![__i]!!.copy() }' % (fn, self.rec(et), fn, fn))
                    elif et.kind == T.CONSTANTARRAY:
                        cp.append('        c.%s = R.cloneGrid(%s)' % (fn, fn))
                    elif ctag(et) == 'c' or et.kind == T.POINTER:
                        cp.append('        c.%s = %s!!.copyOf()' % (fn, fn))
                    else:
                        cp.append('        c.%s = %s!!.clone()' % (fn, fn))
            elif t.kind == T.RECORD:
                out.append('    @JvmField var %s: %s? = %s()' % (fn, self.rec(t), self.rec(t)))
                cp.append('        c.%s = %s!!.copy()' % (fn, fn))
            else:
                ty = self.ktype(f.type, f)
                if ty.rstrip('?') in REFT.values():
                    self.problems.append('ref field %s.%s' % (name, f.spelling))
                out.append('    @JvmField var %s: %s = %s' % (fn, ty, self.zero(f.type)))
                cp.append('        c.%s = %s' % (fn, fn))
        cp += ['        return c', '    }']
        return out + cp + ['}', '']

    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        self.boxed_locals = set(); self.locals = {}
        t = canon(c.type)
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        ty = self.ktype(c.type, c)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            aty = self.ktype(c.type, mode='array')
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return '@JvmField var %s: %s = %s' % (name, aty, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return '@JvmField var %s: CPtr? = R.bufFrom(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return '@JvmField var %s: CPtr? = R.buf(%d)' % (name, t.element_count)
            return '@JvmField var %s: %s = %s' % (name, aty, self.new_array(t))
        if t.kind == T.RECORD:
            return '@JvmField var %s: %s = %s()' % (name, ty, self.rec(t))
        v = self.conv(self.val(init[-1]), init[-1].type, c.type).code if init else self.zero(c.type)
        if k in self.boxed_globals:
            bt = BOXT.get(ctag(c.type), 'OBox<%s>' % ty)
            return '@JvmField val %s = %s(%s)' % (name, bt, v)
        return '@JvmField var %s: %s = %s' % (name, ty, v)

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
                ps.append('a%d: %s' % (i, (REFT[e] if isref else ARR[e]) + '?'))
            else:
                ps.append('a%d: %s' % (i, self.ktype(a, mode='obj' if cat == 'record' else None)))
        rt = self.ktype(ft.get_result())
        return 'fun interface %s { fun call(%s)%s }' % (name, ', '.join(ps), '' if rt == 'Unit' else ': ' + rt)

    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        for f in os.listdir(outdir):
            if f.startswith('F_') and f.endswith('.kt') or f in ('Types.kt', 'Consts.kt'):
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
            ty = self.ktype(d.type, d)
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                glob[b].append('@JvmField var %s: %s = %s' % (name, self.ktype(d.type, mode='array'), self.init_list(strip(init[-1]), t).code))
            elif ctag(t) == 'c' and t.kind == T.CONSTANTARRAY:
                if init:
                    glob[b].append('@JvmField var %s: CPtr? = R.bufFrom(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count))
                else:
                    glob[b].append('@JvmField var %s: CPtr? = R.buf(%d)' % (name, t.element_count))
            elif t.kind == T.CONSTANTARRAY:
                glob[b].append('@JvmField var %s: %s = %s' % (name, self.ktype(d.type, mode='array'), self.new_array(t)))
            elif init:
                glob[b].append('@JvmField var %s: %s = %s' % (name, ty, self.conv(self.val(init[-1]), init[-1].type, d.type).code))
            else:
                glob[b].append('@JvmField var %s: %s = %s' % (name, ty, self.zero(d.type)))
        names = sorted(set(files) | set(glob))
        imports = ['import kotlin.math.abs', 'import kotlin.math.sqrt', 'import kotlin.math.floor', 'import kotlin.math.ceil']
        for b in names:
            lines = ['// Generated from EPA SWMM 5.2.4 (%s) by tools/c2x/emit_kotlin.py. Do not edit by hand;' % b,
                     '// fix the translator, R.kt or Overrides.kt instead.',
                     FILE_HEAD + '@file:JvmName("%s")' % fkt(b),
                     'package swmm5', ''] + imports + ['']
            lines += glob.get(b, [])
            if glob.get(b):
                lines.append('')
            lines += files.get(b, [])
            open(os.path.join(outdir, fkt(b) + '.kt'), 'w').write('\n'.join(lines) + '\n')
        out = ['// Generated by tools/c2x/emit_kotlin.py from EPA SWMM 5.2.4 headers.', FILE_HEAD + 'package swmm5', '']
        for name, c in self.F.records.items():
            out += self.record(name, c)
        for sig, (name, ft) in self.delegates.items():
            out.append(self.delegate_decl_auto(name, ft))
        open(os.path.join(outdir, 'Types.kt'), 'w').write('\n'.join(out) + '\n')
        out = ['// Generated by tools/c2x/emit_kotlin.py from EPA SWMM 5.2.4 headers and string literals.',
               FILE_HEAD + '@file:JvmName("Consts")', 'package swmm5', '']
        for n, v in self.F.enum_consts.items():
            out.append('const val %s: Int = %s' % (kident(n), int_lit(v)))
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, s) in m.items():
                if n in self.macro_global and n not in done and kind in ('int', 'float') and n not in self.F.enum_consts:
                    done.add(n)
                    if kind == 'int':
                        v = re.sub(r'[uUlL]+$', '', s)
                        if len(v) > 1 and v.startswith('0'):
                            v = str(int(v, 8))
                        out.append('const val %s: Int = %s' % (kident(n), int_lit(int(v))))
                    else:
                        out.append('const val %s: Double = %s' % (kident(n), self.cs_float(s, 'd')))
        for bts, name in self.lits.items():
            out.append('@JvmField val %s: CPtr = R.lit(%s)' % (name, kt_string(bts)))
        open(os.path.join(outdir, 'Consts.kt'), 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = KotlinEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_kt')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
