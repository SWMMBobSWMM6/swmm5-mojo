"""
emit_groovy.py - EPA SWMM 5.2.4 C  ->  Groovy 3 with @CompileStatic (package swmm5: one class F_<file> per C file,
records and function-pointer interfaces in Types.groovy, enums, macros and string literals in Consts.groovy).

The Java back end (emit_java.py) supplies the analysis and the type model unchanged, because Groovy compiles to the
same JVM: char* -> CPtr, scalar pointer parameters -> DRef/IRef/LRef/FRef, locals whose address is taken -> boxes,
unsigned int -> long masked to 32 bits, double -> int through R.D2I (x86's rule, not the JVM's saturating one),
structs -> classes with copy(). Most of Java's syntax is also Groovy's. What Groovy changes, each written out here:

  * number literals: a decimal literal without a suffix is a BigDecimal (`0.1` is not a double), so every double
    literal carries `d`; `-0.0d` is folded to +0.0, so C's negative zero is R.NZ; the most negative int and long
    are Integer.MIN_VALUE and Long.MIN_VALUE (2147483648 is a long literal in Groovy)
  * `/` on two integers gives a BigDecimal: C's integer division is R.idiv / R.ldiv (truncating, as C)
  * float arithmetic is done in double: `a * b` on two floats is a double product. Each float-typed C operation is
    written ((float) (a op b)), which rounds once to float; for + - * / this equals the float operation, because a
    double holds more than 2 * 24 + 2 bits (double rounding is innocuous)
  * `switch` compiles to a chain of boxed isCase() calls, one case after another; it becomes an if / else-if chain
    on an int temporary, C's fall-through written out by appending the following case bodies (as the Kotlin back
    end does), inside a labelled do { } while (false) when a break leaves a case early. Every loop is labelled and
    every break and continue names its target
  * `==` on two objects calls equals(), and on two arrays compares their elements: pointer identity is `===`
  * a bare { } block is a closure or a compile error: nested C blocks are flattened (local names are unique per
    function, from the Java back end)
  * a field declared without a modifier is a property with a getter and a setter: every field is `public`
  * a statically imported field named like a class Groovy imports by default resolves to the class (`Node` is
    groovy.util.Node, `Stack` java.util.Stack): those two names get a trailing `_`, and every global and function
    of another file is written with its class (F_project.Node_), so nothing depends on static imports but the
    constants in Consts
  * an assignment to another object's field or another class's static field compiles to a boxed metaclass call
    (ScriptBytecodeAdapter.setProperty); `x.@f = v` is a plain putfield / putstatic, but `x.@f += v` and `x.@f++`
    read the field through another reflective call: such lvalues are written `x.@f = x.f op v`
  * `a > b` and `a >= b` on two doubles or floats compile to dcmpg, which answers true when either is NaN (C, and
    Java's dcmpl, answer false): they are written R.dgt(a, b) and R.dge(a, b), which compare b < a and b <= a
  * `a[i] /= y` compiles to dynamic getAt and div calls: written a[i] = a[i] / y; a constructor reference X::new
    compiles to a dynamic constructor call: written () -> new X()
  * a lambda's parameter types are written out (Groovy's type checker does not infer them from a generic
    constructor); single-quoted strings, so `$` is never interpolated

Written by Claude (Anthropic) for Robert Dickinson; see groovy/README.md.
"""
import os, re, sys, collections, struct, contextlib
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null
import emit_java
from emit_java import JavaEmitter, fclass, JAVA_RESERVED, JT, REFT, BOXT, MASK

# Groovy's own keywords, the classes of this port's runtime, and the two EPA names that clash with a class Groovy
# imports by default (the first builds resolved the globals Node and Stack to groovy.util.Node and java.util.Stack)
GROOVY_EXTRA = set('''as def in trait threadsafe it DElem IElem LElem FElem OElem DField IField LField FField OField
DAcc IAcc LAcc FAcc OAcc CharRef OdeDerivs GlibmRt FloatGetter FloatSetter FloatSupplier FloatConsumer CompileStatic
Node Stack'''.split())
GROOVY_RESERVED = JAVA_RESERVED | GROOVY_EXTRA


def gident(n):
    return n + '_' if n in GROOVY_RESERVED else n


@contextlib.contextmanager
def groovy_names():
    """the Java back end names everything through emit_java.jident; Groovy's rules while this back end runs"""
    old = emit_java.jident
    emit_java.jident = gident
    try:
        yield
    finally:
        emit_java.jident = old


def groovy_string(b):
    """a C string's bytes as a Groovy single-quoted string (no interpolation)"""
    out = []
    for ch in b:
        if ch == 0x5c:
            out.append('\\\\')
        elif ch == 0x27:
            out.append("\\'")
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
    return "'" + ''.join(out) + "'"


DEC_RE = re.compile(r'-?(\d+\.\d*([eE][-+]?\d+)?|\d+[eE][-+]?\d+)')
ZERO_RE = re.compile(r'\(?0\.0+[dDfF]?\)?')
TYPED = {'i': 'int', 'u': 'long', 'l': 'long', 'ul': 'long', 'd': 'double', 'f': 'float'}


SEL_RE = re.compile(r'^(.*[\w\])])\.([A-Za-z_]\w*)$', re.S)


def wlv(code):
    """the write form of an lvalue: Groovy 3's static compiler stores to another object's public field, or to another
    class's static field, through ScriptBytecodeAdapter.setProperty (boxed, through the metaclass); `x.@f = v` is a
    putfield / putstatic. Reads (`x.f`) are already a getfield / getstatic."""
    m = SEL_RE.match(code)
    if m and not m.group(1).endswith('.@'):
        return '%s.@%s' % (m.group(1), m.group(2))
    return code


CTOR_RE = re.compile(r'\b(\w+)::new\b')


def dotted(code):
    return SEL_RE.match(code) is not None


def dlit(code):
    """a double literal Groovy reads as a double"""
    return code + 'd' if DEC_RE.fullmatch(code) else code


class GroovyEmitter(JavaEmitter):
    def __init__(self, F):
        with groovy_names():
            super().__init__(F)
        self.jumps = []          # innermost last: ['loop', label] | ['switch', label, used]
        self.nlabel = 0

    # ================================================================== naming
    def def_key(self, d):
        """the (file, name) key of the function definition a call or a function value refers to"""
        keys = self.F.func_by_decl.get(d.spelling) or []
        cand = [k for k in keys if k[0] == self.cur_file] or \
               [k for k in keys if self.F.funcs[k].storage_class != front.ci.StorageClass.STATIC]
        return cand[0] if cand else None

    def qual_func(self, k):
        if k in OVERRIDES or k[0] in SKIP_FILES:
            return 'Overrides.' + self.fname[k]
        if k[0] == self.cur_file:
            return self.fname[k]
        return '%s.%s' % (fclass(k[0]), self.fname[k])

    def func_ref(self, d, cur_file):
        k = self.def_key(d)
        if k is None:
            return gident(d.spelling)
        return self.qual_func(k)

    def global_ref(self, d):
        k = self.global_key(d)
        if k is not None:
            b = self.F.global_owner[k]
            if b != self.cur_file:
                return '%s.%s' % (fclass(b), self.gname[k])
            return self.gname[k]
        if d.spelling in ('stdout', 'stderr'):
            return 'R.stdout'
        return gident(d.spelling)

    def rname(self, name):
        """a record's class name: Groovy cannot parse a declaration whose type name is lower-case (mempool.c's
        alloc_handle_t and two more, which nothing generated uses), so those get a C_ prefix"""
        n = gident(name)
        return 'C_' + n if n[:1].islower() else n

    def rec(self, t):
        return self.rname(record_name(t))

    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = 'L%d' % len(self.lits)
        return self.lits[b]

    # ================================================================== literals and conversions
    def zero(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0L', 'l': '0L', 'ul': '0L', 'd': '0.0d', 'f': '0.0f'}.get(tg, 'null')

    def as_bool(self, e):
        if e.tag in ('d', 'f'):
            return '(%s != 0.0d)' % e.code
        return super().as_bool(e)

    def x_FLOATING_LITERAL(self, c):
        e = super().x_FLOATING_LITERAL(c)
        if e.tag == 'd':
            return Ex(dlit(e.code), 'd')
        return e

    def x_INTEGER_LITERAL(self, c):
        e = super().x_INTEGER_LITERAL(c)
        if e.code == '-2147483648':
            return Ex('Integer.MIN_VALUE', e.tag)
        if e.code in ('-9223372036854775808L', '-9223372036854775808'):
            return Ex('Long.MIN_VALUE', e.tag)
        return e

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is not None and d.kind == K.FUNCTION_DECL:
            k = self.def_key(d)
            if k is None:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex(gident(d.spelling), 'o')
            q = self.qual_func(k)
            if '.' in q:
                cls, fn = q.rsplit('.', 1)
            else:
                cls, fn = fclass(k[0]), q
            return Ex('%s::%s' % (cls, fn), 'o')
        if d is not None and d.kind == K.VAR_DECL and not (d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL):
            gk = self.global_key(d)
            nm = self.global_ref(d)
            if gk in self.boxed_globals:
                return Ex(nm + '.v', ctag(d.type))
            return Ex(nm, ctag(d.type))
        return super().x_DECL_REF_EXPR(c)

    # ================================================================== operators
    def x_UNARY_OPERATOR(self, c):
        op = unop(c)
        if op == '-':
            a = kids(c)[0]
            e = self.val(a)
            if e.tag in ('d', 'f') and ZERO_RE.fullmatch(e.code):
                return Ex('R.NZ' if e.tag == 'd' else 'R.NZF', e.tag)     # Groovy folds -0.0d to +0.0
            if e.tag == 'f':
                return Ex('((float) (-%s))' % self.paren(e.code), 'f')
            if e.tag == 'u':
                return Ex('((-%s) & %s)' % (self.paren(e.code), MASK), 'u')
            return Ex('(-%s)' % self.paren(e.code), e.tag)
        return super().x_UNARY_OPERATOR(c)

    def arith(self, op, a, b, tg):
        if op == '/' and tg == 'i':
            return 'R.idiv(%s, %s)' % (a, b)
        if op == '/' and tg in ('l', 'ul', 'u'):
            return 'R.ldiv(%s, %s)' % (a, b)       # 'u' operands are non-negative longs
        if tg == 'f' and op in ('+', '-', '*', '/'):
            return '((float) (%s %s %s))' % (a, op, b)
        return super().arith(op, a, b, tg)

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
                if op in ('==', '!='):
                    # C compares addresses; Groovy's == would call equals() (element by element for arrays)
                    return Ex('(%s %s %s)' % (le.code, '===' if op == '==' else '!==', re_.code), 'b')
                return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
            if op in ('>', '>=') and (le.tag in ('d', 'f') or re_.tag in ('d', 'f')):
                # Groovy 3's static compiler writes > and >= on doubles with dcmpg, which makes a comparison with
                # NaN true; R.dgt(a, b) is b < a (both arguments evaluated first, a then b, as C's operands)
                return Ex('R.%s(%s, %s)' % ('dgt' if op == '>' else 'dge', le.code, re_.code), 'b')
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
            v = '((float) %s)' % v
        elif lt == 'i' and common in ('l', 'u', 'ul'):
            v = '((int) %s)' % v
        elif lt == 'u' and common != 'u':
            v = '(%s & %s)' % (v, MASK)
        if k[0] == 'char':
            if common in ('d', 'f'):
                v = 'R.D2I(%s)' % v
            return '%s.s(%s, %s)' % (self.paren(k[1]), k[2], v)
        if k[0] == 'ref':
            return '%s.set(%s)' % (k[1], v)
        # Groovy's x op= y is x = x op y with Groovy's operator: fine for + - * on matching types; not for integer /
        # (a BigDecimal), and a[i] /= y on an array element compiles to dynamic getAt and div calls even on doubles
        if dotted(k[1]):
            return '%s = %s' % (wlv(k[1]), v)          # x.@f op= v reads x.@f reflectively
        if common == lt and lt in ('d', 'i', 'l', 'ul') and op in ('+', '-', '*'):
            return '%s %s= %s' % (k[1], op, self.paren(re_.code))
        return '%s = %s' % (k[1], v)

    # constructor references X::new compile to a dynamic callConstructor; a lambda's `new X()` is static
    def alloc(self, call, t):
        e = super().alloc(call, t)
        return Ex(CTOR_RE.sub(r'(() -> new \1())', e.code), e.tag)

    def new_array(self, t):
        return CTOR_RE.sub(r'(() -> new \1())', super().new_array(t))

    # ================================================================== references
    def ref_of(self, a):
        """a reference object for lvalue a (lambda parameters typed: Groovy does not infer them)"""
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
                return 'new %sField<%s>(%s, (%s __o) -> __o.%s, (%s __o, %s __x) -> { __o.@%s = __x })' % (
                    REFT[tg][0], rt, obj, rt, attr, rt, TYPED[tg], attr)
            vt = self.jtype(sa.type)
            return 'new OField<%s, %s>(%s, (%s __o) -> __o.%s, (%s __o, %s __x) -> { __o.@%s = __x })' % (
                rt, vt, obj, rt, attr, rt, vt, attr)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, ix = kids(sa)
            if tg in REFT:
                return 'new %sElem(%s, %s)' % (REFT[tg][0], self.ex(base).code, self.idx(self.val(ix)))
            return 'new OElem<%s>(%s, %s)' % (self.jtype(sa.type), self.ex(base).code, self.idx(self.val(ix)))
        if sa.kind == K.DECL_REF_EXPR:
            if tg in REFT:
                return 'new %sAcc(() -> %s, (%s __x) -> { %s = __x })' % (REFT[tg][0], lv, TYPED[tg], wlv(lv))
            vt = self.jtype(sa.type)
            return 'new OAcc<%s>(() -> %s, (%s __x) -> { %s = __x })' % (vt, lv, vt, wlv(lv))
        self.problem(a, 'reference to %s' % lv)
        return 'null'

    def assign_code(self, l, rhs):
        k = self.lv_kind(l)
        if k[0] == 'plain':
            return '%s = %s' % (wlv(k[1]), rhs)
        return super().assign_code(l, rhs)

    def incdec_expr(self, a, op):
        k = self.lv_kind(a)
        tg = ctag(a.type)
        if k[0] == 'plain' and dotted(k[1]):
            lv = k[1]
            d = '+' if '++' in op else '-'
            pre = op.startswith('pre')
            if tg == 'c':
                nv = '(%s = %s.add(%s))' % (wlv(lv), self.paren(lv), '1' if d == '+' else '-1')
                return Ex(nv if pre else '%s.add(%s)' % (nv, '-1' if d == '+' else '1'), 'c')
            if tg == 'u':
                nv = '(%s = (%s %s 1L) & %s)' % (wlv(lv), lv, d, MASK)
                return Ex(nv if pre else '((%s %s 1L) & %s)' % (nv, '-' if d == '+' else '+', MASK), 'u')
            if tg in ('i', 'l', 'ul'):
                one = '1' if tg == 'i' else '1L'
                nv = '(%s = %s %s %s)' % (wlv(lv), lv, d, one)
                return Ex(nv if pre else '(%s %s %s)' % (nv, '-' if d == '+' else '+', one), tg)
            self.problems.append('%s on a %s field or global: %s' % (op, tg, lv))
        return super().incdec_expr(a, op)

    def libc(self, c, name, args):
        if name == 'memset':
            dst = strip(args[0])
            if dst.kind == K.UNARY_OPERATOR and unop(dst) == '&' and ctag(strip(kids(dst)[0]).type) == 'rec':
                o = strip(kids(dst)[0])
                return Ex('%s = new %s()' % (wlv(self.lvalue(o)), self.rec(o.type)), 'v')
        return super().libc(c, name, args)

    def init_list(self, c, t):
        t = canon(t)
        if t.kind == T.RECORD:
            items = kids(c)
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                if strip(it).kind == K.INIT_LIST_EXPR:
                    parts.append('__r.@%s = %s;' % (self.field(f.spelling), self.init_list(strip(it), f.type).code))
                else:
                    parts.append('__r.@%s = %s;' % (self.field(f.spelling), self.conv(self.val(it), it.type, f.type).code))
            rn = self.rec(t)
            return Ex('R.make(new %s(), (%s __r) -> { %s })' % (rn, rn, ' '.join(parts)), 'rec')
        return super().init_list(c, t)

    # ================================================================== statements
    def new_label(self, kind):
        self.nlabel += 1
        return 'L_%s%d' % (kind, self.nlabel)

    def stmt(self, c, ind):
        k = c.kind
        p = '    ' * ind
        if k == K.COMPOUND_STMT:
            # a nested C block: its statements, without braces (a bare { } is a closure in Groovy)
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
            head = self.flush([p + '%s: while (%s) {' % (lab, self.cond(ch[0]))], ind)
            self.jumps.append(['loop', lab])
            body = self.body(ch[1], ind)
            self.jumps.pop()
            return head + body + [p + '}']
        if k == K.DO_STMT:
            ch = kids(c)
            lab = self.new_label('d')
            self.jumps.append(['loop', lab])
            body = self.body(ch[0], ind)
            self.jumps.pop()
            tail = self.flush([p + '} while (%s);' % self.cond(ch[1])], ind)
            return [p + '%s: do {' % lab] + body + tail
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            j = self.jumps[-1]
            if j[0] == 'switch':
                j[2] = True
            return [p + 'break %s;' % j[1]]
        if k == K.CONTINUE_STMT:
            for j in reversed(self.jumps):
                if j[0] == 'loop':
                    return [p + 'continue %s;' % j[1]]
            self.problem(c, 'continue outside a loop')
            return []
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'return;']
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            if ctag(self.cur_ret) in ('c', 'o') and is_null(e.code):
                e = Ex('null', 'o')
            if self.post:
                self.tmp += 1
                t = '__r%d' % self.tmp
                return self.flush([p + '%s %s = %s;' % (self.jtype(self.cur_ret), t, e.code)], ind) + [p + 'return %s;' % t]
            return self.flush([p + 'return %s;' % e.code], ind)
        if k == K.NULL_STMT:
            return []
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unhandled statement %s' % k.name)
            return []
        return self.flush([p + self.expr_stmt_code(c) + ';'], ind)

    def flush(self, lines, ind):
        """put the set-up and copy-back statements a call's arguments needed around a statement"""
        if not self.pre and not self.post:
            return lines
        p = '    ' * ind
        pre, post = self.pre, self.post
        self.pre, self.post = [], []
        if post and any(re.match(r'^(return|if |\w+: |\} while)', l.strip()) for l in lines):
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
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            k = self.lv_kind(a)
            tg = ctag(a.type)
            d = '+' if '++' in unop(s) else '-'
            if k[0] == 'plain' and (tg == 'f' or dotted(k[1])):
                lv = k[1]
                if tg == 'f':
                    return '%s = ((float) (%s %s 1.0f))' % (wlv(lv), lv, d)
                if tg == 'c':
                    return '%s = %s.add(%s1)' % (wlv(lv), self.paren(lv), '' if d == '+' else '-')
                if tg == 'u':
                    return '%s = (%s %s 1L) & %s' % (wlv(lv), lv, d, MASK)
                return '%s = %s %s %s' % (wlv(lv), lv, d, {'i': '1', 'd': '1.0d'}.get(tg, '1L'))
        return super().expr_stmt_code(c)

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
        init_s = ''
        if init is not None:
            if init.kind == K.DECL_STMT:
                for d in kids(init):
                    out += self.flush(self.local_decl(d, ind), ind)
            else:
                init_s = self.expr_stmt_code(init).replace('; ', ', ')
                if self.pre or self.post:
                    self.problems.append('call set-up inside a for initialiser')
        cond_s = self.cond(cond) if cond is not None else ''
        if self.pre or self.post:
            self.problems.append('call set-up inside a for condition')
        inc_s = self.expr_stmt_code(inc).replace('; ', ', ') if inc is not None else ''
        if self.pre or self.post:
            self.problems.append('call set-up inside a for increment')
        lab = self.new_label('f')
        self.jumps.append(['loop', lab])
        b = self.body(body, ind)
        self.jumps.pop()
        out.append(p + '%s: for (%s; %s; %s) {' % (lab, init_s, cond_s, inc_s))
        out += b
        out.append(p + '}')
        return out

    def switch(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        e = self.val(ch[0])
        code = e.code if e.tag != 'b' else '(%s ? 1 : 0)' % e.code
        if e.tag in ('l', 'u', 'ul'):
            code = '((int) (%s))' % code
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
        head = self.flush([], ind)
        self.tmp += 1
        sv = '__sw%d' % self.tmp
        lab = self.new_label('s')
        jump = ['switch', lab, False]
        self.jumps.append(jump)
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
            # a break that ends the case body just leaves the switch
            if stmts and stmts[-1].kind == K.BREAK_STMT:
                stmts = stmts[:-1]
            lines = []
            for s in stmts:
                lines += self.stmt(s, ind + 1)
                if not self.completes(s):
                    break
            if None in labels:
                # case labels sharing the default's body need no test of their own (case values are distinct)
                default = lines
            else:
                branches.append((labels, lines))
        self.jumps.pop()
        chain = []
        for bi, (labels, lines) in enumerate(branches):
            test = ' || '.join('%s == %s' % (sv, x) for x in labels)
            chain.append(p + ('if (%s) {' if bi == 0 else '} else if (%s) {') % test)
            chain += lines
        if default is not None:
            if branches:
                chain.append(p + '} else {')
                chain += default
            else:
                chain += [p + 'if (true) {'] + default
        if chain:
            chain.append(p + '}')
        out = head + [p + 'int %s = %s;' % (sv, code)]
        if jump[2]:
            # a break before the end of a case body: the chain sits in a labelled one-pass loop
            return out + [p + '%s: do {' % lab] + ['    ' + l for l in chain] + [p + '} while (false);']
        return out + chain

    def seq_completes(self, stmts):
        for s in stmts:
            if not self.completes(s):
                return False
        return True

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
        lines = self.stmt(body, 2)
        rt = self.jtype(c.result_type)
        out = ['    // %s:%d' % (b, c.location.line), '    static %s %s(%s) {' % (rt, self.fname[key], ', '.join(ps))]
        out += pre + lines
        if rt != 'void' and not (lines and re.match(r'^\s*return\b', lines[-1])):
            out.append('        throw new IllegalStateException(\'%s: no return\');' % n)
        out.append('    }')
        return out

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = self.rname(name)
        out = ['@CompileStatic', 'final class %s {' % nm]
        cp = ['    %s copy() {' % nm, '        %s c = new %s();' % (nm, nm)]
        for f in fields:
            t = canon(f.type)
            fn = self.field(f.spelling)
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    out.append('    public CPtr %s = R.buf(%d);' % (fn, t.element_count))
                    cp.append('        c.@%s = R.copyBuf(%s);' % (fn, fn))
                else:
                    ty = self.jtype(f.type, mode='array')
                    out.append('    public %s %s = %s;' % (ty, fn, self.new_array(t)))
                    if et.kind == T.RECORD:
                        cp.append('        c.@%s = R.copyRecs(%s, new %s[%s.length]);' % (fn, fn, self.rec(et), fn))
                    elif et.kind == T.CONSTANTARRAY:
                        cp.append('        c.@%s = R.cloneGrid(%s);' % (fn, fn))
                    else:
                        cp.append('        c.@%s = R.dup(%s);' % (fn, fn))   # array.clone() fails verification
            elif t.kind == T.RECORD:
                out.append('    public %s %s = new %s();' % (self.rec(t), fn, self.rec(t)))
                cp.append('        c.@%s = %s.copy();' % (fn, fn))
            else:
                ty = self.jtype(f.type, f)
                if ty in REFT.values():
                    self.problems.append('ref field %s.%s' % (name, f.spelling))
                out.append('    public %s %s = %s;' % (ty, fn, self.zero(f.type)))
                cp.append('        c.@%s = %s;' % (fn, fn))
        cp += ['        return c;', '    }']
        return out + cp + ['}', '']

    def global_decl(self, k, c):
        with groovy_names():
            line = super().global_decl(k, c)
        assert line.startswith('    static '), line
        return '    public static ' + line[len('    static '):]

    def emit(self, outdir):
        with groovy_names():
            return self._emit(outdir)

    def _emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        for f in os.listdir(outdir):
            if f.startswith('F_') and f.endswith('.groovy') or f in ('Types.groovy', 'Consts.groovy'):
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
                glob[b].append('    public static %s %s = %s;' % (self.jtype(d.type, mode='array'), name, self.init_list(strip(init[-1]), t).code))
            elif ctag(t) == 'c' and t.kind == T.CONSTANTARRAY:
                if init:
                    glob[b].append('    public static CPtr %s = R.bufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count))
                else:
                    glob[b].append('    public static CPtr %s = R.buf(%d);' % (name, t.element_count))
            elif t.kind == T.CONSTANTARRAY:
                glob[b].append('    public static %s %s = %s;' % (self.jtype(d.type, mode='array'), name, self.new_array(t)))
            elif init:
                glob[b].append('    public static %s %s = %s;' % (ty, name, self.conv(self.val(init[-1]), init[-1].type, d.type).code))
            else:
                glob[b].append('    public static %s %s = %s;' % (ty, name, self.zero(d.type)))
        names = sorted(set(files) | set(glob))
        imports = ['import groovy.transform.CompileStatic', 'import static swmm5.Consts.*']
        for b in names:
            lines = ['// Generated from EPA SWMM 5.2.4 (%s) by tools/c2x/emit_groovy.py. Do not edit by hand;' % b,
                     '// fix the translator, R.groovy or Overrides.groovy instead.',
                     'package swmm5', ''] + imports + ['', '@CompileStatic', 'final class %s {' % fclass(b)]
            lines += glob.get(b, [])
            if glob.get(b):
                lines.append('')
            lines += files.get(b, [])
            lines += ['}']
            open(os.path.join(outdir, fclass(b) + '.groovy'), 'w').write('\n'.join(lines) + '\n')
        out = ['// Generated by tools/c2x/emit_groovy.py from EPA SWMM 5.2.4 headers.', 'package swmm5', '',
               'import groovy.transform.CompileStatic', 'import static swmm5.Consts.*', '']
        for name, c in self.F.records.items():
            out += self.record(name, c)
        for sig, (name, ft) in self.delegates.items():
            out.append(self.delegate_decl_auto(name, ft))
        open(os.path.join(outdir, 'Types.groovy'), 'w').write('\n'.join(out) + '\n')
        out = ['// Generated by tools/c2x/emit_groovy.py from EPA SWMM 5.2.4 headers and string literals.', 'package swmm5', '',
               'import groovy.transform.CompileStatic', '', '@CompileStatic', 'final class Consts {']
        for n, v in self.F.enum_consts.items():
            out.append('    public static final int %s = %s;' % (gident(n), 'Integer.MIN_VALUE' if v == -(1 << 31) else v))
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, s) in m.items():
                if n in self.macro_global and n not in done and kind in ('int', 'float') and n not in self.F.enum_consts:
                    done.add(n)
                    if kind == 'int':
                        v = re.sub(r'[uUlL]+$', '', s)
                        if len(v) > 1 and v.startswith('0'):
                            v = str(int(v, 8))
                        out.append('    public static final int %s = %s;' % (gident(n), v))
                    else:
                        out.append('    public static final double %s = %s;' % (gident(n), dlit(self.cs_float(s, 'd'))))
        for bts, name in self.lits.items():
            out.append('    public static final CPtr %s = R.lit(%s);' % (name, groovy_string(bts)))
        out.append('}')
        open(os.path.join(outdir, 'Consts.groovy'), 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = GroovyEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_groovy')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
