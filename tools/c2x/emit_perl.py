"""
emit_perl.py - EPA SWMM 5.2.4 C  ->  Perl 5.38 (one file, perl/swmm5/engine.pl, package SWMM5)

Reuses the C# and Python emitters' analysis (pointer modes, names, literals) and writes Perl. Perl has C's
`if`, `while`, `for` and its own `last`/`next`; what it does not have, and what it does differently with numbers, is
handled here or in perl/swmm5/crt.pl:

  records       a C struct is an array reference with one slot per field; the field indices are constants
                (`$Node->[$j][TNode_newDepth]`), which Perl inlines at compile time. A struct's own arrays and
                structs are copied by clone_<Type>, as C's struct assignment copies them
  arrays        Perl array references: copying the reference shares the array, as copying a C pointer does.
                The one array that is too big for Perl scalars (TUHData.pastRain, RDII rainfall history: 3.4 GB in
                C on one corpus model) is a packed string of doubles, read and written with unpack/substr
  char*         a CPtr, [\\$buffer, $offset]: a reference to a byte string and an offset, read and written through
                the runtime's cg/cs; NULL is undef
  T* params     a scalar pointer that is only dereferenced (PtrInfo mode 'ref') becomes an alias of the caller's
                variable: Perl passes arguments by alias in @_, and `\\my $h1 = \\$_[3];` (refaliasing) names it
  integers      Perl's `/` is a float division: C's int `/` is int(a / b) (exact for 32-bit operands); `%` follows
                the sign of the right operand in Perl, so C's `%` is rt_imod (under `use integer`); `>>` of a
                signed int is done under `use integer`; bitwise results of signed ints go through rt_i32
  doubles       Perl adds, subtracts and multiplies two doubles that hold integral values as 64-bit integers
                ("IV preservation"), exactly. The result is C's except in the sign of a zero: 0.0 * -3.0 is +0 in
                Perl and -0.0 in C, which C prints as "-0.00". So a double +, - or * whose operands could both be
                integral is written `((A * B) || rt_zm(A, B))`: a nonzero (or NaN) result is kept, a zero result
                is recomputed by the runtime with C's sign rules (rt_za, rt_zs for + and -; operands with side
                effects go through temporaries). Unary minus and ** likewise. No fix where it cannot matter: a
                literal operand that is not an integer (0.5, 32.2) keeps Perl off the integer path, and C's sum or
                difference cannot be -0.0 when an operand is a literal or a converted C integer (zfix())
  division      `/` dies on a zero divisor in Perl: ($d == 0.0 ? rt_fdiv0(A, $d) : A / $d)
  double -> int Perl's int() of NaN is NaN: C's (int) is x86's cvttsd2si (INT_MIN for NaN and out of range)
  float         rt_f32 rounds to single precision as C's (float) does (pack('f') sends values just above
                FLT_MAX to infinity, which C does not)
  math.h        exp, sin, cos, ** and POSIX's tan, asin, acos, atan, log10, floor, ceil call glibc; Perl's log
                and sqrt die where C returns -inf or NaN, POSIX::floor/ceil keep a signaling NaN, and ** of two
                integral values is Perl's own exact integer power: a zero result, or one beyond 2**53, is recomputed
                by rt_cpow through glibc's pow (POSIX::pow cannot do it: POSIX.pm defines it as Perl's **)
  switch        an if/elsif chain when no case falls through; otherwise a labelled bare block (SWn: { ... })
                with a fall-through flag, `break` being `last SWn`. A `continue` that crosses such a block is
                `next Ln` to the enclosing loop's label
  do-while      `while (1) { ...; last unless (cond); }` (Perl's do {} while is not a loop: last/next do not work)
  locals        declared once at the top of the sub (`my (...)`); a C local without an initializer is set to 0, 0.0
                or undef where C declares it (warnings are fatal, so reading an undefined value would stop the
                run), unless its first use in the block is a plain assignment (mark_assigned_first)
  comma         do { A; B }
  function ptrs code references (\\&name), called as $f->(...)
"""
import os, re, sys, collections, struct
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import CSEmitter, Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null
from emit_py import PyEmitter
from emit_php import round_f32

# words a Perl sub cannot be named (keywords and quote-like operators; Perl's named built-in functions are checked
# separately: no EPA function is named like one, see check_names)
PERL_KEYWORDS = set('''if unless else elsif while until for foreach do sub my our local state return last next redo goto
q qq qw qr qx m s tr y x lt gt le ge eq ne cmp and or not xor BEGIN END INIT CHECK UNITCHECK DESTROY AUTOLOAD
__FILE__ __LINE__ __PACKAGE__ __DATA__ __END__ __SUB__ CORE'''.split())
# variable names Perl gives a meaning of its own
PERL_SPECIAL_VARS = {'a', 'b', '_', 'ARGV', 'ENV', 'INC', 'STDIN', 'STDOUT', 'STDERR', 'ARGVOUT', 'SIG', '0'}
# (struct, field) pairs kept as packed doubles
PACKED = {('TUHData', 'pastRain')}

FLOAT_RE = re.compile(r'\(?-?(\d+\.\d*|\d*\.\d+|\d+)([eE][-+]?\d+)?\)?')


def perl_bytes(b):
    """bytes as a Perl double-quoted string literal ($, @ and \\ escaped, everything else outside ASCII as \\xHH)"""
    out = []
    for ch in b:
        if ch == 0x5c:
            out.append('\\\\')
        elif ch == 0x22:
            out.append('\\"')
        elif ch == 0x24:
            out.append('\\$')
        elif ch == 0x40:
            out.append('\\@')
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


def is_simple(code):
    """a variable, possibly followed by ->[...] / [...] subscripts, or a number: safe to read twice"""
    if re.fullmatch(r'\(?-?\d+(\.\d*)?([eE][-+]?\d+)?\)?', code) or code == 'undef':
        return True
    m = re.match(r'\$\w+', code)
    if not m:
        return False
    i = m.end()
    n = len(code)
    while i < n:
        if code.startswith('->[', i):
            i += 2
        if i < n and code[i] == '[':
            d = 0
            j = i
            while j < n:
                if code[j] in '[(':
                    d += 1
                elif code[j] in '])':
                    d -= 1
                    if d == 0:
                        break
                j += 1
            if j >= n or code[j] != ']':
                return False
            inner = code[i + 1:j]
            if not (is_pure(inner) or re.fullmatch(r'\w+', inner)):
                return False
            i = j + 1
        else:
            return False
    return True


def is_pure(code):
    """code that has no side effect and calls nothing (variables, subscripts, numbers, arithmetic, comparisons):
    safe to evaluate twice"""
    if is_simple(code):
        return True
    if re.search(r'(?<![=!<>])=(?!=)|\+\+|--|[\w\]>}]\s*\(|\bdo\b|\bsub\b|[{};]', code):
        return False
    return bool(re.fullmatch(r'[\w$\[\]()\-> .+*/<=!&|?:]+', code))


def float_lit(x):
    """a double as a Perl literal (shortest round-trip decimal; perl/test/run_literals.sh checks Perl reads each back)"""
    if x != x:
        return 'NAN_'
    if x in (float('inf'), float('-inf')):
        return 'INF_' if x > 0 else '(-INF_)'
    s = repr(x)
    if 'e' not in s and '.' not in s:
        s += '.0'
    if s.startswith('-'):
        return '(' + s + ')'
    return s


def nonintegral_literal(code):
    """a float literal whose value is not an integer: an operand that keeps Perl's arithmetic in doubles"""
    if not FLOAT_RE.fullmatch(code):
        return False
    try:
        v = float(code.strip('()'))
    except ValueError:
        return False
    return v == v and v not in (float('inf'), float('-inf')) and v != int(v)


class PerlEmitter(PyEmitter):
    def __init__(self, F):
        CSEmitter.__init__(self, F)
        cnt = collections.Counter()
        for (b, n) in F.funcs:
            cnt[n] += 1
        for k, c in F.globals.items():
            cnt[c.spelling] += 1
        self.fname = {}
        for (b, n), c in F.funcs.items():
            base = b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n
            if base in PERL_KEYWORDS or base.startswith(('c_', 'rt_', 'new_', 'clone_')):
                base += '_'
            self.fname[(b, n)] = base
        self.gname = {}
        for k, c in F.globals.items():
            b = F.global_owner[k]
            n = c.spelling
            base = b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n
            if base in PERL_SPECIAL_VARS:
                base += '_'
            self.gname[k] = base
        self.global_names = set(self.gname.values())
        self.tmp_count = 0
        self.literals = {}          # float literal text -> bits (for perl/test)
        self.rec_fields = collections.OrderedDict()

    # ================================================================== naming
    def global_ref(self, d):
        k = decl_key(d)
        if k in self.gname:
            nm = self.gname[k]
        else:
            nm = None
            for gk, c in self.F.globals.items():
                if c.spelling == d.spelling and not front.is_static(c):
                    nm = self.gname[gk]
                    break
            if nm is None:
                if d.spelling in ('stdout', 'stderr'):
                    return 'rt_%s()' % d.spelling
                nm = d.spelling
        return '$' + nm

    def static_local_name(self, d):
        nm = '%s_%s' % (self.fname.get((self.cur_file, d.semantic_parent.spelling), d.semantic_parent.spelling).rstrip('_'), d.spelling)
        self.global_names.add(nm)
        return nm

    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = '$L%d' % len(self.lits)
        return self.lits[b]

    def rec(self, t):
        return record_name(t)

    def field(self, rec, name):
        return '%s_%s' % (rec, name)

    def tmp(self, stem='t'):
        self.tmp_count += 1
        nm = '$__%s%d' % (stem, self.tmp_count)
        self.temps.append(nm)
        return nm

    def paren(self, s):
        if is_simple(s) or (s.startswith('(') and s.endswith(')') and self._balanced(s[1:-1])):
            return s
        return '(' + s + ')'

    def to_f(self, code):
        if re.fullmatch(r'-?\d+', code):
            v = code + '.0'
            return '(%s)' % v if v.startswith('-') else v
        return code

    # ================================================================== conversions
    def to_ctype(self, e, t):
        want = ctag(t)
        if e.tag in ('b', 'L') and want in NUMTAGS:
            if want in ('d', 'f'):
                return Ex('(%s ? 1.0 : 0.0)' % e.code, want)
            return Ex('(%s ? 1 : 0)' % e.code, want)
        return e

    def as_bool(self, e):
        # Perl's truth of a number is C's: 0, 0.0 and -0.0 are false, NaN is true; undef (NULL) is false
        if e.tag in ('b', 'L'):
            return e.code
        if e.tag in ('i', 'u', 'l', 'ul'):
            return '(%s != 0)' % e.code
        if e.tag in ('d', 'f'):
            return '(%s != 0.0)' % e.code
        return 'defined(%s)' % e.code

    def d2i(self, code, lo='-2147483649.0', hi='2147483648.0', minv='-2147483648'):
        """C's (int)x on x86-64: truncation in range; NaN and out of range give INT_MIN"""
        if is_pure(code):
            code = self.paren(code)
            return '((%s < %s && %s > %s) ? int(%s) : %s)' % (code, hi, code, lo, code, minv)
        t = self.tmp('i')
        return '(((%s = %s) < %s && %s > %s) ? int(%s) : %s)' % (t, code, hi, t, lo, t, minv)

    def conv(self, e, src_t, dst_t):
        s, d = ctag(src_t), ctag(dst_t)
        if e.tag in ('b', 'L') and d in NUMTAGS:
            e = Ex('(%s ? 1 : 0)' % e.code, 'i'); s = 'i'
        if s == d or d in ('v', '?', 'rec'):
            return Ex(e.code, d if d not in ('?',) else e.tag)
        if d == 'i':
            if s in ('d', 'f'):
                return Ex(self.d2i(e.code), 'i')
            if s in ('l', 'u', 'ul'):
                return Ex('rt_i32(%s)' % e.code, 'i')
            return Ex(e.code, 'i')
        if d in ('l', 'ul'):
            if s in ('d', 'f'):
                return Ex('rt_d2l(%s)' % e.code, d)
            return Ex(e.code, d)
        if d == 'u':
            if s in ('d', 'f'):
                return Ex('(rt_d2l(%s) & 0xFFFFFFFF)' % e.code, 'u')
            return Ex('(%s & 0xFFFFFFFF)' % self.paren(e.code), 'u')
        if d == 'd':
            if s in ('i', 'u', 'l', 'ul'):
                return Ex(self.to_f(e.code), 'd')
            return Ex(e.code, 'd')
        if d == 'f':
            return Ex('rt_f32(%s)' % self.to_f(e.code), 'f')
        if d in ('c', 'o'):
            if self.is_undef(e.code) or e.tag == 'n':
                return Ex('undef', d)
            return Ex(e.code, d)
        return e

    def zero(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0', 'l': '0', 'ul': '0', 'd': '0.0', 'f': '0.0'}.get(tg, 'undef')

    # ================================================================== leaves
    def x_INTEGER_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'\d+[uUlL]*', toks[0]):
            s = re.sub(r'[uUlL]+$', '', toks[0])
            if len(s) > 1 and s.startswith('0'):
                s = str(int(s, 8))
            return Ex(s, tg)
        if len(toks) == 1 and re.fullmatch(r'0[xX][0-9a-fA-F]+[uUlL]*', toks[0]):
            return Ex(str(int(re.sub(r'[uUlL]+$', '', toks[0]), 16)), tg)
        v = evaluate(c)
        if v is None:
            self.problem(c, 'integer literal %s' % toks)
        x = v[1] if v else 0
        return Ex(str(x) if x >= 0 else '(%d)' % x, tg)

    def flit(self, x):
        s = float_lit(x)
        self.literals[s] = struct.unpack('<Q', struct.pack('<d', x))[0]
        return s

    def x_FLOATING_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?[fFlL]?', toks[0]):
            s = toks[0].rstrip('fFlL')
            if tg == 'f':
                return Ex(self.flit(round_f32(s)), tg)
            return Ex(self.flit(float(s)), tg)
        v = evaluate(c)
        if v is None:
            self.problem(c, 'floating literal %s' % toks)
        x = v[1] if v else 0.0
        if tg == 'f':
            x = struct.unpack('<f', struct.pack('<f', x))[0]
        return Ex(self.flit(x), tg)

    def x_CHARACTER_LITERAL(self, c):
        v = evaluate(c)
        x = v[1] if v else 0
        return Ex(str(x) if x >= 0 else '(%d)' % x, 'i')

    def x_STRING_LITERAL(self, c):
        return Ex(self.lit(self.string_bytes(c)), 'c')

    def x_CXX_UNARY_EXPR(self, c):
        v = evaluate(c)
        return Ex(str(v[1]) if v else '8', 'ul')

    def x_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        return Ex(self.paren(e.code), e.tag)

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            self.problem(c, 'unresolved name %s' % c.spelling)
            return Ex('$' + c.spelling, '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            v = d.enum_value
            return Ex(str(v) if v >= 0 else '(%d)' % v, 'i')
        if d.kind == K.FUNCTION_DECL:
            n = self.func_ref(d, self.cur_file)
            if n is None:
                self.problem(c, 'function value %s' % d.spelling)
                n = d.spelling
            return Ex('\\&%s' % n, 'o')
        if d.kind == K.PARM_DECL or (d.kind == K.VAR_DECL and d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL and d.storage_class != front.ci.StorageClass.STATIC):
            return Ex('$' + self.local_name(d), ctag(d.type))
        if d.kind == K.VAR_DECL:
            if d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL:
                return Ex('$' + self.static_local_name(d), ctag(d.type))
            return Ex(self.global_ref(d), ctag(d.type))
        self.problem(c, 'name %s' % c.spelling)
        return Ex('$' + c.spelling, ctag(c.type))

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                return Ex(self.zero(c.type), ctag(c.type))
            return self.ex(ch[0])
        e = self.ex(ch[0])
        if canon(c.type).kind == T.POINTER and e.tag == 'i' and e.code == '0':
            return Ex('undef', ctag(c.type))
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
        if (e.tag == 'i' and e.code == '0' and canon(c.type).kind == T.POINTER) or self.is_undef(e.code):
            return Ex('undef', ctag(c.type))
        if ctag(c.type) == 'o' and ctag(inner.type) == 'o':
            return e
        return self.conv(self.to_ctype(e, inner.type), inner.type, c.type)

    # ================================================================== lvalues
    def packed_member(self, base):
        """the MEMBER_REF cursor of a packed field, if base is one"""
        sb = strip(base)
        if sb.kind == K.MEMBER_REF_EXPR and sb.referenced is not None:
            p = sb.referenced.semantic_parent
            if p is not None and (record_name(p.type), sb.referenced.spelling) in PACKED:
                return sb
        return None

    def elem_kind(self, a):
        """'char' for a char reached through a char pointer (cg/cs), 'packed' for a packed double, else None"""
        sa = strip(a)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base = kids(sa)[0]
            if ptr_category(base.type) == 'char':
                return 'char'
            if self.packed_member(base) is not None:
                return 'packed'
            return None
        if sa.kind == K.UNARY_OPERATOR and unop(sa) == '*' and ptr_category(kids(sa)[0].type) == 'char':
            return 'char'
        return None

    def elem_parts(self, a):
        """(pointer code, index code) of a char or packed element"""
        sa = strip(a)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sa)
            return self.ex(base).code, self.val(idx).code
        p = kids(sa)[0]
        sp = strip(p)
        if sp.kind == K.BINARY_OPERATOR and binop(sp) in ('+', '-') and ptr_category(kids(sp)[0].type) == 'char':
            l, r = kids(sp)
            i = self.val(r).code
            return self.ex(l).code, (i if binop(sp) == '+' else '-' + self.paren(i))
        return self.ex(p).code, '0'

    def store(self, l, rhs):
        """C's l = rhs as a Perl expression whose value is the stored value"""
        k = self.elem_kind(l)
        if k == 'char':
            p, i = self.elem_parts(l)
            return 'cs(%s, %s, %s)' % (p, i, rhs)
        if k == 'packed':
            p, i = self.elem_parts(l)
            return 'rt_pset(%s, %s, %s)' % (p, i, rhs)
        return '(%s = %s)' % (self.lvalue(l), rhs)

    def store_stmt(self, l, rhs):
        k = self.elem_kind(l)
        if k:
            return self.bare(self.store(l, rhs))
        return '%s = %s' % (self.lvalue(l), self.bare(rhs))

    def _assign_value(self, l, rhs, tg):
        return Ex(self.store(l, rhs), tg)

    # ================================================================== operators
    @staticmethod
    def int_sourced(c):
        """an operand that is a C integer converted to double: it can be 0.0 but never -0.0"""
        if c is None:
            return False
        x = c
        while True:
            if x.kind == K.PAREN_EXPR:
                x = kids(x)[0]
                continue
            if x.kind in (K.UNEXPOSED_EXPR, K.CSTYLE_CAST_EXPR) and kids(x):
                inner = kids(x)[-1]
                if ctag(inner.type) in ('i', 'u', 'l', 'ul'):
                    return True
                if ctag(inner.type) == ctag(x.type):
                    x = inner
                    continue
            return False

    def zfix(self, op, le, re_, l=None, r=None):
        """a double +, - or * with C's sign of a zero result (see the header). The fix is left out where C's result
        cannot be -0.0 anyway: a sum with an operand that cannot be -0.0 (a literal, or an integer converted to
        double), a difference whose left operand cannot be -0.0 or whose right one is a nonzero literal"""
        if FLOAT_RE.fullmatch(le) and FLOAT_RE.fullmatch(re_):
            # two constants: C's compiler folds them in double arithmetic, and so does Python
            x, y = float(le.strip('()')), float(re_.strip('()'))
            return self.flit({'+': x + y, '-': x - y, '*': x * y}[op])
        if nonintegral_literal(le) or nonintegral_literal(re_):
            return '(%s %s %s)' % (le, op, re_)

        def not_negzero(code, cur):
            return bool(FLOAT_RE.fullmatch(code) or re.fullmatch(r'\(?-?\d+\)?', code)) or self.int_sourced(cur)

        def nonzero_lit(code):
            return bool(FLOAT_RE.fullmatch(code)) and float(code.strip('()')) != 0.0
        if op == '+' and (not_negzero(le, l) or not_negzero(re_, r)):
            return '(%s + %s)' % (le, re_)
        if op == '-' and (not_negzero(le, l) or nonzero_lit(re_)):
            return '(%s - %s)' % (le, re_)
        helper = {'+': 'rt_za', '-': 'rt_zs', '*': 'rt_zm'}[op]
        a, b = le, re_
        ea, eb = a, b
        if not is_pure(a) or not is_pure(b):
            # operands with calls or side effects are evaluated once, in C's order, into temporaries
            if not is_pure(a):
                a = self.tmp('a')
                ea = '(%s = %s)' % (a, le)
            if not is_pure(b):
                b = self.tmp('b')
                eb = '(%s = %s)' % (b, re_)
        return '((%s %s %s) || %s(%s, %s))' % (ea, op, eb, helper, a, b)

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
        tg = ctag(c.type)
        if op == '-':
            if tg in ('d', 'f'):
                if re.fullmatch(r'\d+(\.\d*)?([eE][-+]?\d+)?', e.code):
                    v = float(e.code)
                    return Ex(self.flit(-v) if v != 0 else '(-0.0)', tg)
                if self.int_sourced(a):
                    return Ex('(-%s)' % self.paren(e.code), tg)
                if is_pure(e.code):
                    x = self.paren(e.code)
                    return Ex('(-%s || rt_zn(%s))' % (x, x), tg)
                t = self.tmp('n')
                return Ex('(-(%s = %s) || rt_zn(%s))' % (t, e.code, t), tg)
            if re.fullmatch(r'\d+', e.code):
                return Ex('(-%s)' % e.code, e.tag) if tg != 'u' else Ex('(-%s & 0xFFFFFFFF)' % e.code, 'u')
            code = '(-%s)' % self.paren(e.code)
            if tg == 'u':
                code = '(%s & 0xFFFFFFFF)' % code
            return Ex(code, e.tag)
        if op == '+':
            return e
        if op == '~':
            code = '(~%s)' % self.paren(e.code)
            code = '(%s & 0xFFFFFFFF)' % code if tg == 'u' else 'rt_i32(%s)' % code
            return Ex(code, e.tag)
        self.problem(c, 'unary ' + op)
        return e

    def incdec_expr(self, a, op):
        """++/-- used as a value"""
        d = '+' if '++' in op else '-'
        tg = ctag(a.type)
        k = self.elem_kind(a)
        if k:
            if k == 'packed':
                self.problem(a, 'increment of a packed element')
            p, i = self.elem_parts(a)
            if op.startswith('pre'):
                return Ex('cs(%s, %s, cg(%s, %s) %s 1)' % (p, i, p, i, d), tg)
            return Ex('rt_first(cg(%s, %s), cs(%s, %s, cg(%s, %s) %s 1))' % (p, i, p, i, p, i, d), tg)
        lv = self.lvalue(a)
        if tg == 'c':
            if not is_simple(lv):
                self.problem(a, 'increment of a pointer expression with side effects: %s' % lv)
            if op.startswith('pre'):
                return Ex('(%s = cadd(%s, %s1))' % (lv, lv, '' if d == '+' else '-'), 'c')
            return Ex('rt_first(%s, %s = cadd(%s, %s1))' % (lv, lv, lv, '' if d == '+' else '-'), 'c')
        if tg in ('i', 'l', 'ul', 'd'):
            # Perl's ++/-- on a number: +1 / -1 (exact for doubles: x - 1 is never -0.0)
            return Ex('(%s%s%s)' % (lv, d, d) if op.startswith('post') else '(%s%s%s)' % (d, d, lv), tg)
        if not is_simple(lv):
            self.problem(a, 'increment of an expression with side effects: %s' % lv)
        nv = '%s %s %s' % (lv, d, '1.0' if tg == 'f' else '1')
        nv = 'rt_f32(%s)' % nv if tg == 'f' else '(%s) & 0xFFFFFFFF' % nv
        if op.startswith('pre'):
            return Ex('(%s = %s)' % (lv, nv), tg)
        return Ex('rt_first(%s, %s = %s)' % (lv, lv, nv), tg)

    def check_rec_store(self, l):
        """*p = struct through a pointer variable would only rebind the Perl variable, not copy into the caller's
        struct: flag it (EPA has none)"""
        sl = strip(l)
        if sl.kind == K.UNARY_OPERATOR and unop(sl) == '*':
            self.problem(l, 'struct assigned through a pointer')
        if sl.kind == K.DECL_REF_EXPR and sl.referenced is not None and sl.referenced.kind == K.PARM_DECL:
            self.problem(l, 'struct parameter assigned')

    def deref(self, a):
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            p, i = self.elem_parts(Wrap(a))
            return Ex('cg(%s, %s)' % (p, i), 'i')
        e = self.ex(a)
        if cat == 'record':
            return Ex(e.code, 'rec')
        mode = self.mode_of_expr(sa)
        pt = ctag(canon(a.type).get_pointee())
        if mode == 'ref':
            return Ex(e.code, pt)
        if sa.kind == K.BINARY_OPERATOR:
            l, r = kids(sa)
            return Ex('%s->[%s]' % (self.paren(self.ex(l).code), self.val(r).code), pt)
        return Ex('%s->[0]' % self.paren(e.code), pt)

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
                return Ex(b if i == '0' else 'cadd(%s, %s)' % (b, i), 'c')
            if ctag(sa.type) == 'rec':
                return Ex(self.ex(sa).code, 'o')
            i = self.val(idx).code
            if i == '0':
                return Ex(self.ex(base).code, 'o')
        # &scalar: legal only where an aliased parameter takes it (arg(), scan targets)
        return Ex(self.lvalue(sa), 'ref')

    def fdiv_code(self, le, re_, r):
        """C double division: Perl's `/` dies on a zero divisor; rt_fdiv0 gives IEEE's answer (0/0: x86's NaN)"""
        if self.const_nonzero(r):
            return '(%s / %s)' % (self.paren(le), self.paren(re_))
        if is_pure(re_):
            r = self.paren(re_)
            return '(%s == 0.0 ? rt_fdiv0(%s, %s) : %s / %s)' % (r, le, r, self.paren(le), r)
        if not is_pure(le):
            # both operands may have side effects or calls: evaluate the left one first, as C does
            ta, tb = self.tmp('a'), self.tmp('d')
            return 'do { %s = %s; %s = %s; %s == 0.0 ? rt_fdiv0(%s, %s) : %s / %s }' % (ta, le, tb, re_, tb, ta, tb, ta, tb)
        t = self.tmp('d')
        return '((%s = %s) == 0.0 ? rt_fdiv0(%s, %s) : %s / %s)' % (t, re_, le, t, self.paren(le), t)

    @staticmethod
    def is_undef(code):
        return code.strip('() ') == 'undef' or is_null(code)

    def ptr_cmp(self, l, r, le, re_, op):
        nl = self.is_undef(le.code) or le.tag == 'n'
        nr = self.is_undef(re_.code) or re_.tag == 'n'
        if op in ('==', '!=') and (nl or nr):
            x = le.code if not nl else re_.code
            if self.mode_of_expr(l if not nl else r) == 'ref' and ptr_category((l if not nl else r).type) in ('scalar', 'ptrptr'):
                self.problem(l, 'aliased parameter compared with NULL: %s' % x)
            return '%sdefined(%s)' % ('!' if op == '==' else '', x)
        if ptr_category(l.type) == 'char' or ptr_category(r.type) == 'char':
            if op in ('==', '!='):
                return '%srt_peq(%s, %s)' % ('' if op == '==' else '!', le.code, re_.code)
            return '(%s->[1] %s %s->[1])' % (self.paren(le.code), op, self.paren(re_.code))
        if ptr_category(l.type) == 'func':
            return '(%s %s %s)' % (le.code, op, re_.code)
        if op in ('==', '!='):
            # references compare by address
            return '(%s %s %s)' % (le.code, op, re_.code)
        self.problem(l, 'ordering of non-char pointers')
        return '(%s %s %s)' % (le.code, op, re_.code)

    def arith(self, op, le, re_, tg, r, c, l=None):
        """C's le op re_ in type tg (l, r: the operand cursors, where known)"""
        intlike = tg in ('i', 'u', 'l', 'ul')
        if op == '/' and intlike:
            return 'int(%s / %s)' % (self.paren(le), self.paren(re_))
        if op == '%' and intlike:
            return 'rt_imod(%s, %s)' % (le, re_)
        if op == '/':
            return self.fdiv_code(le, re_, r)
        if op in ('+', '-', '*') and tg in ('d', 'f'):
            return self.zfix(op, le, re_, l, r)
        if op == '>>' and tg in ('i', 'l'):
            return 'do { use integer; %s >> %s }' % (self.paren(le), self.paren(re_))
        if op in ('|', '^', '&', '<<') and tg in ('i',):
            return 'rt_i32(%s %s %s)' % (self.paren(le), op, self.paren(re_))
        return '(%s %s %s)' % (le, op, re_)

    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            if ctag(l.type) == 'rec':
                self.check_rec_store(l)
                return self._assign_value(l, self.clone_of(r), 'rec')
            re_ = self.conv(self.val(r), r.type, l.type)
            return self._assign_value(l, re_.code, ctag(l.type))
        if op in ('&&', '||'):
            return Ex('(%s %s %s)' % (self.paren(self.cond(l)), op, self.paren(self.cond(r))), 'b')
        if op == ',':
            return Ex('do { %s; %s }' % ('; '.join(self.expr_stmts(l)), self.val(r).code), ctag(c.type))
        lt, rt = canon(l.type), canon(r.type)
        le, re_ = self.val(l), self.val(r)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            if le.tag in ('c', 'o', 'n') or re_.tag in ('c', 'o', 'n'):
                return Ex(self.ptr_cmp(l, r, le, re_, op), 'b')
            return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
        tg = ctag(c.type)
        if tg == 'c':
            if op == '+':
                if ptr_category(l.type) == 'char':
                    return Ex('cadd(%s, %s)' % (le.code, re_.code), 'c')
                return Ex('cadd(%s, %s)' % (re_.code, le.code), 'c')
            if op == '-':
                return Ex('cadd(%s, -%s)' % (le.code, self.paren(re_.code)), 'c')
            self.problem(c, 'char pointer operator %s' % op)
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            if ptr_category(l.type) != 'char':
                self.problem(c, 'difference of non-char pointers')
            return Ex('(%s->[1] - %s->[1])' % (self.paren(le.code), self.paren(re_.code)), 'l')
        if tg == 'o':
            self.problem(c, 'arithmetic on a non-char pointer')
        code = self.arith(op, le.code, re_.code, tg, r, c, l)
        if tg == 'u':
            code = '(%s & 0xFFFFFFFF)' % code
        elif tg == 'f':
            code = 'rt_f32(%s)' % self.bare(code)
        return Ex(code, tg)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        lv, rhs, tg, simple = self.compound_parts(c)
        if simple:
            return Ex('(%s)' % simple, tg)
        l = kids(c)[0]
        return Ex(self.store(l, rhs), tg)

    def compound_parts(self, c):
        """(lvalue, new value expression, tag, Perl compound form or None) for lhs op= rhs, with C's conversions"""
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        k = self.elem_kind(l)
        if k:
            p, i = self.elem_parts(l)
            lv = ('cg(%s, %s)' if k == 'char' else 'rt_pget(%s, %s)') % (p, i)
        else:
            lv = self.lvalue(l)
        re_ = self.val(r)
        if lt == 'c':
            if op == '+':
                return lv, 'cadd(%s, %s)' % (lv, re_.code), 'c', None
            if op == '-':
                return lv, 'cadd(%s, -%s)' % (lv, self.paren(re_.code)), 'c', None
            self.problem(c, 'char pointer %s=' % op)
        common = 'd' if 'd' in (lt, rt) else ('f' if 'f' in (lt, rt) else lt)
        rc = re_.code
        if not is_simple(lv) and not k:
            self.problem(c, 'compound assignment to an expression with side effects: %s' % lv)
        v = self.arith(op, lv, self.paren(rc), common, r, c, l if lt == common else None)
        simple = None
        if lt in ('i', 'l') and common in ('d', 'f'):
            v = self.d2i(v) if lt == 'i' else 'rt_d2l(%s)' % v
        elif lt == 'ul' and common in ('d', 'f'):
            v = 'rt_d2l(%s)' % v
        elif lt == 'u':
            v = ('(rt_d2l(%s) & 0xFFFFFFFF)' if common in ('d', 'f') else '(%s) & 0xFFFFFFFF') % v
        elif lt == 'f':
            v = 'rt_f32(%s)' % v
        elif lt == common and lt in ('i', 'l', 'ul') and op in ('+', '-', '*') and not k:
            simple = '%s %s= %s' % (lv, op, self.paren(rc))
        return lv, v, lt, simple

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        ea = self.conv(self.val(a), a.type, c.type)
        eb = self.conv(self.val(b), b.type, c.type)
        return Ex('(%s ? %s : %s)' % (self.paren(self.cond(cc)), self.paren(ea.code), self.paren(eb.code)), ctag(c.type))

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, idx = kids(c)
        k = self.elem_kind(c)
        if k == 'char':
            p, i = self.elem_parts(c)
            return Ex('cg(%s, %s)' % (p, i), ctag(c.type))
        if k == 'packed':
            p, i = self.elem_parts(c)
            return Ex('rt_pget(%s, %s)' % (p, i), ctag(c.type))
        b = self.ex(base)
        i = self.val(idx)
        return Ex('%s->[%s]' % (self.paren(b.code), i.code), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        b = self.ex(base)
        d = c.referenced
        rn = record_name(d.semantic_parent.type)
        return Ex('%s->[%s]' % (self.paren(b.code), self.field(rn, d.spelling)), ctag(c.type))

    def x_INIT_LIST_EXPR(self, c):
        return self.init_list(c, c.type)

    def clone_of(self, r):
        """the value of struct expression r, copied as C's struct assignment copies it"""
        t = canon(r.type)
        return 'clone_%s(%s)' % (self.rec(t), self.ex(r).code)

    # ================================================================== init lists
    def init_list(self, c, t):
        t = canon(t)
        items = kids(c)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            et = canon(t.element_type)
            n = t.element_count if t.kind == T.CONSTANTARRAY else len(items)
            if (et.kind == T.POINTER and front.is_char(et.get_pointee()) and items
                    and strip(items[-1]).kind == K.STRING_LITERAL and len(items) == n):
                # string table with no NULL sentinel: C's findmatch() reads past the end; EPA's build
                # finds a zero word there, so the table gets the NULL the C source forgot (as in C#)
                self.defects.append('%s:%d string table without NULL sentinel' % (os.path.basename(c.location.file.name), c.location.line))
                n += 1
            if ctag(t) == 'c' and et.kind != T.POINTER:
                vals = [self.val(it).code for it in items]
                return Ex('c_from_bytes([%s], %d)' % (', '.join(vals), n), 'c')
            vals = []
            for it in items:
                if strip(it).kind == K.INIT_LIST_EXPR:
                    vals.append(self.init_list(strip(it), et).code)
                elif ctag(et) == 'c' and strip(it).kind == K.STRING_LITERAL and canon(et).kind == T.CONSTANTARRAY:
                    vals.append('c_buf_from(%s, %d)' % (self.lit(self.string_bytes(strip(it))), canon(et).element_count))
                else:
                    vals.append(self.conv(self.val(it), it.type, et).code)
            while len(vals) < n:
                if ctag(et) == 'rec':
                    vals.append('new_%s()' % self.rec(et))
                elif et.kind == T.CONSTANTARRAY:
                    vals.append(self.new_array(et))
                else:
                    vals.append(self.zero(et))
            return Ex('[%s]' % ', '.join(vals), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            rn = self.rec(t)
            parts = []
            for f, it in zip(fields, items):
                if strip(it).kind == K.INIT_LIST_EXPR:
                    v = self.init_list(strip(it), f.type).code
                else:
                    v = self.conv(self.val(it), it.type, f.type).code
                parts.append('%s, %s' % (self.field(rn, f.spelling), v))
            return Ex('rt_rec_init(new_%s(), %s)' % (rn, ', '.join(parts)), 'rec')
        if len(items) == 1:
            return self.val(items[0])
        return Ex('undef', '?')

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
                    codes = [self.arg(x, q) if j != i else '$_[0]' for j, (x, q) in enumerate(zip(args, params))]
                    return Ex('rt_arr1(%s, sub { %s(%s) })' % (self.lvalue(kids(sa)[0]), n, ', '.join(codes)), ctag(c.type))
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    codes = [self.arg(x, q) if j != i else '$_[0]' for j, (x, q) in enumerate(zip(args, params))]
                    return Ex('rt_chr1(%s, sub { %s(%s) })' % (self.lvalue(kids(sa)[0]), n, ', '.join(codes)), ctag(c.type))
            return Ex('%s(%s)' % (n, ', '.join(self.arg(a, p) for a, p in zip(args, params))), ctag(c.type))
        fe = self.ex(callee)
        argcodes = []
        for a in args:
            sa = strip(a)
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and ctag(strip(kids(sa)[0]).type) in NUMTAGS:
                argcodes.append(self.lvalue(kids(sa)[0]))
            else:
                argcodes.append(self.val(a).code)
        return Ex('%s->(%s)' % (self.paren(fe.code), ', '.join(argcodes)), ctag(c.type))

    def arg(self, a, p):
        pmode = self.P.mode_of(p)
        cat = ptr_category(p.type)
        sa = strip(a)
        if (cat == 'scalar' and pmode == 'ref') or (cat == 'ptrptr' and pmode == 'ref'):
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                if self.elem_kind(kids(sa)[0]):
                    self.problem(a, 'address of a char or packed element passed by alias')
                return self.lvalue(kids(sa)[0])
            if self.mode_of_expr(sa) == 'ref':
                return self.ex(sa).code
            e = self.ex(sa)
            if self.is_undef(e.code):
                self.problem(a, 'NULL passed to aliased parameter %s' % p.spelling)
                return 'my $__null'
            self.problem(a, 'array passed to aliased parameter %s' % p.spelling)
            return '%s->[0]' % self.paren(e.code)
        if cat == 'scalar' and pmode == 'array':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = strip(kids(sa)[0])
                if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                    base, idx = kids(o)
                    i = self.val(idx).code
                    if i != '0':
                        self.problem(a, 'array offset &x[%s] passed to array parameter %s' % (i, p.spelling))
                    return self.ex(base).code
        e = self.conv(self.val(a), a.type, p.type)
        if e.tag == 'ref':
            self.problem(a, 'address passed where %s (%s) expected' % (p.spelling, pmode))
        return e.code

    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name in ('exp', 'sin', 'cos'):
            return Ex('%s(%s)' % (name, A(0)), 'd')
        if name in ('tan', 'asin', 'acos', 'atan', 'log10'):
            return Ex('POSIX::%s(%s)' % (name, A(0)), 'd')
        if name == 'fabs':
            return Ex('abs(%s)' % A(0), 'd')
        if name in ('log', 'sqrt'):
            x = A(0)
            if is_pure(x):
                x = self.paren(x)
                return Ex('(%s > 0.0 ? %s(%s) : rt_%s0(%s))' % (x, name, x, name, x), 'd')
            t = self.tmp('m')
            return Ex('((%s = %s) > 0.0 ? %s(%s) : rt_%s0(%s))' % (t, x, name, t, name, t), 'd')
        if name in ('floor', 'ceil'):
            x = A(0)
            if is_pure(x):
                x = self.paren(x)
                return Ex('(%s == %s ? POSIX::%s(%s) : %s + %s)' % (x, x, name, x, x, x), 'd')
            t = self.tmp('m')
            return Ex('((%s = %s) == %s ? POSIX::%s(%s) : %s + %s)' % (t, x, t, name, t, t, t), 'd')
        if name == 'pow':
            x, y = A(0), A(1)
            if nonintegral_literal(y):
                return Ex('(%s ** %s)' % (self.paren(x), y), 'd')
            # two integral operands take Perl's own exact integer power, whose result is glibc's only when it is a
            # nonzero double of at most 53 bits: otherwise rt_cpow recomputes it through glibc's pow
            ta = x if is_pure(x) else self.tmp('a')
            tb = y if is_pure(y) else self.tmp('b')
            ea = '(%s = %s)' % (ta, x) if ta != x else self.paren(ta)
            eb = '(%s = %s)' % (tb, y) if tb != y else self.paren(tb)
            t = self.tmp('p')
            return Ex('((((%s = %s ** %s) && abs(%s) <= 9007199254740992.0)) ? %s : rt_cpow(%s, %s))' % (t, ea, eb, t, t, ta, tb), 'd')
        if name in ('fprintf', 'snprintf', 'sscanf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}[name]
            head = [A(i) for i in range(fixed)]
            if name == 'sscanf':
                rest = [self.scanarg(a) for a in args[fixed:]]
            else:
                rest = [self.val(a).code for a in args[fixed:]]
            return Ex('c_%s(%s)' % (name, ', '.join(head + rest)), 'i')
        if name == 'free':
            return Ex('undef', 'v')
        if name in ('calloc', 'malloc', 'realloc'):
            return self.alloc(c, c.type)
        if name in ('fwrite', 'fread'):
            return self.freadwrite(c, name, args)
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return Ex('c_strtod(%s, %s)' % (A(0), self.lvalue(kids(ep)[0])), 'd')
            return Ex('c_strtod(%s)' % A(0), 'd')
        if name == 'time':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                return Ex('(%s = c_time())' % self.lvalue(kids(a0)[0]), 'l')
            return Ex('c_time()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('c_ctime(%s)' % (self.ex(kids(a0)[0]).code if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('(%s - %s)' % (A(0), A(1)), 'd')
        if name == 'fseeko':
            name = 'fseek'
        return Ex('c_%s(%s)' % (name, ', '.join(A(i) for i in range(len(args)))), tg)

    def scanarg(self, a):
        """an sscanf target: &number -> the lvalue itself (the runtime assigns it through @_); a char buffer as is"""
        sa = strip(a)
        if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
            o = strip(kids(sa)[0])
            if ctag(o.type) in NUMTAGS:
                if self.elem_kind(o):
                    self.problem(a, 'sscanf into a char or packed element')
                return self.lvalue(o)
            return self.ex(sa).code
        return self.val(a).code

    def alloc(self, call, t):
        args = list(call.get_arguments())
        t = canon(t)
        if t.kind != T.POINTER:
            return Ex('undef', 'o')
        et = canon(t.get_pointee())
        name = call.spelling
        if name == 'calloc':
            n = self.count_expr(args[0], args[1], et, mul=True)
        elif name == 'malloc':
            n = self.count_expr(args[0], None, et, mul=False)
        else:
            n = self.count_expr(args[1], None, et, mul=False)
            if ctag(t) == 'c':
                return Ex('rt_realloc_c(%s, %s)' % (self.val(args[0]).code, n), 'c')
            return Ex('rt_realloc(%s, %s, %s)' % (self.val(args[0]).code, n, self.fill_of(et)), 'o')
        if ctag(t) == 'c':
            return Ex('c_buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('new_%s()' % self.rec(et), 'o')
            return Ex('rt_recs(\\&new_%s, %s)' % (self.rec(et), n), 'o')
        if self.alloc_target_packed:
            return Ex('rt_pnew(%s)' % n, 'o')
        return Ex('rt_arr(%s, %s)' % (n, self.fill_of(et)), 'o')

    def fill_of(self, et):
        et = canon(et)
        if et.kind == T.RECORD:
            return '\\&new_%s' % self.rec(et)
        return self.zero(et)

    def count_expr(self, a, b, et, mul):
        size = self.sizeof_type(et)

        def is_sizeof(x):
            return strip(x).kind == K.CXX_UNARY_EXPR
        if mul:
            if is_sizeof(b):
                return self.val(a).code
            if is_sizeof(a):
                return self.val(b).code
            return 'int(%s * %s / %d)' % (self.val(a).code, self.val(b).code, size)
        sa = strip(a)
        if is_sizeof(sa):
            return '1'
        if sa.kind == K.BINARY_OPERATOR and binop(sa) == '*':
            l, r = kids(sa)
            if is_sizeof(l):
                return self.val(r).code
            if is_sizeof(r):
                return self.val(l).code
        return 'int(%s / %d)' % (self.paren(self.val(a).code), size)

    def code_of(self, et):
        return {T.DOUBLE: 'd', T.FLOAT: 'f', T.INT: 'i', T.LONG: 'q', T.CHAR_S: 'c', T.SCHAR: 'c', T.UINT: 'I', T.ENUM: 'i'}.get(canon(et).kind, '?')

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
                return Ex("c_%s_arr('%s', %d, %s, %s, %s, %s)" % (name, self.code_of(et), sz, self.ex(base).code, self.val(idx).code, self.val(cnt).code, fc), 'ul')
            return Ex("c_%s1('%s', %d, %s, %s)" % (name, self.code_of(et), sz, self.lvalue(o), fc), 'ul')
        if self.mode_of_expr(sb) == 'ref':
            et = canon(canon(sb.type).get_pointee())
            return Ex("c_%s1('%s', %d, %s, %s)" % (name, self.code_of(et), sz, self.ex(sb).code, fc), 'ul')
        bt = canon(sb.type)
        et = canon(bt.get_pointee()) if bt.kind == T.POINTER else canon(bt.element_type)
        return Ex("c_%s_arr('%s', %d, %s, 0, %s, %s)" % (name, self.code_of(et), sz, self.ex(sb).code, self.val(cnt).code, fc), 'ul')

    # ================================================================== statements
    def local_name(self, d):
        return self.locals.get(decl_key(d), d.spelling)

    def declare_local(self, d):
        n = d.spelling
        if n in PERL_SPECIAL_VARS or n in self.global_names:
            n = n + '_l'
        nn = n
        if nn in self.used_names:
            i = 2
            while '%s_%d' % (n, i) in self.used_names:
                i += 1
            nn = '%s_%d' % (n, i)
        self.used_names.add(nn)
        self.locals[decl_key(d)] = nn
        self.local_order.append(nn)
        return nn

    def bare(self, code):
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        return code

    def new_label(self, stem):
        self.label_count += 1
        return '%s%d' % (stem, self.label_count)

    def loop_ctx(self, kind, cond=None):
        """a C loop or switch on the context stack: [kind, label, label used, do-while condition]"""
        return [kind, self.new_label('L' if kind != 'switch' else 'SW'), False, cond]

    def labelled(self, ctx, head):
        """head with the loop's label in front if a jump used it (the marker is resolved in function())"""
        return '#LBL%s#%s' % (ctx[1], head)

    def stmt(self, c, ind):
        k = c.kind
        p = '    ' * ind
        if k == K.COMPOUND_STMT:
            out = []
            ch = kids(c)
            for i, x in enumerate(ch):
                if x.kind == K.DECL_STMT:
                    self.mark_assigned_first(x, ch[i + 1:])
                out += self.stmt(x, ind)
            return out
        if k == K.DECL_STMT:
            out = []
            for d in kids(c):
                out += self.local_decl(d, ind)
            return out
        if k == K.IF_STMT:
            ch = kids(c)
            out = [p + 'if (%s) {' % self.bare(self.cond(ch[0]))]
            out += self.stmt(ch[1], ind + 1)
            e = ch[2] if len(ch) > 2 else None
            while e is not None:
                if e.kind == K.IF_STMT:
                    ec = kids(e)
                    out.append(p + '} elsif (%s) {' % self.bare(self.cond(ec[0])))
                    out += self.stmt(ec[1], ind + 1)
                    e = ec[2] if len(ec) > 2 else None
                else:
                    out.append(p + '} else {')
                    out += self.stmt(e, ind + 1)
                    e = None
            out.append(p + '}')
            return out
        if k == K.WHILE_STMT:
            ch = kids(c)
            ctx = self.loop_ctx('loop')
            self.loops.append(ctx)
            head = 'while (%s) {' % self.bare(self.cond(ch[0]))
            body = self.stmt(ch[1], ind + 1)
            self.loops.pop()
            return [p + self.labelled(ctx, head)] + body + [p + '}']
        if k == K.DO_STMT:
            ch = kids(c)
            cnd = self.bare(self.cond(ch[1]))
            ctx = self.loop_ctx('do', cnd)
            self.loops.append(ctx)
            body = self.stmt(ch[0], ind + 1)
            self.loops.pop()
            return [p + self.labelled(ctx, 'while (1) {')] + body + [p + '    last unless (%s);' % cnd, p + '}']
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            ctx = self.loops[-1]
            if ctx[0] == 'switch-if':
                return []            # if/elsif switch: the section-final break is dropped
            if ctx[0] == 'switch':
                ctx[2] = True
                return [p + 'last %s;' % ctx[1]]
            return [p + 'last;']
        if k == K.CONTINUE_STMT:
            return self.continue_stmt(ind)
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'return;']
            if ctag(self.cur_ret) == 'rec':
                return [p + 'return %s;' % self.clone_of(ch[0])]
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            return [p + 'return %s;' % self.bare(e.code)]
        if k == K.NULL_STMT:
            return []
        if k in (K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'goto/label')
            return []
        return [p + x + ';' for x in self.expr_stmts(c)]

    def continue_stmt(self, ind):
        p = '    ' * ind
        crossed = False
        for ctx in reversed(self.loops):
            if ctx[0] == 'switch':
                crossed = True
                continue
            if ctx[0] == 'switch-if':
                continue
            if crossed:
                ctx[2] = True
            lbl = (' ' + ctx[1]) if crossed else ''
            if ctx[0] == 'do':
                if crossed:
                    ctx[2] = True
                return [p + 'last%s unless (%s);' % (lbl, ctx[3]), p + 'next%s;' % lbl]
            return [p + 'next%s;' % lbl]
        self.problem(None, 'continue outside a loop')
        return [p + 'next;']

    def expr_stmts(self, c):
        """an expression evaluated for its side effects, as one or more Perl statements (without ';')"""
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) == 'v':
            return self.expr_stmts(kids(s)[-1])
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            if ctag(l.type) == 'rec':
                self.check_rec_store(l)
                return [self.store_stmt(l, self.clone_of(r))]
            sl = strip(l)
            if self.packed_member(sl) is not None:
                # the packed field itself assigned: a new packed array, or NULL
                self.alloc_target_packed = True
                try:
                    v = self.conv(self.val(r), r.type, l.type).code
                finally:
                    self.alloc_target_packed = False
                return ['%s = %s' % (self.lvalue(l), v)]
            return [self.store_stmt(l, self.conv(self.val(r), r.type, l.type).code)]
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmts(l) + self.expr_stmts(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            lv, v, tg, simple = self.compound_parts(s)
            if simple:
                return [simple]
            return [self.store_stmt(kids(s)[0], v)]
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            d = '+' if '++' in unop(s) else '-'
            tg = ctag(a.type)
            k = self.elem_kind(a)
            if k:
                p, i = self.elem_parts(a)
                if k == 'packed':
                    return ['rt_pset(%s, %s, rt_pget(%s, %s) %s 1.0)' % (p, i, p, i, d)]
                return ['cs(%s, %s, cg(%s, %s) %s 1)' % (p, i, p, i, d)]
            lv = self.lvalue(a)
            if tg == 'f':
                return ['%s = rt_f32(%s %s 1.0)' % (lv, lv, d)]
            if tg == 'c':
                return ['%s = cadd(%s, %s1)' % (lv, lv, '' if d == '+' else '-')]
            if tg == 'u':
                return ['%s = (%s %s 1) & 0xFFFFFFFF' % (lv, lv, d)]
            return ['%s%s%s' % (lv, d, d)]
        e = self.ex(c)
        return [self.bare(e.code)]

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
        init_s = ''
        if init is not None:
            if init.kind == K.DECL_STMT:
                lines = []
                for d in kids(init):
                    lines += self.local_decl(d, 0)
                init_s = ', '.join(x.rstrip(';') for x in lines)
            else:
                init_s = ', '.join(self.expr_stmts(init))
        inc_s = ', '.join(self.expr_stmts(inc)) if inc is not None else ''
        cond_s = self.bare(self.cond(cond)) if cond is not None else ''
        ctx = self.loop_ctx('loop')
        self.loops.append(ctx)
        body_lines = self.stmt(body, ind + 1)
        self.loops.pop()
        return [p + self.labelled(ctx, 'for (%s; %s; %s) {' % (init_s, cond_s, inc_s))] + body_lines + [p + '}']

    def case_label(self, x):
        v = evaluate(strip(x))
        if v is not None and v[0] == 'int':
            return str(v[1]) if v[1] >= 0 else '(%d)' % v[1]
        return self.val(x).code

    def switch(self, c, ind):
        p = '    ' * ind
        ch = kids(c)
        e = self.val(ch[0])
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
                        labels.append(self.case_label(xc[0])); x = xc[1]
                    else:
                        labels.append(None); x = xc[0]
                if sections and not sections[-1][1]:
                    sections[-1][0].extend(labels)
                else:
                    sections.append([labels, []])
                sections[-1][1].append(x)
            elif sections:
                sections[-1][1].append(it)
        sv = e.code if e.tag not in ('b', 'L') else '(%s ? 1 : 0)' % e.code
        pre = []
        if not is_simple(sv):
            t = self.tmp('sw')
            pre = [p + '%s = %s;' % (t, self.bare(sv))]
            sv = t
        allvals = [l for sec in sections for l in sec[0] if l is not None]

        def test(labels):
            vals = [l for l in labels if l is not None]
            conds = ['%s == %s' % (sv, v) for v in vals]
            if None in labels:
                conds.append('(%s)' % ' && '.join('%s != %s' % (sv, v) for v in allvals) if allvals else '1')
            return ' || '.join(conds)

        simple = all(self.ends_clean(sec[1]) for sec in sections[:-1]) and all(not self.inner_break(sec[1]) for sec in sections)
        if simple and len(sections) >= 5 and all(l is None or re.fullmatch(r'\(?-?\d+\)?', l) for sec in sections for l in sec[0]):
            return pre + self.switch_tree(sections, sv, ind)
        if simple:
            out = list(pre)
            ordered = [s for s in sections if None not in s[0]] + [s for s in sections if None in s[0]]
            for si, (labels, stmts) in enumerate(ordered):
                if None in labels:
                    head = (p + '} else {') if si else (p + '{')
                else:
                    head = p + ('if (%s) {' if si == 0 else '} elsif (%s) {') % test(labels)
                self.loops.append(['switch-if', None, False, None])
                lines = []
                for s_ in stmts:
                    lines += self.stmt(s_, ind + 1)
                self.loops.pop()
                out += [head] + lines
            if ordered:
                out.append(p + '}')
            return out
        # general case: a labelled bare block (a loop that runs once), fall-through through a flag
        ft = self.tmp('ft')
        ctx = self.loop_ctx('switch')
        self.loops.append(ctx)
        out = list(pre) + [p + '%s = 0;' % ft]
        inner = []
        for si, (labels, stmts) in enumerate(sections):
            lines = []
            for s_ in stmts:
                lines += self.stmt(s_, ind + 2)
            inner.append(p + '    if (%s || %s) {' % (ft, test(labels)))
            inner += lines
            if not self.terminates(stmts):
                inner.append(p + '        %s = 1;' % ft)
            inner.append(p + '    }')
        self.loops.pop()
        ctx[2] = True
        out += [p + '%s: {' % ctx[1]] + inner + [p + '}']
        return out

    def switch_tree(self, sections, sv, ind):
        """a switch with many cases and no fall-through: the case value is mapped to its section's number through
        an array (or a hash) made once at load time, and the sections are chosen by a balanced tree of comparisons
        on that number, about log2(n) of them instead of up to n"""
        p = '    ' * ind
        vals = {}
        dflt = -1
        for si, (labels, stmts) in enumerate(sections):
            for l in labels:
                if l is None:
                    dflt = si
                else:
                    vals[int(l.strip('()'))] = si
        self.switch_maps.append(None)
        mname = 'SWMAP%d' % len(self.switch_maps)
        sn = self.tmp('s')
        if min(vals) >= 0 and max(vals) <= 1000:
            arr = ['undef'] * (max(vals) + 1)
            for v, si in vals.items():
                arr[v] = str(si)
            self.switch_maps[-1] = 'my @%s = (%s);' % (mname, ', '.join(arr))
            sw = sv if is_simple(sv) else sv
            out = [p + '%s = ((%s >= 0 && %s <= %d) ? $%s[%s] : undef) // %d;' % (sn, sw, sw, max(vals), mname, sw, dflt)]
        else:
            self.switch_maps[-1] = 'my %%%s = (%s);' % (mname, ', '.join('%d => %d' % kv for kv in sorted(vals.items())))
            out = [p + '%s = $%s{%s} // %d;' % (sn, mname, sv, dflt)]

        def body(si, ind2):
            self.loops.append(['switch-if', None, False, None])
            lines = []
            for s_ in sections[si][1]:
                lines += self.stmt(s_, ind2)
            self.loops.pop()
            return lines

        def tree(lo, hi, ind2):
            q = '    ' * ind2
            if hi - lo == 1:
                return body(lo, ind2)
            if hi - lo == 2:
                return [q + 'if (%s == %d) {' % (sn, lo)] + body(lo, ind2 + 1) + [q + '} else {'] + body(lo + 1, ind2 + 1) + [q + '}']
            mid = (lo + hi) // 2
            return [q + 'if (%s < %d) {' % (sn, mid)] + tree(lo, mid, ind2 + 1) + [q + '} else {'] + tree(mid, hi, ind2 + 1) + [q + '}']
        if dflt < 0:
            out += [p + 'if (%s >= 0) {' % sn] + tree(0, len(sections), ind + 1) + [p + '}']
        else:
            out += tree(0, len(sections), ind)
        return out

    @staticmethod
    def refers_to(c, key):
        if c.kind == K.DECL_REF_EXPR and decl_key(c.referenced) == key:
            return True
        return any(PerlEmitter.refers_to(x, key) for x in c.get_children())

    def mark_assigned_first(self, decl_stmt, rest):
        """the scalar locals of decl_stmt, without initializer, whose first use in the statements after it (in the same
        block) is a statement `x = e;` with no x in e: such a variable is always assigned before it is read, so the
        translation leaves out the zero that stands for C's indeterminate value (a statement at the block's own
        level runs before every later one; a jump that skips it skips all later uses in the block as well)"""
        for d in kids(decl_stmt):
            if d.kind != K.VAR_DECL or d.storage_class in (front.ci.StorageClass.EXTERN, front.ci.StorageClass.STATIC):
                continue
            if [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]:
                continue
            t = canon(d.type)
            if t.kind == T.CONSTANTARRAY or ctag(t) == 'rec':
                continue
            key = decl_key(d)
            for st in rest:
                if not self.refers_to(st, key):
                    continue
                if st.kind == K.BINARY_OPERATOR and binop(st) == '=':
                    lhs, rhs = kids(st)
                    if strip(lhs).kind == K.DECL_REF_EXPR and decl_key(strip(lhs).referenced) == key \
                            and not self.refers_to(rhs, key):
                        self.assigned_first.add(key)
                break

    def local_decl(self, d, ind):
        p = '    ' * ind
        if d.kind != K.VAR_DECL:
            return []
        if d.storage_class == front.ci.StorageClass.EXTERN:
            return []            # block-scope extern: refers to the global
        if d.storage_class == front.ci.StorageClass.STATIC:
            self.static_locals.append((d, self.cur_file))
            return []
        name = '$' + self.declare_local(d)
        init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        t = canon(d.type)
        if t.kind == T.CONSTANTARRAY:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return [p + '%s = %s;' % (name, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return [p + '%s = c_buf_from(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return [p + '%s = c_buf(%d);' % (name, t.element_count)]
            return [p + '%s = %s;' % (name, self.new_array(t))]
        if ctag(t) == 'rec':
            if init:
                return [p + '%s = %s;' % (name, self.clone_of(init[-1]))]
            return [p + '%s = new_%s();' % (name, self.rec(t))]
        if not init and decl_key(d) in self.assigned_first:
            return []
        v = self.conv(self.val(init[-1]), init[-1].type, d.type).code if init else self.zero(d.type)
        return [p + '%s = %s;' % (name, self.bare(v))]

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return 'rt_recs(\\&new_%s, %d)' % (self.rec(et), n)
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return 'rt_bufs(%d, %d)' % (n, et.element_count)
        if et.kind == T.CONSTANTARRAY:
            return 'rt_arr2(%d, %d, %s)' % (n, et.element_count, self.zero(et.element_type))
        return 'rt_arr(%d, %s)' % (n, self.zero(et))

    # ================================================================== functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.local_order = []
        self.temps = []
        self.loops = []
        self.tmp_count = 0
        self.label_count = 0
        self.cur_ret = c.result_type
        self.alloc_target_packed = False
        self.assigned_first = set()
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        pnames, aliases = [], []
        for i, prm in enumerate(params):
            nm = self.declare_local(prm)
            cat = ptr_category(prm.type)
            if cat in ('scalar', 'ptrptr') and self.P.mode_of(prm) == 'ref':
                pnames.append('undef')
                aliases.append('    \\my $%s = \\$_[%d];' % (nm, i))
            else:
                pnames.append('$' + nm)
        nparams = len(self.local_order)
        lines = self.stmt(body, 1)
        # resolve loop labels: keep those a last/next uses
        used = set(re.findall(r'\b(?:last|next) ((?:L|SW)\d+)\b', '\n'.join(lines)))
        out_lines = []
        for l in lines:
            m = re.match(r'(\s*)#LBL(\w+)#(.*)', l)
            if m:
                l = m.group(1) + ('%s: ' % m.group(2) if m.group(2) in used else '') + m.group(3)
            out_lines.append(l)
        out = ['# %s:%d' % (b, c.location.line), 'sub %s {' % self.fname[key]]
        while pnames and pnames[-1] == 'undef':
            pnames.pop()
        if pnames:
            out.append('    my (%s) = @_;' % ', '.join(pnames))
        out += aliases
        locs = ['$' + x for x in self.local_order[nparams:]] + self.temps
        for i in range(0, len(locs), 12):
            out.append('    my (%s);' % ', '.join(locs[i:i + 12]))
        if self.problems_in(out_lines):
            pass
        return out + out_lines + ['}']

    def problems_in(self, lines):
        return False

    def problem(self, c, msg):
        if c is None:
            self.problems.append('%s %s' % (self.cur_file, msg))
            return
        CSEmitter.problem(self, c, msg)

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = name
        consts = []
        init = []
        clone = []
        for i, f in enumerate(fields):
            t = canon(f.type)
            fc = self.field(nm, f.spelling)
            consts.append('    %s => %d,' % (fc, i))
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    init.append('c_buf(%d)' % t.element_count)
                    clone.append('    $c->[%s] = c_dup($s->[%s]);' % (fc, fc))
                else:
                    init.append(self.new_array(t))
                    if et.kind == T.RECORD:
                        clone.append('    $c->[%s] = [map { clone_%s($_) } @{$s->[%s]}];' % (fc, self.rec(et), fc))
                    elif ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
                        clone.append('    $c->[%s] = [map { c_dup($_) } @{$s->[%s]}];' % (fc, fc))
                    elif et.kind == T.CONSTANTARRAY:
                        clone.append('    $c->[%s] = [map { [@$_] } @{$s->[%s]}];' % (fc, fc))
                    else:
                        clone.append('    $c->[%s] = [@{$s->[%s]}];' % (fc, fc))
            elif t.kind == T.RECORD:
                init.append('new_%s()' % self.rec(t))
                clone.append('    $c->[%s] = clone_%s($s->[%s]);' % (fc, self.rec(t), fc))
            else:
                init.append(self.zero(f.type))
        self.rec_fields[nm] = consts
        out = ['sub new_%s { [%s] }' % (nm, ', '.join(init))]
        if clone:
            out += ['sub clone_%s {' % nm, '    my $s = $_[0];', '    my $c = [@$s];'] + clone + ['    $c;', '}']
        else:
            out.append('sub clone_%s { [@{$_[0]}] }' % nm)
        return out + ['']

    def global_init(self, name, c, t, init):
        t = canon(t)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return '$%s = %s;' % (name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return '$%s = c_buf_from(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return '$%s = c_buf(%d);' % (name, t.element_count)
            return '$%s = %s;' % (name, self.new_array(t))
        if t.kind == T.RECORD:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return '$%s = %s;' % (name, self.init_list(strip(init[-1]), t).code)
            return '$%s = new_%s();' % (name, self.rec(t))
        v = self.conv(self.val(init[-1]), init[-1].type, t).code if init else self.zero(t)
        return '$%s = %s;' % (name, self.bare(v))

    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        self.static_locals = []
        self.cur_file = None
        self.locals = {}
        self.used_names = set()
        self.local_order = []
        self.temps = []
        self.loops = []
        self.alloc_target_packed = False
        self.switch_maps = []
        recs = []
        for name, c in self.F.records.items():
            recs += self.record(name, c)
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
        names = []
        self.temps = []
        for k, c in self.F.globals.items():
            if self.F.global_owner[k] in SKIP_FILES:
                continue
            self.cur_file = self.F.global_owner[k]
            self.locals = {}
            init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
            glob.append(self.global_init(self.gname[k], c, c.type, init))
            names.append(self.gname[k])
        for d, b in self.static_locals:
            self.cur_file = b
            self.locals = {}
            init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
            nm = self.static_local_name(d)
            glob.append(self.global_init(nm, d, d.type, init))
            names.append(nm)
        if self.temps:
            self.problems.append('temporaries in global initialisers: %s' % self.temps)
        out = ['# Generated from EPA SWMM 5.2.4 by tools/c2x/emit_perl.py. Do not edit by hand;',
               '# fix the translator or swmm5/crt.pl instead.',
               'package SWMM5;',
               'use strict;',
               "use warnings FATAL => 'all';",
               "no warnings 'recursion';",
               "use feature 'refaliasing';",
               "no warnings 'experimental::refaliasing';",
               'use POSIX ();', '',
               '# record field indices (a C struct is an array reference, one slot per field)',
               'use constant {']
        for nm, consts in self.rec_fields.items():
            out += consts
        out += ['};', '']
        out.append('# C globals and function statics (initialised by init_globals)')
        for i in range(0, len(names), 10):
            out.append('our (%s);' % ', '.join('$' + n for n in names[i:i + 10]))
        out += ['', '# string literals: one shared buffer each, as C keeps one copy of each literal']
        for bts, name in self.lits.items():
            out.append('my %s = c_lit(%s);' % (name, perl_bytes(bts)))
        out += ['', '# case value -> section number, for switch statements with many cases (see switch_tree)']
        out += self.switch_maps
        out.append('')
        out += recs
        out += funcs
        out += ['# C globals and function statics, with their initial values', 'sub init_globals {']
        out += ['    ' + g for g in glob]
        out += ['}', '', '1;', '']
        open(os.path.join(outdir, 'engine.pl'), 'w').write('\n'.join(out) + '\n')
        with open(os.path.join(outdir, 'literals.txt'), 'w') as f:
            for s, bits in sorted(self.literals.items()):
                f.write('%s\t%016x\n' % (s, bits))
        return self.problems


class Wrap:
    """a cursor stand-in for deref(): makes elem_parts see *p as a unary '*' expression"""
    def __init__(self, a):
        self.a = a


def _elem_parts_wrap(self, a, _orig=PerlEmitter.elem_parts):
    if isinstance(a, Wrap):
        p = a.a
        sp = strip(p)
        if sp.kind == K.BINARY_OPERATOR and binop(sp) in ('+', '-') and ptr_category(kids(sp)[0].type) == 'char':
            l, r = kids(sp)
            i = self.val(r).code
            return self.ex(l).code, (i if binop(sp) == '+' else '-' + self.paren(i))
        return self.ex(p).code, '0'
    return _orig(self, a)


PerlEmitter.elem_parts = _elem_parts_wrap


if __name__ == '__main__':
    F = front.Front()
    em = PerlEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_perl')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
