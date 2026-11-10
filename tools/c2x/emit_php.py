"""
emit_php.py - EPA SWMM 5.2.4 C  ->  PHP 8.3 (one file, php/swmm5/engine.php, namespace SWMM5)

Reuses the C# and Python emitters' analysis (pointer modes, names, literals) and writes PHP. PHP looks like C and
is not C; these are the places where that matters (each is handled here or in php/swmm5/crt.php):

  arrays        PHP arrays are values: assignment and argument passing copy them. Every C array (malloc'd or a
                fixed array, of numbers, records or pointers) is an object, Arr, whose public property `a` holds
                a PHP array: `$Node->a[$j]->newDepth`. Copying the handle shares the array, as copying a C pointer
                does. A struct's own (embedded) arrays and structs are copied by __clone, as C's struct assignment
                copies them.
  char*         CPtr: a byte buffer object (Buf) plus an offset, with ArrayAccess for p[i]; strings are values in
                PHP too, so the buffer is an object that every pointer into it shares
  T* params     a scalar pointer that is only dereferenced (PtrInfo mode 'ref') is a PHP by-reference
                parameter (&$x), as the C# port uses `ref`: *x is $x, and &local, &obj.field, &arr[i] pass the
                lvalue itself. The analysis finds no stored scalar pointers and no NULL passed to them (C#: 0 problems)
  integers      `/` on two ints gives a float in PHP           -> \\intdiv(a, b) (truncates, as C)
                PHP's `%` is C's remainder; unsigned results are masked to 32 bits; there is no unsigned 64-bit
                type, and EPA never needs one (its unsigned longs are sizes and a hash sum far below 2**63)
  int -> double PHP keeps an int an int (and 6 / 2 is int 3): every C conversion clang records is written out
                                                               -> (float)$x, literals as 1.0
  double -> int (int)$x is C's truncation in range only        -> rt_d2i / rt_d2l (x86: INT_MIN outside the range)
  division      `/` throws DivisionByZeroError for a zero divisor, even for floats
                                                               -> ($b == 0.0 ? \\fdiv($a, $b) : $a / $b)
  negation      PHP compiles -$x as $x * -1, which leaves a NaN's sign alone; C flips it  -> rt_neg($x)
  float         PHP has no single precision                     -> rt_f32() rounds as C's (float) does
  globals       `global $Name;` at the top of each function that uses one; locals that share a global's name are
                renamed. Function statics are globals named function_variable.
  constants     enum values and macros are written as literals (a PHP constant costs a lookup per use)
  names         one namespace, SWMM5; functions are case-insensitive in PHP (checked: no two clash) and keywords
                such as `match` cannot name a function (suffixed with '_'); PHP's own functions are called fully
                qualified (\\exp)
  switch, for   PHP has C's switch (with fall-through), for, do-while, break; a `continue` inside a switch must
                say `continue 2` (in PHP a switch counts as a loop)
  comma         no comma operator in PHP expressions          -> split into statements, or rt_comma(a, b)
  function ptrs a string naming the function ('SWMM5\\\\name'), called as ($f)(...)
"""
import os, re, sys, collections, struct
from fractions import Fraction
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import CSEmitter, Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null
from emit_py import PyEmitter

# words PHP reserves: a function cannot be called this (PHP 8.3)
PHP_KEYWORDS = set('''abstract and array as break callable case catch class clone const continue declare default die do echo
else elseif empty enddeclare endfor endforeach endif endswitch endwhile eval exit extends final finally fn for foreach
function global goto if implements include include_once instanceof insteadof interface isset list match namespace new or
print private protected public readonly require require_once return static switch throw trait try unset use var while xor
yield int float bool string true false null void iterable object mixed never enum parent self __halt_compiler'''.split())
# variable names PHP gives a meaning of its own
PHP_SPECIAL_VARS = {'this', 'GLOBALS', '_GET', '_POST', '_COOKIE', '_FILES', '_ENV', '_REQUEST', '_SERVER', '_SESSION',
                    'http_response_header', 'argc', 'argv'}
# classes the runtime (php/swmm5/crt.php) defines in namespace SWMM5
RT_CLASSES = {'Arr', 'Buf', 'CPtr', 'CFile'}

SIMPLE_VAR = re.compile(r'\$\w+')


def php_bytes(b):
    """bytes as a PHP double-quoted string literal ($ and \\ escaped, everything else outside ASCII as \\xHH)"""
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
            out.append('\\x%02x' % ch)
    return '"' + ''.join(out) + '"'


def is_simple(code):
    """a variable, possibly followed by ->name and [index] parts: safe to read twice and needs no parentheses"""
    if not code.startswith('$'):
        return bool(re.fullmatch(r'\d+(\.\d*)?([eE][-+]?\d+)?', code))
    m = re.match(r'\$\w+', code)
    i = m.end()
    n = len(code)
    while i < n:
        if code.startswith('->', i):
            m = re.match(r'\w+', code[i + 2:])
            if not m:
                return False
            i += 2 + m.end()
        elif code[i] == '[':
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
            if not is_simple(inner):
                return False
            i = j + 1
        else:
            return False
    return True


def float_lit(x):
    """a double as a PHP literal that PHP's (correctly rounded) parser reads back to the same double"""
    if x != x:
        return '\\NAN'
    if x in (float('inf'), float('-inf')):
        return '\\INF' if x > 0 else '(-\\INF)'
    s = repr(x)
    if 'e' not in s and '.' not in s:
        s += '.0'
    if s.startswith('-'):
        return '(' + s + ')'
    return s


def round_f32(s):
    """the C float nearest the decimal literal s (one rounding, as the C compiler does), as a Python float"""
    q = Fraction(s)
    if q == 0:
        return 0.0
    neg = q < 0
    q = abs(q)
    # find e with 2**e <= q < 2**(e+1)
    e = q.numerator.bit_length() - q.denominator.bit_length()
    if Fraction(2) ** e > q:
        e -= 1
    if e < -126:
        e = -126
    ulp = Fraction(2) ** (e - 23)
    m = q / ulp
    n = m.numerator // m.denominator
    r = m - n
    if r > Fraction(1, 2) or (r == Fraction(1, 2) and n % 2 == 1):
        n += 1
    v = float(n * ulp)
    if v > 3.4028234663852886e38:
        v = float('inf')
    return -v if neg else v


class PhpEmitter(PyEmitter):
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
            if base.lower() in PHP_KEYWORDS or base.startswith(('c_', 'rt_')):
                base += '_'
            self.fname[(b, n)] = base
        # PHP function names are case-insensitive: no two may differ only in case
        low = collections.Counter(v.lower() for v in self.fname.values())
        clash = [v for v in self.fname.values() if low[v.lower()] > 1]
        if clash:
            raise SystemExit('function names that differ only in case: %s' % sorted(set(clash)))
        self.gname = {}
        for k, c in F.globals.items():
            b = F.global_owner[k]
            n = c.spelling
            base = b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n
            if base in PHP_SPECIAL_VARS:
                base += '_'
            self.gname[k] = base
        self.global_names = set(self.gname.values())
        self.clash_names = set()
        self.blocks = [(0, False)]
        self.block_count = 0
        self.guse = {}
        self.tmp_count = 0
        self.static_names = {}
        self.cur_globals = set()

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
        self.use_global(nm)
        return '$' + nm

    def use_global(self, nm):
        """note a use of global nm at the current block path (see place_globals)"""
        self.cur_globals.add(nm)
        self.guse.setdefault(nm, []).append(tuple(self.blocks))

    def static_local_name(self, d):
        nm = '%s_%s' % (self.fname.get((self.cur_file, d.semantic_parent.spelling), d.semantic_parent.spelling).rstrip('_'), d.spelling)
        self.global_names.add(nm)
        return nm

    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = 'L%d' % len(self.lits)
        return self.lits[b]

    def rec(self, t):
        n = record_name(t)
        if n in RT_CLASSES or n.lower() in PHP_KEYWORDS:
            n += '_'
        return n

    def tmp(self, stem='t'):
        self.tmp_count += 1
        return '$__%s%d' % (stem, self.tmp_count)

    def paren(self, s):
        if is_simple(s) or (s.startswith('(') and s.endswith(')') and self._balanced(s[1:-1])):
            return s
        return '(' + s + ')'

    def to_f(self, code):
        if re.fullmatch(r'-?\d+', code):
            v = code + '.0'
            return '(%s)' % v if v.startswith('-') else v
        return '(float)' + self.paren(code)

    # ================================================================== conversions
    def to_ctype(self, e, t):
        want = ctag(t)
        if e.tag in ('b', 'L') and want in NUMTAGS:
            if want in ('d', 'f'):
                return Ex('(%s ? 1.0 : 0.0)' % e.code, want)
            return Ex('(%s ? 1 : 0)' % e.code, want)
        return e

    def as_bool(self, e):
        if e.tag in ('b', 'L'):
            return e.code
        if e.tag in ('i', 'u', 'l', 'ul'):
            return '(%s != 0)' % e.code
        if e.tag in ('d', 'f'):
            return '(%s != 0.0)' % e.code
        return '(%s !== null)' % e.code

    def conv(self, e, src_t, dst_t):
        s, d = ctag(src_t), ctag(dst_t)
        if e.tag in ('b', 'L') and d in NUMTAGS:
            e = Ex('(%s ? 1 : 0)' % e.code, 'i'); s = 'i'
        if s == d or d in ('v', '?', 'rec'):
            return Ex(e.code, d if d not in ('?',) else e.tag)
        if d == 'i':
            if s in ('d', 'f'):
                return Ex('rt_d2i(%s)' % e.code, 'i')
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
            if s in ('i', 'u', 'l', 'ul'):
                return Ex('rt_f32(%s)' % self.to_f(e.code), 'f')
            return Ex('rt_f32(%s)' % e.code, 'f')
        if d in ('c', 'o'):
            if is_null(e.code) or e.code == 'null' or e.tag == 'n':
                return Ex('null', d)
            return Ex(e.code, d)
        return e

    def zero(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0', 'l': '0', 'ul': '0', 'd': '0.0', 'f': '0.0'}.get(tg, 'null')

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

    def x_FLOATING_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?[fFlL]?', toks[0]):
            s = toks[0].rstrip('fFlL')
            if tg == 'f':
                return Ex(float_lit(round_f32(s)), tg)
            return Ex(float_lit(float(s)), tg)
        v = evaluate(c)
        if v is None:
            self.problem(c, 'floating literal %s' % toks)
        x = v[1] if v else 0.0
        if tg == 'f':
            x = struct.unpack('<f', struct.pack('<f', x))[0]
        return Ex(float_lit(x), tg)

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
            return Ex("'SWMM5\\\\%s'" % n, 'o')
        if d.kind == K.PARM_DECL or (d.kind == K.VAR_DECL and d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL and d.storage_class != front.ci.StorageClass.STATIC):
            return Ex('$' + self.local_name(d), ctag(d.type))
        if d.kind == K.VAR_DECL:
            if d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL:
                nm = self.static_local_name(d)
                self.use_global(nm)
                return Ex('$' + nm, ctag(d.type))
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
        if (e.tag == 'i' and e.code == '0' and canon(c.type).kind == T.POINTER) or is_null(e.code) or e.code == 'null':
            return Ex('null', ctag(c.type))
        if ctag(c.type) == 'o' and ctag(inner.type) == 'o':
            return e
        return self.conv(self.to_ctype(e, inner.type), inner.type, c.type)

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
        tg = ctag(c.type)
        if op == '-':
            if tg in ('d', 'f'):
                if re.fullmatch(r'\d+(\.\d*)?([eE][-+]?\d+)?', e.code):
                    return Ex('(-%s)' % e.code, tg)
                return Ex('rt_neg(%s)' % e.code, tg)
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
            if tg == 'u':
                code = '(%s & 0xFFFFFFFF)' % code
            return Ex(code, e.tag)
        self.problem(c, 'unary ' + op)
        return e

    @staticmethod
    def is_char_elem(a):
        """a char reached through a char pointer: an ArrayAccess element of a CPtr, which PHP cannot ++ in place"""
        sa = strip(a)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            return ptr_category(kids(sa)[0].type) == 'char'
        return sa.kind == K.UNARY_OPERATOR and unop(sa) == '*' and ptr_category(kids(sa)[0].type) == 'char'

    def incdec_expr(self, a, op):
        """++/-- used as a value"""
        d = '+' if '++' in op else '-'
        tg = ctag(a.type)
        lv = self.lvalue(a)
        if self.is_char_elem(a):
            if op.startswith('pre'):
                return Ex('(%s = %s %s 1)' % (lv, lv, d), tg)
            return Ex('rt_first(%s, %s = %s %s 1)' % (lv, lv, lv, d), tg)
        if tg == 'c':
            if op.startswith('pre'):
                return Ex('(%s = %s->add(%s1))' % (lv, lv, '' if d == '+' else '-'), 'c')
            if not is_simple(lv):
                self.problem(a, 'post-increment of a pointer expression with side effects: %s' % lv)
            return Ex('rt_first(%s, %s = %s->add(%s1))' % (lv, lv, lv, '' if d == '+' else '-'), 'c')
        if tg in ('i', 'l', 'ul'):
            return Ex('(%s%s%s)' % (lv, d, d) if op.startswith('post') else '(%s%s%s)' % (d, d, lv), tg)
        if op.startswith('pre'):
            if tg == 'f':
                return Ex('(%s = rt_f32(%s %s 1.0))' % (lv, lv, d), tg)
            if tg == 'u':
                return Ex('(%s = (%s %s 1) & 0xFFFFFFFF)' % (lv, lv, d), tg)
            return Ex('(%s %s= 1.0)' % (lv, d), tg)
        if not is_simple(lv):
            self.problem(a, 'post-increment of an expression with side effects: %s' % lv)
        if tg == 'd':
            return Ex('(%s%s%s)' % (lv, d, d), tg)
        nv = '%s %s %s' % (lv, d, '1.0' if tg == 'f' else '1')
        nv = 'rt_f32(%s)' % nv if tg == 'f' else '(%s) & 0xFFFFFFFF' % nv
        return Ex('rt_first(%s, %s = %s)' % (lv, lv, nv), tg)

    def check_rec_store(self, l):
        """*p = struct through a pointer variable would only rebind the PHP variable, not copy into the caller's
        struct: flag it (EPA has none)"""
        sl = strip(l)
        if sl.kind == K.UNARY_OPERATOR and unop(sl) == '*':
            self.problem(l, 'struct assigned through a pointer')
        if sl.kind == K.DECL_REF_EXPR and sl.referenced is not None and sl.referenced.kind == K.PARM_DECL:
            self.problem(l, 'struct parameter assigned')

    def _assign_value(self, l, rhs, tg):
        return Ex('(%s = %s)' % (self.lvalue(l), rhs), tg)

    def deref(self, a):
        e = self.ex(a)
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-') and ptr_category(kids(sa)[0].type) == 'char':
                l, r = kids(sa)
                i = self.val(r).code
                return Ex('%s[%s]' % (self.paren(self.ex(l).code), i if binop(sa) == '+' else '-' + self.paren(i)), 'i')
            return Ex('%s[0]' % self.paren(e.code), 'i')
        if cat == 'record':
            return Ex(e.code, 'rec')
        mode = self.mode_of_expr(sa)
        pt = ctag(canon(a.type).get_pointee())
        if mode == 'ref':
            return Ex(e.code, pt)
        if sa.kind == K.BINARY_OPERATOR:
            l, r = kids(sa)
            return Ex('%s->a[%s]' % (self.paren(self.ex(l).code), self.val(r).code), pt)
        return Ex('%s->a[0]' % self.paren(e.code), pt)

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
                return Ex(b if i == '0' else '%s->add(%s)' % (self.paren(b), i), 'c')
            if ctag(sa.type) == 'rec':
                return Ex(self.ex(sa).code, 'o')
            i = self.val(idx).code
            if i == '0':
                return Ex(self.ex(base).code, 'o')
        # &scalar: legal only where a by-reference parameter takes it (arg(), vararg())
        return Ex(self.lvalue(sa), 'ref')

    def fdiv_code(self, le, re_, r):
        """C double division: PHP's `/` throws for a zero divisor; \\fdiv gives IEEE's answer (0/0: x86's default NaN)"""
        if self.const_nonzero(r):
            return '(%s / %s)' % (self.paren(le), self.paren(re_))
        if is_simple(re_):
            return '(%s == 0.0 ? \\fdiv(%s, %s) : %s / %s)' % (re_, le, re_, self.paren(le), re_)
        if not is_simple(le):
            # both operands may have side effects or calls: keep C's left-to-right order through a call
            return '\\fdiv(%s, %s)' % (le, re_)
        t = self.tmp('d')
        return '((%s = %s) == 0.0 ? \\fdiv(%s, %s) : %s / %s)' % (t, re_, le, t, self.paren(le), t)

    def ptr_cmp(self, l, r, le, re_, op):
        nl = le.code == 'null' or is_null(le.code) or le.tag == 'n'
        nr = re_.code == 'null' or is_null(re_.code) or re_.tag == 'n'
        if op in ('==', '!=') and (nl or nr):
            x = le.code if not nl else re_.code
            if self.mode_of_expr(l if not nl else r) == 'ref' and ptr_category((l if not nl else r).type) in ('scalar', 'ptrptr'):
                self.problem(l, 'by-reference parameter compared with NULL: %s' % x)
            return '(%s %s null)' % (x, '===' if op == '==' else '!==')
        if ptr_category(l.type) == 'char' or ptr_category(r.type) == 'char':
            if op in ('==', '!='):
                return '%srt_peq(%s, %s)' % ('' if op == '==' else '!', le.code, re_.code)
            return '(%s->o %s %s->o)' % (self.paren(le.code), op, self.paren(re_.code))
        if op in ('==', '!='):
            return '(%s %s %s)' % (le.code, '===' if op == '==' else '!==', re_.code)
        self.problem(l, 'ordering of non-char pointers')
        return '(%s %s %s)' % (le.code, op, re_.code)

    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            if ctag(l.type) == 'rec':
                self.check_rec_store(l)
                return self._assign_value(l, 'clone %s' % self.paren(self.ex(r).code), 'rec')
            re_ = self.conv(self.val(r), r.type, l.type)
            return self._assign_value(l, re_.code, ctag(l.type))
        if op in ('&&', '||'):
            return Ex('(%s %s %s)' % (self.paren(self.cond(l)), op, self.paren(self.cond(r))), 'b')
        if op == ',':
            return Ex('rt_comma(%s, %s)' % (self.ex(l).code, self.val(r).code), ctag(c.type))
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
                    return Ex('%s->add(%s)' % (self.paren(le.code), re_.code), 'c')
                return Ex('%s->add(%s)' % (self.paren(re_.code), le.code), 'c')
            if op == '-':
                return Ex('%s->add(-%s)' % (self.paren(le.code), self.paren(re_.code)), 'c')
            self.problem(c, 'char pointer operator %s' % op)
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            if ptr_category(l.type) != 'char':
                self.problem(c, 'difference of non-char pointers')
            return Ex('(%s->o - %s->o)' % (self.paren(le.code), self.paren(re_.code)), 'l')
        if tg == 'o':
            self.problem(c, 'arithmetic on a non-char pointer')
        intlike = tg in ('i', 'u', 'l', 'ul')
        if op == '/' and intlike:
            code = '\\intdiv(%s, %s)' % (le.code, re_.code)
        elif op == '%' and intlike:
            code = '(%s %% %s)' % (self.paren(le.code), self.paren(re_.code))
        elif op == '/':
            code = self.fdiv_code(le.code, re_.code, r)
        else:
            code = '(%s %s %s)' % (le.code, op, re_.code)
        if tg == 'u':
            code = '(%s & 0xFFFFFFFF)' % code
        elif tg == 'f':
            code = 'rt_f32%s' % code if code.startswith('(') and self._balanced(code[1:-1]) else 'rt_f32(%s)' % code
        return Ex(code, tg)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        lv, rhs, tg, simple = self.compound_parts(c)
        if simple:
            return Ex('(%s)' % simple, tg)
        return Ex('(%s = %s)' % (lv, rhs), tg)

    def compound_parts(self, c):
        """(lvalue, new value expression, tag, PHP compound form or None) for lhs op= rhs, with C's conversions"""
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        lv = self.lvalue(l)
        re_ = self.val(r)
        if lt == 'c':
            if op == '+':
                return lv, '%s->add(%s)' % (lv, re_.code), 'c', None
            if op == '-':
                return lv, '%s->add(-%s)' % (lv, self.paren(re_.code)), 'c', None
            self.problem(c, 'char pointer %s=' % op)
        common = 'd' if 'd' in (lt, rt) else ('f' if 'f' in (lt, rt) else lt)
        intlike = common in ('i', 'u', 'l', 'ul')
        rc = re_.code
        lvv = lv
        if common in ('d', 'f') and lt in ('i', 'u', 'l', 'ul'):
            lvv = self.to_f(lv)
        if common in ('d', 'f') and rt in ('i', 'u', 'l', 'ul'):
            rc = self.to_f(rc)
        if op == '/' and intlike:
            v = '\\intdiv(%s, %s)' % (lvv, rc)
        elif op == '%' and intlike:
            v = '%s %% %s' % (self.paren(lvv), self.paren(rc))
        elif op == '/':
            v = self.fdiv_code(lvv, rc, r)
        else:
            v = '%s %s %s' % (lvv, op, self.paren(rc))
        simple = None
        if lt in ('i', 'l') and common in ('d', 'f'):
            v = ('rt_d2i(%s)' if lt == 'i' else 'rt_d2l(%s)') % v
        elif lt == 'ul' and common in ('d', 'f'):
            v = 'rt_d2l(%s)' % v
        elif lt == 'u':
            v = ('(rt_d2l(%s) & 0xFFFFFFFF)' if common in ('d', 'f') else '(%s) & 0xFFFFFFFF') % v
        elif lt == 'f':
            v = 'rt_f32(%s)' % v
        elif lt == common and op in ('+', '-', '*', '|', '&', '^', '<<', '>>'):
            simple = '%s %s= %s' % (lv, op, self.paren(rc))
        return lv, v, lt, simple

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        ea = self.conv(self.val(a), a.type, c.type)
        eb = self.conv(self.val(b), b.type, c.type)
        return Ex('(%s ? %s : %s)' % (self.paren(self.cond(cc)), self.paren(ea.code), self.paren(eb.code)), ctag(c.type))

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, idx = kids(c)
        b = self.ex(base)
        i = self.val(idx)
        if ptr_category(base.type) == 'char':
            return Ex('%s[%s]' % (self.paren(b.code), i.code), ctag(c.type))
        return Ex('%s->a[%s]' % (self.paren(b.code), i.code), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        b = self.ex(base)
        return Ex('%s->%s' % (self.paren(b.code), c.referenced.spelling), ctag(c.type))

    def x_INIT_LIST_EXPR(self, c):
        return self.init_list(c, c.type)

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
                # char x[] = {'a', 'b', ...}
                vals = [self.val(it).code for it in items]
                return Ex('CPtr::from_bytes([%s], %d)' % (', '.join(vals), n), 'c')
            vals = []
            for it in items:
                if strip(it).kind == K.INIT_LIST_EXPR:
                    vals.append(self.init_list(strip(it), et).code)
                elif ctag(et) == 'c' and strip(it).kind == K.STRING_LITERAL and canon(et).kind == T.CONSTANTARRAY:
                    vals.append('CPtr::buf_from(%s, %d)' % (self.lit(self.string_bytes(strip(it))), canon(et).element_count))
                else:
                    vals.append(self.conv(self.val(it), it.type, et).code)
            while len(vals) < n:
                if ctag(et) == 'rec':
                    vals.append('new %s()' % self.rec(et))
                elif et.kind == T.CONSTANTARRAY:
                    vals.append(self.new_array(et))
                else:
                    vals.append(self.zero(et))
            return Ex('new Arr([%s])' % ', '.join(vals), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                if strip(it).kind == K.INIT_LIST_EXPR:
                    v = self.init_list(strip(it), f.type).code
                else:
                    v = self.conv(self.val(it), it.type, f.type).code
                parts.append("'%s', %s" % (f.spelling, v))
            return Ex('rt_rec_init(new %s(), %s)' % (self.rec(t), ', '.join(parts)), 'rec')
        if len(items) == 1:
            return self.val(items[0])
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
                    codes = [self.arg(x, q) if j != i else '$__a' for j, (x, q) in enumerate(zip(args, params))]
                    return Ex('rt_arr1(%s, fn($__a) => %s(%s))' % (self.lvalue(kids(sa)[0]), n, ', '.join(codes)), ctag(c.type))
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    codes = [self.arg(x, q) if j != i else '$__c' for j, (x, q) in enumerate(zip(args, params))]
                    return Ex('rt_chr1(%s, fn($__c) => %s(%s))' % (self.lvalue(kids(sa)[0]), n, ', '.join(codes)), ctag(c.type))
            return Ex('%s(%s)' % (n, ', '.join(self.arg(a, p) for a, p in zip(args, params))), ctag(c.type))
        fe = self.ex(callee)
        argcodes = []
        for a in args:
            sa = strip(a)
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and ctag(strip(kids(sa)[0]).type) in NUMTAGS:
                argcodes.append(self.lvalue(kids(sa)[0]))
            else:
                argcodes.append(self.val(a).code)
        return Ex('(%s)(%s)' % (fe.code, ', '.join(argcodes)), ctag(c.type))

    def arg(self, a, p):
        pmode = self.P.mode_of(p)
        cat = ptr_category(p.type)
        sa = strip(a)
        if (cat == 'scalar' and pmode == 'ref') or (cat == 'ptrptr' and pmode == 'ref'):
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return self.lvalue(kids(sa)[0])
            if self.mode_of_expr(sa) == 'ref':
                return self.ex(sa).code
            e = self.ex(sa)
            if is_null(e.code) or e.code == 'null':
                self.problem(a, 'NULL passed to by-reference parameter %s' % p.spelling)
                return '$__null'
            # an array (or &arr[0]) passed to a pointer the callee only dereferences: its element 0
            self.problem(a, 'array passed to by-reference parameter %s' % p.spelling)
            return '%s->a[0]' % self.paren(e.code)
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

    # math.h: PHP's math functions call glibc (php/test/run_libm_tests.sh); pow is PHP's ** on two floats. PHP's
    # floor and ceil return a signaling NaN unchanged where glibc's quiet it: rt_floor and rt_ceil do that first
    MATH_PHP = {'exp': '\\exp', 'sin': '\\sin', 'cos': '\\cos', 'tan': '\\tan', 'atan': '\\atan', 'asin': '\\asin',
                'acos': '\\acos', 'log': '\\log', 'log10': '\\log10', 'sqrt': '\\sqrt', 'floor': 'rt_floor',
                'ceil': 'rt_ceil', 'fabs': '\\abs'}

    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name in self.MATH_PHP:
            return Ex('%s(%s)' % (self.MATH_PHP[name], A(0)), 'd')
        if name == 'pow':
            return Ex('(%s ** %s)' % (self.paren(A(0)), self.paren(A(1))), 'd')
        if name in ('fprintf', 'snprintf', 'sscanf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}[name]
            head = [A(i) for i in range(fixed)]
            if name == 'sscanf':
                return Ex('c_sscanf(%s, [%s])' % (', '.join(head), ', '.join(self.scanarg(a) for a in args[fixed:])), 'i')
            rest = [self.val(a).code for a in args[fixed:]]
            return Ex('c_%s(%s)' % (name, ', '.join(head + rest)), 'i')
        if name == 'free':
            return Ex('null', 'v')
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
            return Ex('(float)(%s - %s)' % (A(0), A(1)), 'd')
        if name == 'fseeko':
            name = 'fseek'
        return Ex('c_%s(%s)' % (name, ', '.join(A(i) for i in range(len(args)))), tg)

    def scanarg(self, a):
        """an sscanf target: &number -> a PHP reference (&$x); a char buffer or a number pointer passed through"""
        sa = strip(a)
        if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
            o = strip(kids(sa)[0])
            if ctag(o.type) in NUMTAGS:
                return '&' + self.lvalue(o)
            return self.ex(sa).code
        if ptr_category(sa.type) == 'scalar' and self.mode_of_expr(sa) == 'ref':
            return '&' + self.ex(sa).code
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
            if ctag(t) == 'c':
                return Ex('rt_realloc_c(%s, %s)' % (self.val(args[0]).code, n), 'c')
            return Ex('rt_realloc(%s, %s, %s)' % (self.val(args[0]).code, n, self.fill_of(et)), 'o')
        if ctag(t) == 'c':
            return Ex('CPtr::buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('new %s()' % self.rec(et), 'o')
            return Ex('rt_recs(%s::class, %s)' % (self.rec(et), n), 'o')
        return Ex('rt_arr(%s, %s)' % (n, self.fill_of(et)), 'o')

    def fill_of(self, et):
        et = canon(et)
        if et.kind == T.RECORD:
            return "'%s'" % self.rec(et)
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
            return '\\intdiv(%s * %s, %d)' % (self.val(a).code, self.val(b).code, size)
        sa = strip(a)
        if is_sizeof(sa):
            return '1'
        if sa.kind == K.BINARY_OPERATOR and binop(sa) == '*':
            l, r = kids(sa)
            if is_sizeof(l):
                return self.val(r).code
            if is_sizeof(r):
                return self.val(l).code
        return '\\intdiv(%s, %d)' % (self.val(a).code, size)

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
        if n in PHP_SPECIAL_VARS or n in self.clash_names:
            n = n + '_l'
        nn = n
        if nn in self.used_names:
            i = 2
            while '%s_%d' % (n, i) in self.used_names:
                i += 1
            nn = '%s_%d' % (n, i)
        self.used_names.add(nn)
        self.locals[decl_key(d)] = nn
        return nn

    def stmt(self, c, ind):
        k = c.kind
        p = '    ' * ind
        if k == K.COMPOUND_STMT:
            out = []
            for ch in kids(c):
                out += self.stmt(ch, ind)
            return out
        if k == K.DECL_STMT:
            out = []
            for d in kids(c):
                out += self.local_decl(d, ind)
            return out
        if k == K.IF_STMT:
            ch = kids(c)
            out = [p + 'if (%s) {' % self.bare(self.cond(ch[0]))]
            out += self.block(ch[1], ind + 1)
            e = ch[2] if len(ch) > 2 else None
            while e is not None:
                if e.kind == K.IF_STMT:
                    ec = kids(e)
                    # an elseif condition is evaluated in the enclosing block
                    out.append(p + '} elseif (%s) {' % self.bare(self.cond(ec[0])))
                    out += self.block(ec[1], ind + 1)
                    e = ec[2] if len(ec) > 2 else None
                else:
                    out.append(p + '} else {')
                    out += self.block(e, ind + 1)
                    e = None
            out.append(p + '}')
            return out
        if k == K.WHILE_STMT:
            ch = kids(c)
            self.loops.append('loop')
            out = [p + 'while (%s) {' % self.bare(self.cond(ch[0]))] + self.block(ch[1], ind + 1, loop=True) + [p + '}']
            self.loops.pop()
            return out
        if k == K.DO_STMT:
            ch = kids(c)
            self.loops.append('loop')
            body = self.block(ch[0], ind + 1, loop=True)
            self.loops.pop()
            return [p + 'do {'] + body + [p + '} while (%s);' % self.bare(self.cond(ch[1]))]
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            return [p + 'break;']
        if k == K.CONTINUE_STMT:
            n = 1
            for x in reversed(self.loops):
                if x == 'loop':
                    break
                n += 1
            return [p + ('continue;' if n == 1 else 'continue %d;' % n)]
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'return;']
            if ctag(self.cur_ret) == 'rec':
                return [p + 'return clone %s;' % self.paren(self.ex(ch[0]).code)]
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            return [p + 'return %s;' % self.bare(e.code)]
        if k == K.NULL_STMT:
            return []
        if k in (K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'goto/label')
            return []
        return [p + x + ';' for x in self.expr_stmts(c)]

    def block(self, c, ind, loop=False, items=None):
        """the lines of a statement list (c, or the cursors in items) as a block that may receive `global`
        bindings: a marker line first, replaced or dropped by place_globals"""
        self.block_count += 1
        bid = self.block_count
        self.blocks.append((bid, loop))
        out = ['    ' * ind + '#G%d' % bid]
        if items is None:
            out += self.stmt(c, ind)
        else:
            for it in items:
                out += self.stmt(it, ind)
        self.blocks.pop()
        return out

    def place_globals(self, lines):
        """bind each global in the innermost block that holds all its uses, but never inside a loop (a binding
        costs a hash lookup each time it runs): a function that uses a table in one case of a switch binds it
        there, not on every call"""
        at = collections.defaultdict(list)
        for nm, paths in self.guse.items():
            common = list(paths[0])
            for pth in paths[1:]:
                k = 0
                while k < len(common) and k < len(pth) and common[k] == pth[k]:
                    k += 1
                del common[k:]
            target = common[0][0]
            for bid, loop in common:
                if loop:
                    break
                target = bid
            at[target].append(nm)
        out = []
        for l in lines:
            st = l.lstrip(' ')
            if st.startswith('#G') and st[2:].isdigit():
                names = at.get(int(st[2:]))
                if names:
                    pre = l[:len(l) - len(st)]
                    out.append(pre + 'global %s;' % ', '.join('$' + g for g in sorted(names)))
                continue
            out.append(l)
        return out

    def bare(self, code):
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        return code

    def expr_stmts(self, c):
        """an expression evaluated for its side effects, as one or more PHP statements (without ';')"""
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) == 'v':
            return self.expr_stmts(kids(s)[-1])
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            lv = self.lvalue(l)
            if ctag(l.type) == 'rec':
                self.check_rec_store(l)
                return ['%s = clone %s' % (lv, self.paren(self.ex(r).code))]
            return ['%s = %s' % (lv, self.bare(self.conv(self.val(r), r.type, l.type).code))]
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmts(l) + self.expr_stmts(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            lv, v, tg, simple = self.compound_parts(s)
            if simple:
                return [simple]
            return ['%s = %s' % (lv, self.bare(v))]
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            lv = self.lvalue(a)
            d = '+' if '++' in unop(s) else '-'
            tg = ctag(a.type)
            if self.is_char_elem(a):
                return ['%s = %s %s 1' % (lv, lv, d)]
            if tg == 'f':
                return ['%s = rt_f32(%s %s 1.0)' % (lv, lv, d)]
            if tg == 'd':
                return ['%s %s= 1.0' % (lv, d)]
            if tg == 'c':
                return ['%s = %s->add(%s1)' % (lv, lv, '' if d == '+' else '-')]
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
        self.loops.append('loop')
        body_lines = self.block(body, ind + 1, loop=True)
        self.loops.pop()
        return [p + 'for (%s; %s; %s) {' % (init_s, cond_s, inc_s)] + body_lines + [p + '}']

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
        out = [p + 'switch (%s) {' % self.bare(e.code if e.tag not in ('b', 'L') else '(%s ? 1 : 0)' % e.code)]
        self.loops.append('switch')

        def emit_item(it, depth):
            lines = []
            x = it
            while x.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                xc = kids(x)
                if x.kind == K.CASE_STMT:
                    lines.append(p + '    case %s:' % self.case_label(xc[0])); x = xc[1]
                else:
                    lines.append(p + '    default:'); x = xc[0]
            return lines, x
        sections = []          # [label lines, statement cursors]
        for it in items:
            if it.kind in (K.CASE_STMT, K.DEFAULT_STMT):
                lab, x = emit_item(it, 0)
                if sections and not sections[-1][1]:
                    sections[-1][0].extend(lab)
                else:
                    sections.append([lab, []])
                sections[-1][1].append(x)
            elif sections:
                sections[-1][1].append(it)
        for lab, stmts in sections:
            # a binding after the labels runs whether control jumps to them or falls through from above
            out += lab
            out += self.block(None, ind + 2, items=stmts)
        self.loops.pop()
        out.append(p + '}')
        return out

    def local_decl(self, d, ind):
        p = '    ' * ind
        if d.kind != K.VAR_DECL:
            return []
        if d.storage_class == front.ci.StorageClass.EXTERN:
            return []            # block-scope extern: refers to the global
        if d.storage_class == front.ci.StorageClass.STATIC:
            self.static_locals.append((d, self.cur_file, self.fname.get((self.cur_file, d.semantic_parent.spelling))))
            return []
        name = '$' + self.declare_local(d)
        init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        t = canon(d.type)
        if t.kind == T.CONSTANTARRAY:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return [p + '%s = %s;' % (name, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return [p + '%s = CPtr::buf_from(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return [p + '%s = CPtr::buf(%d);' % (name, t.element_count)]
            return [p + '%s = %s;' % (name, self.new_array(t))]
        if ctag(t) == 'rec':
            if init:
                return [p + '%s = clone %s;' % (name, self.paren(self.ex(init[-1]).code))]
            return [p + '%s = new %s();' % (name, self.rec(t))]
        v = self.conv(self.val(init[-1]), init[-1].type, d.type).code if init else self.zero(d.type)
        return [p + '%s = %s;' % (name, self.bare(v))]

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return 'rt_recs(%s::class, %d)' % (self.rec(et), n)
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return 'rt_bufs(%d, %d)' % (n, et.element_count)
        if et.kind == T.CONSTANTARRAY:
            return 'rt_arr2(%d, %d, %s)' % (n, et.element_count, self.zero(et.element_type))
        return 'rt_arr(%d, %s)' % (n, self.zero(et))

    # ================================================================== functions
    def function(self, key, c):
        # a local named like a global the same function uses would be bound to the global by `global $x;`:
        # emit once, and if any local shares a name with a used global, emit again with those locals renamed
        self.clash_names = set()
        np, ns = len(self.problems), len(self.static_locals)
        out = self.function1(key, c)
        clash = {n for n in self.used_names if n in self.cur_globals}
        if clash:
            del self.problems[np:]
            del self.static_locals[ns:]
            self.clash_names = clash
            out = self.function1(key, c)
        return out

    def function1(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.loops = []
        self.tmp_count = 0
        self.cur_globals = set()
        self.cur_ret = c.result_type
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        ps = []
        for prm in params:
            nm = self.declare_local(prm)
            cat = ptr_category(prm.type)
            byref = cat in ('scalar', 'ptrptr') and self.P.mode_of(prm) == 'ref'
            ps.append(('&$' if byref else '$') + nm)
        self.blocks = []
        self.block_count = 0
        self.guse = {}
        lines = self.place_globals(self.block(body, 1))
        out = ['// %s:%d' % (b, c.location.line), 'function %s(%s)' % (self.fname[key], ', '.join(ps)), '{']
        return out + lines + ['}']

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = self.rec(c.type)
        out = ['final class %s' % nm, '{']
        ctor, clone = [], []
        for f in fields:
            t = canon(f.type)
            fn = f.spelling
            if t.kind == T.CONSTANTARRAY:
                out.append('    public $%s;' % fn)
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    ctor.append('        $this->%s = CPtr::buf(%d);' % (fn, t.element_count))
                    clone.append('        $this->%s = $this->%s->dup();' % (fn, fn))
                else:
                    ctor.append('        $this->%s = %s;' % (fn, self.new_array(t)))
                    if et.kind == T.RECORD or (et.kind == T.CONSTANTARRAY):
                        clone.append('        $this->%s = rt_deep($this->%s);' % (fn, fn))
                    else:
                        clone.append('        $this->%s = clone $this->%s;' % (fn, fn))
            elif t.kind == T.RECORD:
                out.append('    public $%s;' % fn)
                ctor.append('        $this->%s = new %s();' % (fn, self.rec(t)))
                clone.append('        $this->%s = clone $this->%s;' % (fn, fn))
            else:
                out.append('    public $%s = %s;' % (fn, self.zero(f.type)))
        if ctor:
            out += ['', '    public function __construct()', '    {'] + ctor + ['    }']
        if clone:
            out += ['', '    public function __clone()', '    {'] + clone + ['    }']
        return out + ['}', '']

    def global_init(self, name, c, t, init):
        t = canon(t)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return '$%s = %s;' % (name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return '$%s = CPtr::buf_from(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return '$%s = CPtr::buf(%d);' % (name, t.element_count)
            return '$%s = %s;' % (name, self.new_array(t))
        if t.kind == T.RECORD:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return '$%s = %s;' % (name, self.init_list(strip(init[-1]), t).code)
            return '$%s = new %s();' % (name, self.rec(t))
        v = self.conv(self.val(init[-1]), init[-1].type, t).code if init else self.zero(t)
        return '$%s = %s;' % (name, self.bare(v))

    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        self.static_locals = []
        self.cur_file = None
        self.locals = {}
        self.used_names = set()
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
        for k, c in self.F.globals.items():
            if self.F.global_owner[k] in SKIP_FILES:
                continue
            self.cur_file = self.F.global_owner[k]
            self.locals = {}
            init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
            glob.append(self.global_init(self.gname[k], c, c.type, init))
            names.append(self.gname[k])
        for d, b, fn in self.static_locals:
            self.cur_file = b
            self.locals = {}
            init = [x for x in kids(d) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
            nm = self.static_local_name(d)
            glob.append(self.global_init(nm, d, d.type, init))
            names.append(nm)
        out = ['<?php',
               '// Generated from EPA SWMM 5.2.4 by tools/c2x/emit_php.py. Do not edit by hand;',
               '// fix the translator or swmm5/crt.php instead.',
               'namespace SWMM5;', '',
               '// string literals: one shared buffer each, as C keeps one copy of each literal']
        for bts, name in self.lits.items():
            out.append('const %s = new CPtr(new Buf(%s), 0);' % (name, php_bytes(bts + b'\0')))
        out.append('')
        for name, c in self.F.records.items():
            out += self.record(name, c)
        out += funcs
        out += ['// C globals and function statics, with their initial values',
                'function init_globals()', '{']
        for i in range(0, len(names), 8):
            out.append('    global %s;' % ', '.join('$' + n for n in names[i:i + 8]))
        out += ['    ' + g for g in glob]
        out += ['}', '']
        open(os.path.join(outdir, 'engine.php'), 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = PhpEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_php')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
