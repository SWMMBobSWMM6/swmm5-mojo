"""
emit_ruby.py - EPA SWMM 5.2.4 C  ->  Ruby (one module, ruby/swmm5/engine.rb)

Reuses the C# and Python emitters' analysis (pointer modes, which locals live in boxes, names, literals) and writes
its own syntax. Ruby is not Python, and these are the places where that matters:

  integers      Ruby's `/` and `%` floor; C truncates            -> idiv(a, b), a.remainder(b)
  int -> double Ruby never converts an Integer to a Float by itself, and `1 / 2` is 0 in Ruby: every C
                conversion clang records is written out           -> (x).to_f, literals as 1.0
  truth         0 and 0.0 are true in Ruby                         -> (x != 0), (x != 0.0); a C comparison used as
                a number becomes (c ? 1 : 0)
  0.0 / 0.0     MRI's Float#/ returns nan("") (sign bit clear); x86 gives the default NaN (sign bit set, printed
                "-nan")                                            -> (b == 0.0 ? fdiv0(a, b) : a / b)
  libm          Math.sqrt/log/log10/asin/acos raise Math::DomainError where C returns NaN, Math.sqrt(-0.0) is
                +0.0, Float#** returns a Complex for a negative base, Float#floor returns an Integer
                                                                   -> c_sqrt, c_log, c_log10, c_asin, c_acos,
                                                                      c_pow / x ** y, c_floor (crt.rb)
  names         locals must start with a lower-case letter; constants (enums, macros, records) with an upper-case
                one; keywords and Object/Kernel/Module methods are suffixed with '_'; C globals are $globals
  switch        `case` with integer literals when no case falls through; otherwise a one-pass `while true` loop
  statements    if/elsif/else/end, while ... end, do-while as `while true ... break unless c end`; assignments
                are expressions in Ruby, so C's `if ((f = fopen(...)) == NULL)` keeps its shape
"""
import os, re, sys, collections, struct
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import CSEmitter, Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null
from emit_py import PyEmitter

RB_KEYWORDS = set('''alias and begin BEGIN break case class def defined do else elsif end END ensure false for if in module
next nil not or redo rescue retry return self super then true undef unless until when while yield __FILE__ __LINE__
__ENCODING__ __method__'''.split())
# instance and private methods of Module, Kernel, Object and BasicObject (ruby 3.3.6) that a generated name could shadow
RB_METHODS = set('''__callee__ __dir__ __id__ __method__ __send__ abort alias_method ancestors append_features at_exit attr
attr_accessor attr_reader attr_writer autoload binding caller caller_locations catch class class_eval class_exec
class_variable_get class_variable_set class_variables clone const_added const_get const_missing const_set
const_source_location constants define_method define_singleton_method deprecate_constant display dup enum_for eval
exec exit extend extend_object extended fail fork format freeze gem gem_original_require gets global_variables hash
include included included_modules initialize initialize_clone initialize_copy initialize_dup inspect instance_eval
instance_exec instance_method instance_methods instance_variable_get instance_variable_set instance_variables itself
lambda load local_variables loop method method_added method_missing method_removed method_undefined methods
module_eval module_exec module_function name object_id open p pp prepend prepend_features prepended print printf
private private_class_method private_constant private_instance_methods private_methods proc protected
protected_instance_methods protected_methods public public_class_method public_constant public_instance_method
public_instance_methods public_method public_methods public_send putc puts raise rand readline readlines refine
refinements remove_class_variable remove_const remove_instance_variable remove_method require require_relative
ruby2_keywords select send set_temporary_name set_trace_func singleton_class singleton_method singleton_method_added
singleton_method_removed singleton_method_undefined singleton_methods sleep spawn sprintf srand syscall system tap
test then throw to_enum to_s trace_var trap undef_method undefined_instance_methods untrace_var using warn
yield_self copy'''.split())
# names the runtime (ruby/swmm5/crt.rb) defines in module CRT, which the engine module includes
RT_NAMES = set('''lit cstr bytes_of str_of d2i d2l f32 i32 i64 idiv fdiv fdiv0 post postp arr1 chr1 fieldref
cptr_diff realloc_ rec_init'''.split())
SPECIAL_GVARS = {'stdout', 'stdin', 'stderr', 'DEBUG', 'VERBOSE', 'FILENAME', 'LOAD_PATH', 'LOADED_FEATURES',
                 'PROGRAM_NAME', 'SAFE', 'KCODE', 'FIELD_SEPARATOR', 'FS'}
# Ruby constants a generated constant must not hide inside module SWMM5
RB_CONSTS = {'Math', 'Float', 'Integer', 'Array', 'String', 'File', 'IO', 'Time', 'Data', 'Struct', 'Kernel',
             'Object', 'Module', 'Class', 'Comparable', 'Process', 'Signal', 'Random', 'Range', 'Set', 'Method', 'Proc',
             'Thread', 'Dir', 'GC', 'ENV', 'ARGV', 'STDOUT', 'STDERR', 'STDIN', 'CRT', 'SWMM5', 'CPtr', 'Box',
             'FieldRef', 'ElemRef', 'CFile', 'Hash', 'Symbol', 'NilClass', 'Numeric', 'Rational', 'Complex'}


def rb_meth(n):
    """a C function name as a Ruby method name"""
    if n in RB_KEYWORDS or n in RB_METHODS or n in RT_NAMES or n.startswith('c_'):
        return n + '_'
    return n


def rb_local(n):
    """a C local or parameter as a Ruby local variable (must begin with a lower-case letter or '_')"""
    if n[0].isupper():
        return '_' + n
    if n in RB_KEYWORDS:
        return n + '_'
    return n


def rb_field(n):
    if n in RB_KEYWORDS or n in RB_METHODS:
        return n + '_'
    return n


def rb_const(n):
    """an enum constant or macro as a Ruby constant"""
    if not n[0].isupper():
        return 'K_' + n
    if n in RB_CONSTS:
        return n + '_'
    return n


def rb_class(n):
    if not n[0].isupper():
        return 'T_' + n
    if n in RB_CONSTS:
        return n + '_'
    return n


def rb_gvar(n):
    return '$' + (n + '_' if n in SPECIAL_GVARS else n)


def rb_bytes(b):
    """bytes as a Ruby double-quoted string literal (no interpolation: '#' is escaped)"""
    out = []
    for ch in b:
        if ch == 0x5c:
            out.append('\\\\')
        elif ch == 0x22:
            out.append('\\"')
        elif ch == 0x23:
            out.append('\\#')
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


SIMPLE = re.compile(r'[\w$@.\[\]]+')          # an expression with no call, no operator: safe to evaluate twice


def is_pure(code):
    return bool(SIMPLE.fullmatch(code)) and '..' not in code


class RbEmitter(PyEmitter):
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
            self.fname[(b, n)] = rb_meth(base)
        self.gname = {}
        for k, c in F.globals.items():
            b = F.global_owner[k]
            n = c.spelling
            base = b[:-2] + '_' + n if (cnt[n] > 1 and front.is_static(c)) else n
            self.gname[k] = rb_gvar(base)
        self.boxed_globals = set()
        self._find_boxed_globals()
        self.tmp_count = 0
        self.cur_hoist = False
        self.hoisted = []                    # (constant name) of boxes allocated once at load time
        self.reentrant = self.find_reentrant()

    # ================================================================== boxes
    def find_reentrant(self):
        """functions that can be active twice at once (on a cycle of the call graph; a call through a function
        pointer may reach any function whose address is taken). The others keep their boxed locals (C locals
        whose address is taken) in boxes allocated once, not one Box.new per call."""
        F = self.F
        addr = set()
        for n in self.P.func_values:
            addr.update(F.func_by_decl.get(n, []))
        edges = {k: set() for k in F.funcs}

        def walk(x, k):
            if x.kind == K.CALL_EXPR:
                d = x.referenced
                if d is not None and d.kind == K.FUNCTION_DECL:
                    keys = F.func_by_decl.get(d.spelling) or []
                    cand = [q for q in keys if q[0] == k[0]] or [q for q in keys if F.funcs[q].storage_class != front.ci.StorageClass.STATIC]
                    if cand:
                        edges[k].add(cand[0])
                else:
                    edges[k].update(addr)
            for y in x.get_children():
                walk(y, k)
        for k, c in F.funcs.items():
            walk(c, k)
        # Tarjan's strongly connected components, iteratively
        index, low, on, stack, res, n = {}, {}, set(), [], set(), [0]
        for root in edges:
            if root in index:
                continue
            work = [(root, iter(sorted(edges[root])))]
            index[root] = low[root] = n[0]; n[0] += 1; stack.append(root); on.add(root)
            while work:
                v, it = work[-1]
                w = next(it, None)
                if w is not None:
                    if w not in index:
                        index[w] = low[w] = n[0]; n[0] += 1; stack.append(w); on.add(w)
                        work.append((w, iter(sorted(edges[w]))))
                    elif w in on:
                        low[v] = min(low[v], index[w])
                    continue
                work.pop()
                if work:
                    low[work[-1][0]] = min(low[work[-1][0]], low[v])
                if low[v] == index[v]:
                    comp = []
                    while True:
                        w = stack.pop(); on.discard(w); comp.append(w)
                        if w == v:
                            break
                    if len(comp) > 1 or v in edges[v]:
                        res.update(comp)
        return res

    def hoisted_box(self, local):
        name = 'BX_%s_%s' % (self.cur_fname.rstrip('_'), local)
        if name not in self.hoisted:
            self.hoisted.append(name)
        return name

    # ================================================================== naming
    def global_ref(self, d):
        k = decl_key(d)
        if k in self.gname:
            return self.gname[k]
        for gk, c in self.F.globals.items():
            if c.spelling == d.spelling and not front.is_static(c):
                return self.gname[gk]
        if d.spelling in ('stdout', 'stderr'):
            return 'C_' + d.spelling.upper()
        return rb_gvar(d.spelling)

    def macro_name(self, n):
        for b, m in self.F.macros.items():
            if n in m and m[n][0] in ('int', 'float') and n in self.macro_global:
                return rb_const(n)
        return None

    def static_local_name(self, d):
        return '$%s_%s' % (d.semantic_parent.spelling, d.spelling)

    def rec(self, t):
        return rb_class(record_name(t))

    def tmp(self, stem='t'):
        self.tmp_count += 1
        return '__%s%d' % (stem, self.tmp_count)

    def paren(self, s):
        if re.fullmatch(r'[\w.\[\]$@]+', s) or (s.startswith('(') and s.endswith(')') and self._balanced(s[1:-1])):
            return s
        return '(' + s + ')'

    @staticmethod
    def to_f(code):
        if re.fullmatch(r'-?\d+', code):
            return code + '.0'
        if re.fullmatch(r'[\w.\[\]$@]+', code) or (code.startswith('(') and code.endswith(')') and CSEmitter._balanced(code[1:-1])):
            return code + '.to_f'
        return '(%s).to_f' % code

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
        return '!%s.nil?' % self.paren(e.code)

    def conv(self, e, src_t, dst_t):
        s, d = ctag(src_t), ctag(dst_t)
        if e.tag in ('b', 'L') and d in NUMTAGS:
            e = Ex('(%s ? 1 : 0)' % e.code, 'i'); s = 'i'
        if s == d or d in ('v', '?', 'rec'):
            return Ex(e.code, d if d not in ('?',) else e.tag)
        if d == 'i':
            if s in ('d', 'f'):
                return Ex('d2i(%s)' % e.code, 'i')
            if s in ('l', 'u', 'ul'):
                return Ex('i32(%s)' % e.code, 'i')
            return Ex(e.code, 'i')
        if d == 'l':
            if s in ('d', 'f'):
                return Ex('d2l(%s)' % e.code, 'l')
            if s == 'ul':
                return Ex('i64(%s)' % e.code, 'l')
            return Ex(e.code, 'l')
        if d == 'u':
            if s in ('d', 'f'):
                return Ex('(d2l(%s) & 0xFFFFFFFF)' % e.code, 'u')
            return Ex('(%s & 0xFFFFFFFF)' % self.paren(e.code), 'u')
        if d == 'ul':
            if s in ('d', 'f'):
                return Ex('(d2l(%s) & 0xFFFFFFFFFFFFFFFF)' % e.code, 'ul')
            return Ex('(%s & 0xFFFFFFFFFFFFFFFF)' % self.paren(e.code), 'ul')
        if d == 'd':
            if s in ('i', 'u', 'l', 'ul'):
                return Ex(self.to_f(e.code), 'd')
            return Ex(e.code, 'd')
        if d == 'f':
            if s in ('i', 'u', 'l', 'ul'):
                return Ex('f32(%s)' % self.to_f(e.code), 'f')
            return Ex('f32(%s)' % e.code, 'f')
        if d in ('c', 'o'):
            if is_null(e.code) or e.code in ('None', 'nil') or e.tag == 'n':
                return Ex('nil', d)
            return Ex(e.code, d)
        return e

    def zero(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0', 'l': '0', 'ul': '0', 'd': '0.0', 'f': '0.0'}.get(tg, 'nil')

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
        if len(toks) == 1 and self.macro_name(toks[0]):
            return Ex(self.macro_name(toks[0]), tg)
        v = evaluate(c)
        return Ex(str(v[1]) if v else '0', tg)

    @staticmethod
    def rb_float(s):
        s = s.rstrip('fFlL')
        if s.startswith('.'):
            s = '0' + s
        s = re.sub(r'\.([eE])', r'.0\1', s)
        if s.endswith('.'):
            s += '0'
        if '.' not in s and 'e' not in s.lower():
            s += '.0'
        return s

    def x_FLOATING_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?[fFlL]?', toks[0]):
            s = self.rb_float(toks[0])
            if tg == 'f':
                x = struct.unpack('<f', struct.pack('<f', float(s)))[0]
                return Ex(self.rb_float(repr(x)), tg)
            return Ex(s, tg)
        if len(toks) == 1 and self.macro_name(toks[0]) and tg != 'f':
            return Ex(self.macro_name(toks[0]), tg)
        v = evaluate(c)
        x = v[1] if v else 0.0
        if tg == 'f':
            x = struct.unpack('<f', struct.pack('<f', x))[0]
        return Ex(self.rb_float(repr(x)), tg)

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return Ex(rb_local(c.spelling), '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return Ex(str(d.enum_value), 'i')
            return Ex(rb_const(d.spelling), 'i')
        if d.kind == K.FUNCTION_DECL:
            n = self.func_ref(d, self.cur_file)
            if n is None:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex('method(:%s)' % rb_meth(d.spelling), 'o')
            return Ex('method(:%s)' % n, 'o')
        if d.kind == K.PARM_DECL or (d.kind == K.VAR_DECL and d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL and d.storage_class != front.ci.StorageClass.STATIC):
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
        return Ex(rb_local(c.spelling), ctag(c.type))

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                return Ex(self.zero(c.type), ctag(c.type))
            return self.ex(ch[0])
        e = self.ex(ch[0])
        if canon(c.type).kind == T.POINTER and e.tag == 'i' and e.code == '0':
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
        if (e.tag == 'i' and e.code == '0' and canon(c.type).kind == T.POINTER) or is_null(e.code) or e.code == 'nil':
            return Ex('nil', ctag(c.type))
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
            code = '-%s' % self.paren(e.code)
            if tg == 'u':
                code = '(%s & 0xFFFFFFFF)' % code
            elif tg == 'ul':
                code = '(%s & 0xFFFFFFFFFFFFFFFF)' % code
            return Ex(code, e.tag)
        if op == '+':
            return e
        if op == '~':
            code = '~%s' % self.paren(e.code)
            if tg == 'u':
                code = '(%s & 0xFFFFFFFF)' % code
            elif tg == 'ul':
                code = '(%s & 0xFFFFFFFFFFFFFFFF)' % code
            return Ex(code, e.tag)
        self.problem(c, 'unary ' + op)
        return e

    def incdec_expr(self, a, op):
        """++/-- used as a value"""
        d = '+' if '++' in op else '-'
        tg = ctag(a.type)
        lv = self.lvalue(a)
        one = '1.0' if tg in ('d', 'f') else '1'
        if op.startswith('pre'):
            if tg == 'f':
                return Ex('(%s = f32(%s %s 1.0))' % (lv, lv, d), tg)
            if tg in ('u', 'ul'):
                m = '0xFFFFFFFF' if tg == 'u' else '0xFFFFFFFFFFFFFFFF'
                return Ex('(%s = (%s %s 1) & %s)' % (lv, lv, d, m), tg)
            return Ex('(%s %s= %s)' % (lv, d, one), tg)
        if tg in ('i', 'l'):
            return Ex('((%s %s= 1) %s 1)' % (lv, d, '-' if d == '+' else '+'), tg)
        if not is_pure(lv):
            self.problem(a, 'post-increment of an expression with side effects: %s' % lv)
        t = self.tmp()
        nv = '%s %s %s' % (t, d, one)
        if tg == 'f':
            nv = 'f32(%s)' % nv
        elif tg == 'u':
            nv = '(%s) & 0xFFFFFFFF' % nv
        elif tg == 'ul':
            nv = '(%s) & 0xFFFFFFFFFFFFFFFF' % nv
        return Ex('(%s = %s; %s = %s; %s)' % (t, lv, lv, nv, t), tg)

    def _assign_value(self, l, rhs, tg):
        """assignment used as an expression value: Ruby assignments are expressions"""
        return Ex('(%s = %s)' % (self.lvalue(l), rhs), tg)

    def ref_of(self, a, inc=None):
        """a reference object (responds to v and v=) for lvalue a"""
        sa = strip(a)
        lv = self.lvalue(a)
        if lv.endswith('.v'):
            return lv[:-2]
        if sa.kind == K.MEMBER_REF_EXPR:
            obj, attr = lv.rsplit('.', 1)
            return 'fieldref(%s, :%s)' % (obj, attr)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sa)
            return 'ElemRef.new(%s, %s)' % (self.ex(base).code, self.val(idx).code)
        if sa.kind == K.DECL_REF_EXPR:
            d = sa.referenced
            if d.kind == K.VAR_DECL and (d.semantic_parent is None or d.semantic_parent.kind != K.FUNCTION_DECL
                                         or d.storage_class == front.ci.StorageClass.STATIC):
                return 'GlobalRef.new(:%s)' % lv
        self.problem(a, 'reference to unboxed local %s' % lv)
        return 'Box.new(%s)' % lv

    def deref(self, a):
        e = self.ex(a)
        cat = ptr_category(a.type)
        sa = strip(a)
        if cat == 'char':
            return Ex('%s[0]' % self.paren(e.code), 'i')
        if cat == 'record':
            return Ex(e.code, 'rec')
        mode = self.mode_of_expr(sa)
        if mode == 'ref':
            return Ex(self.paren(e.code) + '.v', ctag(canon(a.type).get_pointee()))
        if sa.kind == K.BINARY_OPERATOR:
            l, r = kids(sa)
            return Ex('%s[%s]' % (self.paren(self.ex(l).code), self.val(r).code), ctag(canon(a.type).get_pointee()))
        return Ex('%s[0]' % self.paren(e.code), ctag(canon(a.type).get_pointee()))

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
                return Ex(b if i == '0' else '(%s + %s)' % (self.paren(b), i), 'c')
            if ctag(sa.type) == 'rec':
                return Ex(self.ex(sa).code, 'o')
            i = self.val(idx).code
            if i == '0':
                return Ex(self.ex(base).code, 'o')
        return Ex(self.ref_of(sa), 'ref')

    def fdiv_code(self, le, re_, r):
        """C double division: x86 gives the default NaN (sign set) for 0/0; MRI gives nan("")"""
        if self.const_nonzero(r):
            return '(%s / %s)' % (le, re_)
        if is_pure(re_):
            return '(%s == 0.0 ? fdiv0(%s, %s) : %s / %s)' % (re_, le, re_, self.paren(le), re_)
        if '(' in le and not is_pure(le) and re.search(r'\w\(', le):
            # both operands may call functions: keep C's usual left-to-right order through the helper
            return 'fdiv(%s, %s)' % (le, re_)
        t = self.tmp('d')
        return '((%s = %s) == 0.0 ? fdiv0(%s, %s) : %s / %s)' % (t, re_, le, t, self.paren(le), t)

    def x_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            if ctag(l.type) == 'rec':
                return self._assign_value(l, '%s.copy' % self.paren(self.ex(r).code), 'rec')
            re_ = self.conv(self.val(r), r.type, l.type)
            return self._assign_value(l, re_.code, ctag(l.type))
        if op in ('&&', '||'):
            return Ex('(%s %s %s)' % (self.paren(self.cond(l)), op, self.paren(self.cond(r))), 'b')
        if op == ',':
            return Ex('(%s; %s)' % (self.expr_stmt_code(l), self.val(r).code), ctag(c.type))
        lt, rt = canon(l.type), canon(r.type)
        le, re_ = self.val(l), self.val(r)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            if le.tag in ('c', 'o', 'n') or re_.tag in ('c', 'o', 'n'):
                nl, nr = le.code == 'nil' or is_null(le.code), re_.code == 'nil' or is_null(re_.code)
                if op in ('==', '!=') and (nl or nr):
                    x = le.code if not nl else re_.code
                    return Ex(('%s.nil?' if op == '==' else '!%s.nil?') % self.paren(x), 'b')
                if ptr_category(l.type) == 'char' or ptr_category(r.type) == 'char' or ptr_category(l.type) == 'func':
                    return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
                return Ex(('%s.equal?(%s)' if op == '==' else '!%s.equal?(%s)') % (self.paren(le.code), re_.code), 'b')
            return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
        tg = ctag(c.type)
        if tg == 'c':
            return Ex('(%s %s %s)' % (le.code, op, re_.code), 'c')
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            return Ex('cptr_diff(%s, %s)' % (le.code, re_.code), 'l')
        intlike = tg in ('i', 'u', 'l', 'ul')
        if op == '/' and intlike:
            code = 'idiv(%s, %s)' % (le.code, re_.code)
        elif op == '%' and intlike:
            code = '%s.remainder(%s)' % (self.paren(le.code), re_.code)
        elif op == '/':
            code = self.fdiv_code(le.code, re_.code, r)
        else:
            code = '(%s %s %s)' % (le.code, op, re_.code)
        if tg == 'u':
            code = '(%s & 0xFFFFFFFF)' % code
        elif tg == 'ul':
            code = '(%s & 0xFFFFFFFFFFFFFFFF)' % code
        elif tg == 'f':
            code = 'f32%s' % code if code.startswith('(') and self._balanced(code[1:-1]) else 'f32(%s)' % code
        return Ex(code, tg)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        lv, rhs, tg = self.compound_parts(c)
        return Ex('(%s = %s)' % (lv, rhs), tg)

    def compound_parts(self, c):
        """(lvalue, new value expression, tag) for lhs op= rhs, with C conversions"""
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        lv = self.lvalue(l)
        re_ = self.val(r)
        if lt == 'c':
            return lv, '%s %s %s' % (lv, op, self.paren(re_.code)), 'c'
        common = 'd' if 'd' in (lt, rt) else ('f' if 'f' in (lt, rt) else lt)
        intlike = common in ('i', 'u', 'l', 'ul')
        rc = re_.code
        lvv = lv
        if common in ('d', 'f') and lt in ('i', 'u', 'l', 'ul'):
            lvv = self.to_f(lv)
        if common in ('d', 'f') and rt in ('i', 'u', 'l', 'ul'):
            rc = self.to_f(rc)
        if op == '/' and intlike:
            v = 'idiv(%s, %s)' % (lvv, rc)
        elif op == '%' and intlike:
            v = '%s.remainder(%s)' % (self.paren(lvv), rc)
        elif op == '/':
            v = self.fdiv_code(lvv, rc, r)
        else:
            v = '%s %s %s' % (lvv, op, self.paren(rc))
        if lt in ('i', 'l') and common in ('d', 'f'):
            v = ('d2i(%s)' if lt == 'i' else 'd2l(%s)') % v
        elif lt == 'u':
            v = ('(d2l(%s) & 0xFFFFFFFF)' if common in ('d', 'f') else '(%s) & 0xFFFFFFFF') % v
        elif lt == 'ul':
            v = ('(d2l(%s) & 0xFFFFFFFFFFFFFFFF)' if common in ('d', 'f') else '(%s) & 0xFFFFFFFFFFFFFFFF') % v
        elif lt == 'f':
            v = 'f32(%s)' % v
        return lv, v, lt

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        ea = self.conv(self.val(a), a.type, c.type)
        eb = self.conv(self.val(b), b.type, c.type)
        return Ex('(%s ? %s : %s)' % (self.paren(self.cond(cc)), ea.code, eb.code), ctag(c.type))

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, idx = kids(c)
        b = self.ex(base)
        i = self.val(idx)
        return Ex('%s[%s]' % (self.paren(b.code), i.code), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        b = self.ex(base)
        return Ex('%s.%s' % (self.paren(b.code), rb_field(c.referenced.spelling)), ctag(c.type))

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
            vals = []
            for it in items:
                if strip(it).kind == K.INIT_LIST_EXPR:
                    vals.append(self.init_list(strip(it), et).code)
                elif ctag(et) == 'c' and strip(it).kind == K.STRING_LITERAL and canon(et).kind == T.CONSTANTARRAY:
                    vals.append('CPtr.buf_from(%s, %d)' % (self.lit(self.string_bytes(strip(it))), canon(et).element_count))
                else:
                    vals.append(self.conv(self.val(it), it.type, et).code)
            while len(vals) < n:
                vals.append(self.zero(et) if ctag(et) != 'rec' else '%s.new' % self.rec(et))
            return Ex('[%s]' % ', '.join(vals), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                parts.append(':%s, %s' % (rb_field(f.spelling), self.conv(self.val(it), it.type, f.type).code))
            return Ex('rec_init(%s.new, %s)' % (self.rec(t), ', '.join(parts)), 'rec')
        if len(items) == 1:
            return self.val(items[0])
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
            for i, (a, p) in enumerate(zip(args, params)):
                sa = strip(a)
                if (ptr_category(p.type) == 'scalar' and self.P.mode_of(p) == 'array' and sa.kind == K.UNARY_OPERATOR
                        and unop(sa) == '&' and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    codes = [self.arg(x, q) if j != i else '__a' for j, (x, q) in enumerate(zip(args, params))]
                    return Ex('arr1(%s, ->(__a) { %s(%s) })' % (self.ref_of(kids(sa)[0]), n, ', '.join(codes)), ctag(c.type))
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    codes = [self.arg(x, q) if j != i else '__c' for j, (x, q) in enumerate(zip(args, params))]
                    return Ex('chr1(%s, ->(__c) { %s(%s) })' % (self.ref_of(kids(sa)[0]), n, ', '.join(codes)), ctag(c.type))
            return Ex('%s(%s)' % (n, ', '.join(self.arg(a, p) for a, p in zip(args, params))), ctag(c.type))
        fe = self.ex(callee)
        argcodes = []
        for a in args:
            sa = strip(a)
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and ctag(strip(kids(sa)[0]).type) in NUMTAGS:
                argcodes.append(self.ref_of(kids(sa)[0]))
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
            if is_null(e.code) or e.code == 'nil':
                return 'nil'
            return 'ElemRef.new(%s, 0)' % e.code
        if cat == 'scalar' and pmode == 'array':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = strip(kids(sa)[0])
                if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                    base, idx = kids(o)
                    return self.ex(base).code
        e = self.conv(self.val(a), a.type, p.type)
        return e.code

    # math.h: exp, sin, cos, tan and atan reach glibc unchanged through MRI's Math (rb_math_exp etc. check
    # nothing); the others need C's answers where MRI raises or differs (crt.rb)
    MATH_RB = {'exp': '::Math.exp', 'sin': '::Math.sin', 'cos': '::Math.cos', 'tan': '::Math.tan',
               'atan': '::Math.atan', 'sqrt': 'c_sqrt', 'floor': 'c_floor', 'ceil': 'c_ceil', 'log': 'c_log',
               'log10': 'c_log10', 'asin': 'c_asin', 'acos': 'c_acos'}

    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name == 'fabs':
            return Ex('%s.abs' % self.paren(A(0)), 'd')
        if name in self.MATH_RB:
            return Ex('%s(%s)' % (self.MATH_RB[name], A(0)), 'd')
        if name == 'pow':
            x, y = A(0), A(1)
            # Float#** calls glibc's pow except for a negative base with a non-integral exponent
            if is_pure(x):
                return Ex('(%s < 0.0 ? c_powneg(%s, %s) : %s ** %s)' % (x, x, y, x, self.paren(y)), 'd')
            t = self.tmp('p')
            return Ex('((%s = %s) < 0.0 ? c_powneg(%s, %s) : %s ** %s)' % (t, x, t, y, t, self.paren(y)), 'd')
        if name in ('fprintf', 'snprintf', 'sscanf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}[name]
            head = [A(i) for i in range(fixed)]
            rest = [self.vararg(a, name == 'sscanf') for a in args[fixed:]]
            return Ex('c_%s(%s)' % (name, ', '.join(head + rest)), 'i')
        if name == 'free':
            return Ex('nil', 'v')
        if name in ('calloc', 'malloc', 'realloc'):
            return self.alloc(c, c.type)
        if name in ('fwrite', 'fread'):
            return self.freadwrite(c, name, args)
        if name == 'memset':
            return Ex('c_memset(%s, %s, %s)' % (A(0), A(1), A(2)), 'v')
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return Ex('c_strtod(%s, %s)' % (A(0), self.ref_of(kids(ep)[0])), 'd')
            return Ex('c_strtod(%s, nil)' % A(0), 'd')
        if name == 'time':
            return Ex('c_time()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('c_ctime(%s)' % (self.ex(kids(a0)[0]).code if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('(%s - %s).to_f' % (A(0), A(1)), 'd')
        if name == 'fseeko':
            name = 'fseek'
        return Ex('c_%s(%s)' % (name, ', '.join(A(i) for i in range(len(args)))), tg)

    def vararg(self, a, scanf):
        sa = strip(a)
        if scanf:
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = kids(sa)[0]
                t = ctag(strip(o).type)
                return '[:%s, %s]' % ({'i': 'i', 'd': 'd', 'f': 'f', 'l': 'l'}.get(t, 'i'), self.ref_of(o))
            # a number pointer passed straight through (e.g. rain.c parseStdLine's int *year): the runtime
            # needs the same [tag, ref] pair it gets for &x (lessons/08)
            if ptr_category(sa.type) == 'scalar':
                t = ctag(canon(sa.type).get_pointee())
                if t in ('i', 'u', 'l', 'ul', 'd', 'f'):
                    return '[:%s, %s]' % ({'u': 'i', 'ul': 'l'}.get(t, t), self.val(a).code)
            return self.val(a).code
        return self.val(a).code

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
            return Ex('realloc_(%s, %s)' % (self.val(args[0]).code, n), 'o' if ctag(t) != 'c' else 'c')
        if ctag(t) == 'c':
            return Ex('CPtr.buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('%s.new' % self.rec(et), 'o')
            return Ex('::Array.new(%s) { %s.new }' % (n, self.rec(et)), 'o')
        if et.kind == T.POINTER:
            return Ex('::Array.new(%s)' % n, 'o')
        return Ex('::Array.new(%s, %s)' % (n, self.zero(et)), 'o')

    def count_expr(self, a, b, et, mul):
        return CSEmitter.count_expr(self, a, b, et, mul)

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
                return Ex('c_%s_arr(:%s, %d, %s, %s, %s, %s)' % (name, self.code_of(et), sz, self.ex(base).code, self.val(idx).code, self.val(cnt).code, fc), 'ul')
            if name == 'fwrite':
                return Ex('c_fwrite1(:%s, %d, %s, %s)' % (self.code_of(et), sz, self.ex(o).code, fc), 'ul')
            return Ex('c_fread1(:%s, %d, %s, %s)' % (self.code_of(et), sz, self.ref_of(o), fc), 'ul')
        if self.mode_of_expr(sb) == 'ref':
            et = canon(canon(sb.type).get_pointee())
            if name == 'fwrite':
                return Ex('c_fwrite1(:%s, %d, %s.v, %s)' % (self.code_of(et), sz, self.ex(sb).code, fc), 'ul')
            return Ex('c_fread1(:%s, %d, %s, %s)' % (self.code_of(et), sz, self.ex(sb).code, fc), 'ul')
        bt = canon(sb.type)
        et = canon(bt.get_pointee()) if bt.kind == T.POINTER else canon(bt.element_type)
        return Ex('c_%s_arr(:%s, %d, %s, 0, %s, %s)' % (name, self.code_of(et), sz, self.ex(sb).code, self.val(cnt).code, fc), 'ul')

    # ================================================================== statements
    def local_name(self, d):
        return self.locals.get(decl_key(d), rb_local(d.spelling))

    def declare_local(self, d):
        n = d.spelling
        nn = n
        if n in self.used_names:
            i = 2
            while '%s_%d' % (n, i) in self.used_names:
                i += 1
            nn = '%s_%d' % (n, i)
        self.used_names.add(nn)
        self.locals[decl_key(d)] = rb_local(nn)
        return rb_local(nn)

    def stmt(self, c, ind):
        k = c.kind
        p = '  ' * ind
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
            out = [p + 'if %s' % self.cond(ch[0])]
            out += self.stmt(ch[1], ind + 1)
            e = ch[2] if len(ch) > 2 else None
            while e is not None:
                if e.kind == K.IF_STMT:
                    ec = kids(e)
                    out.append(p + 'elsif %s' % self.cond(ec[0]))
                    out += self.stmt(ec[1], ind + 1)
                    e = ec[2] if len(ec) > 2 else None
                else:
                    out.append(p + 'else')
                    out += self.stmt(e, ind + 1)
                    e = None
            out.append(p + 'end')
            return out
        if k == K.WHILE_STMT:
            ch = kids(c)
            self.loops.append(('while', None))
            out = [p + 'while %s' % self.cond(ch[0])] + self.stmt(ch[1], ind + 1) + [p + 'end']
            self.loops.pop()
            return out
        if k == K.DO_STMT:
            ch = kids(c)
            cnd = self.cond(ch[1])
            self.loops.append(('do', cnd))
            out = [p + 'while true'] + self.stmt(ch[0], ind + 1) + [p + '  break unless %s' % self.paren(cnd), p + 'end']
            self.loops.pop()
            return out
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            ctx = self.loops[-1] if self.loops else None
            if ctx and ctx[0] == 'switch-if':
                return []           # case/when switch: the section-final break is dropped
            return [p + 'break']
        if k == K.CONTINUE_STMT:
            return self.continue_stmt(ind)
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'return']
            if ctag(self.cur_ret) == 'rec':
                return [p + 'return %s.copy' % self.paren(self.ex(ch[0]).code)]
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            return [p + 'return %s' % e.code]
        if k == K.NULL_STMT:
            return []
        if k in (K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'goto/label')
            return []
        return [p + self.expr_stmt_code(c)]

    def continue_stmt(self, ind):
        p = '  ' * ind
        out = []
        for i in range(len(self.loops) - 1, -1, -1):
            kind, info = self.loops[i]
            if kind == 'switch-loop':
                self.switch_continue[-1][1] = True
                return [p + '%s = true' % self.switch_continue[-1][0], p + 'break']
            if kind == 'switch-if':
                continue
            if kind == 'for' and info:
                out += [p + x for x in info]
            elif kind == 'do':
                return [p + 'break unless %s' % self.paren(info), p + 'next']
            return out + [p + 'next']
        return out + [p + 'next']

    def expr_stmt_code(self, c):
        """an expression evaluated for its side effects"""
        s = c
        while s.kind == K.PAREN_EXPR or (s.kind == K.UNEXPOSED_EXPR and len(kids(s)) == 1):
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) == 'v':
            return self.expr_stmt_code(kids(s)[-1])
        if s.kind == K.BINARY_OPERATOR and binop(s) == '=':
            l, r = kids(s)
            lv = self.lvalue(l)
            if ctag(l.type) == 'rec':
                return '%s = %s.copy' % (lv, self.paren(self.ex(r).code))
            return '%s = %s' % (lv, self.conv(self.val(r), r.type, l.type).code)
        if s.kind == K.BINARY_OPERATOR and binop(s) == ',':
            l, r = kids(s)
            return self.expr_stmt_code(l) + '; ' + self.expr_stmt_code(r)
        if s.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            lv, v, tg = self.compound_parts(s)
            op = binop(s)[:-1]
            r = kids(s)[1]
            simple = '%s %s %s' % (lv, op, self.paren(self.val(r).code))
            if v == simple and op in ('+', '-', '*'):
                return '%s %s= %s' % (lv, op, self.paren(self.val(r).code))
            return '%s = %s' % (lv, v)
        if s.kind == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            a = kids(s)[0]
            lv = self.lvalue(a)
            d = '+' if '++' in unop(s) else '-'
            tg = ctag(a.type)
            if tg == 'f':
                return '%s = f32(%s %s 1.0)' % (lv, lv, d)
            if tg == 'd':
                return '%s %s= 1.0' % (lv, d)
            if tg == 'c':
                return '%s = %s %s 1' % (lv, lv, d)
            if tg == 'u':
                return '%s = (%s %s 1) & 0xFFFFFFFF' % (lv, lv, d)
            if tg == 'ul':
                return '%s = (%s %s 1) & 0xFFFFFFFFFFFFFFFF' % (lv, lv, d)
            return '%s %s= 1' % (lv, d)
        e = self.ex(c)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
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
        out = []
        if init is not None:
            if init.kind == K.DECL_STMT:
                for d in kids(init):
                    out += self.local_decl(d, ind)
            else:
                out.append(p + self.expr_stmt_code(init))
        inc_lines = [self.expr_stmt_code(inc)] if inc is not None else []
        inc_lines = [x for l in inc_lines for x in l.split('; ')]
        self.loops.append(('for', inc_lines))
        body_lines = self.stmt(body, ind + 1)
        self.loops.pop()
        out.append(p + 'while %s' % (self.cond(cond) if cond is not None else 'true'))
        out += body_lines
        out += [p + '  ' + x for x in inc_lines]
        out.append(p + 'end')
        return out

    def case_label(self, x):
        """an integer case label as a Ruby integer literal (so `case` dispatches through a hash)"""
        v = evaluate(strip(x))
        if v is not None and v[0] == 'int':
            return str(v[1])
        return self.val(x).code

    def switch(self, c, ind):
        p = '  ' * ind
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
        sv = e.code
        if e.tag in ('b', 'L'):
            sv = '(%s ? 1 : 0)' % sv
        pre = []
        if not re.fullmatch(r'[\w.$@]+', sv):
            tmp = self.tmp('sw')
            pre = [p + '%s = %s' % (tmp, sv)]
            sv = tmp
        allvals = [l for sec in sections for l in sec[0] if l is not None]

        simple = all(self.ends_clean(sec[1]) for sec in sections[:-1]) and all(not self.inner_break(sec[1]) for sec in sections)
        if simple:
            out = list(pre) + [p + 'case %s' % sv]
            ordered = [s for s in sections if None not in s[0]] + [s for s in sections if None in s[0]]
            for labels, stmts in ordered:
                if None in labels:
                    head = p + 'else'
                else:
                    head = p + 'when %s' % ', '.join(labels)
                self.loops.append(('switch-if', None))
                lines = []
                for s_ in stmts:
                    lines += self.stmt(s_, ind + 1)
                self.loops.pop()
                out += [head] + lines
            out.append(p + 'end')
            return out

        def test(labels):
            vals = [l for l in labels if l is not None]
            conds = ['%s == %s' % (sv, v) for v in vals]
            if None in labels:
                conds.append('(%s)' % ' && '.join('%s != %s' % (sv, v) for v in allvals) if allvals else 'true')
            return ' || '.join(conds)
        # general case: a one-pass loop, fall-through through a flag
        ft = self.tmp('ft')
        cont = self.tmp('cont')
        self.switch_continue.append([cont, False])
        self.loops.append(('switch-loop', None))
        out = list(pre) + [p + '%s = false' % ft, p + 'while true']
        for si, (labels, stmts) in enumerate(sections):
            lines = []
            for s_ in stmts:
                lines += self.stmt(s_, ind + 2)
            out.append(p + '  if %s || %s' % (ft, test(labels)))
            out += lines
            if not self.terminates(stmts):
                out.append(p + '    %s = true' % ft)
            out.append(p + '  end')
        out.append(p + '  break')
        out.append(p + 'end')
        self.loops.pop()
        if self.switch_continue.pop()[1]:
            out = [p + '%s = false' % cont] + out + [p + 'if %s' % cont] + self.continue_stmt(ind + 1) + [p + 'end']
        return out

    def local_decl(self, d, ind):
        p = '  ' * ind
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
        boxed = decl_key(d) in self.boxed_locals
        if t.kind == T.CONSTANTARRAY:
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return [p + '%s = %s' % (name, self.init_list(strip(init[-1]), t).code)]
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return [p + '%s = CPtr.buf_from(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)]
                return [p + '%s = CPtr.buf(%d)' % (name, t.element_count)]
            return [p + '%s = %s' % (name, self.new_array(t))]
        if ctag(t) == 'rec':
            if init:
                return [p + '%s = %s.copy' % (name, self.paren(self.ex(init[-1]).code))]
            return [p + '%s = %s.new' % (name, self.rec(t))]
        v = self.conv(self.val(init[-1]), init[-1].type, d.type).code if init else self.zero(d.type)
        if boxed:
            if self.cur_hoist:
                bx = self.hoisted_box(name)
                return [p + '%s = %s' % (name, bx), p + '%s.v = %s' % (name, v)]
            return [p + '%s = Box.new(%s)' % (name, v)]
        return [p + '%s = %s' % (name, v)]

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return '::Array.new(%d) { %s.new }' % (n, self.rec(et))
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return '::Array.new(%d) { CPtr.buf(%d) }' % (n, et.element_count)
        if et.kind == T.CONSTANTARRAY:
            return '::Array.new(%d) { ::Array.new(%d, %s) }' % (n, et.element_count, self.zero(et.element_type))
        if et.kind == T.POINTER:
            return '::Array.new(%d)' % n
        return '::Array.new(%d, %s)' % (n, self.zero(et))

    # ================================================================== functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.loops = []
        self.switch_continue = []
        self.tmp_count = 0
        self.cur_ret = c.result_type
        self.boxed_locals = set()
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]

        def scan(x):
            if x.kind == K.UNARY_OPERATOR and unop(x) == '&':
                o = strip(kids(x)[0])
                if o.kind == K.DECL_REF_EXPR and o.referenced is not None and o.referenced.kind in (K.VAR_DECL, K.PARM_DECL):
                    d = o.referenced
                    boxable = ctag(d.type) in NUMTAGS or (canon(d.type).kind == T.POINTER)
                    if boxable and (d.kind == K.PARM_DECL or (d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL and d.storage_class != front.ci.StorageClass.STATIC)):
                        self.boxed_locals.add(decl_key(d))
            for y in x.get_children():
                scan(y)
        scan(body)
        ps = [self.declare_local(prm) for prm in params]
        out = ['  # %s:%d' % (b, c.location.line), '  def %s(%s)' % (self.fname[key], ', '.join(ps))]
        self.cur_hoist = key not in self.reentrant
        self.cur_fname = self.fname[key]
        lines = []
        for prm, nm in zip(params, ps):
            if decl_key(prm) in self.boxed_locals:
                if self.cur_hoist:
                    bx = self.hoisted_box(nm)
                    lines += ['    %s.v = %s' % (bx, nm), '    %s = %s' % (nm, bx)]
                else:
                    lines.append('    %s = Box.new(%s)' % (nm, nm))
        lines += self.stmt(body, 2)
        return out + lines + ['  end']

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = rb_class(name)
        out = ['  class %s' % nm]
        if fields:
            out.append('    attr_accessor %s' % ', '.join(':' + rb_field(f.spelling) for f in fields))
        out.append('    def initialize')
        copy = ['    def copy', '      c = dup']
        for f in fields:
            t = canon(f.type)
            fn = rb_field(f.spelling)
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    out.append('      @%s = CPtr.buf(%d)' % (fn, t.element_count))
                    copy.append('      c.%s = @%s.copy' % (fn, fn))
                else:
                    out.append('      @%s = %s' % (fn, self.new_array(t)))
                    if et.kind == T.RECORD:
                        copy.append('      c.%s = @%s.map(&:copy)' % (fn, fn))
                    elif et.kind == T.CONSTANTARRAY:
                        copy.append('      c.%s = @%s.map(&:dup)' % (fn, fn))
                    else:
                        copy.append('      c.%s = @%s.dup' % (fn, fn))
            elif t.kind == T.RECORD:
                out.append('      @%s = %s.new' % (fn, self.rec(t)))
                copy.append('      c.%s = @%s.copy' % (fn, fn))
            else:
                out.append('      @%s = %s' % (fn, self.zero(f.type)))
        out.append('    end')
        copy += ['      c', '    end']
        return out + copy + ['  end', '']

    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        self.boxed_locals = set(); self.locals = {}
        t = canon(c.type)
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return '  %s = %s' % (name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return '  %s = CPtr.buf_from(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return '  %s = CPtr.buf(%d)' % (name, t.element_count)
            return '  %s = %s' % (name, self.new_array(t))
        if t.kind == T.RECORD:
            return '  %s = %s.new' % (name, self.rec(t))
        v = self.conv(self.val(init[-1]), init[-1].type, c.type).code if init else self.zero(c.type)
        if k in self.boxed_globals:
            return '  %s = Box.new(%s)' % (name, v)
        return '  %s = %s' % (name, v)

    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        self.static_locals = []
        self.cur_file = None
        self.boxed_locals = set(); self.locals = {}
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
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                glob.append('  %s = %s' % (name, self.init_list(strip(init[-1]), t).code))
            elif ctag(t) == 'c' and t.kind == T.CONSTANTARRAY:
                glob.append('  %s = CPtr.buf_from(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count))
            elif init:
                glob.append('  %s = %s' % (name, self.conv(self.val(init[-1]), init[-1].type, d.type).code))
            else:
                glob.append('  %s = %s' % (name, self.zero(d.type)))
        out = ['# Generated from EPA SWMM 5.2.4 by tools/c2x/emit_ruby.py. Do not edit by hand;',
               '# fix the translator or swmm5/crt.rb instead.',
               '# frozen_string_literal: false', '',
               'module SWMM5', '  include CRT', '  extend self',
               '  # the runtime classes, visible by name inside the record classes below too',
               '  CPtr = CRT::CPtr', '  Box = CRT::Box', '  FieldRef = CRT::FieldRef', '  ElemRef = CRT::ElemRef',
               '  GlobalRef = CRT::GlobalRef', '']
        for n, v in self.F.enum_consts.items():
            out.append('  %s = %d' % (rb_const(n), v))
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, s) in m.items():
                if n in self.macro_global and n not in done and kind in ('int', 'float') and n not in self.F.enum_consts:
                    done.add(n)
                    if kind == 'int':
                        v = re.sub(r'[uUlL]+$', '', s)
                        if len(v.lstrip('-')) > 1 and v.lstrip('-').startswith('0'):
                            v = str(int(v, 8))
                    else:
                        v = self.rb_float(s)
                    out.append('  %s = %s' % (rb_const(n), v))
        out.append('')
        for bts, name in self.lits.items():
            out.append('  %s = lit(%s)' % (name, rb_bytes(bts)))
        out += ['', '  # boxes for the C locals whose address is taken, in functions that cannot be re-entered (one per',
                '  # local, allocated once; see find_reentrant in tools/c2x/emit_ruby.py)']
        for name in self.hoisted:
            out.append('  %s = Box.new(nil)' % name)
        out += ['']
        for name, c in self.F.records.items():
            out += self.record(name, c)
        out += funcs
        out += ['  def self.init_globals', '    # C globals and function statics, with their initial values']
        out += ['  ' + g for g in glob]
        out += ['  end', '  init_globals', 'end', '']
        open(os.path.join(outdir, 'engine.rb'), 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = RbEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_rb')
    print('%d problems' % len(probs))
    for p in probs[:100]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
