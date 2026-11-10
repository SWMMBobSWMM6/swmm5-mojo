"""
emit_f90.py - EPA SWMM 5.2.4 C  ->  Fortran 2008 (one module, swmm5_engine)

Mapping (see the swmm5-fortran README):
  structs/unions     -> derived types (intrinsic assignment copies like C; pointer components stay shallow)
  T* indexed         -> pointer arrays, lower bound 0          T* used with ->  -> type(T), pointer
  double* param      -> intent(inout), target dummy (C passes &x)   by-value scalars -> VALUE dummies
  char*, char[]      -> type(CPtr) (int8 buffer + offset); fixed char arrays are int8 arrays seen through cview()
  T** / arrays of T* -> arrays of one-pointer wrapper types
  void*              -> type(c_ptr)                  function pointers -> abstract interfaces
  a[i][j] (fixed)    -> a(j, i)  (transposed, so a C row is a contiguous Fortran column)
  && || ?:           -> explicit short-circuit when the right side could fault or has side effects
                        (Fortran's .and./.or. may evaluate both operands)
  switch             -> select case; fall-through switches dispatch to labels so C's order is kept
  side effects inside expressions (x = y in a condition, ++) -> hoisted into statements before the use
"""
import os, re, sys, collections, glob
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import CSEmitter, Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES

HERE = os.path.dirname(os.path.abspath(__file__))
RUNTIME_DIR = os.path.join(HERE, '../../f90/runtime')
IND = '   '

F_RESERVED = set('''abs sqrt exp log log10 sin cos tan acos asin atan atan2 int real mod modulo merge associated allocated size
min max iand ior ieor not ishft shifta shiftl shiftr achar ichar char transfer huge null present c_loc c_f_pointer
c_associated c_null_ptr c_ptr c_double c_int dp sp int8 int32 int64 real32 real64 aint anint floor ceiling nint len trim
index scan verify len_trim lbound ubound allocate deallocate nullify exit cycle stop return call if then else elseif end
endif enddo do while select case default type module contains use implicit none function subroutine result recursive
pointer target value intent in out inout optional save data parameter logical integer character complex double precision
kind sign dble float ifix idint sngl epsilon tiny maxval minval sum product count any all iso_fortran_env iso_c_binding
print write read open close inquire rewind backspace format goto continue go block associate procedure interface abstract
nopass pass extends class public private protected sequence bind entry pure elemental impure dimension external intrinsic
equivalence common namelist include where forall elsewhere stat output_unit date_and_time random_number flush
swmm5_engine crt_base crt_format crt_io res_ lbound shape reshape spread pack unpack dot_product matmul cshift eoshift
selected_int_kind selected_real_kind digits range precision radix exponent fraction nearest spacing rrspacing scale
set_exponent bit_size btest ibset ibclr ibits mvbits popcnt poppar leadz trailz storage_size is_iostat_end
new_line adjustl adjustr repeat lge lgt lle llt dim dprod cmplx conjg aimag move_alloc get_command_argument
command_argument_count system_clock cpu_time mask32 iobuf'''.split())


def runtime_names():
    """public names defined by the hand-written runtime modules (generated names must not shadow them)"""
    names = set()
    names |= set('''ode_nmax ode_y ode_yscal ode_dydx ode_yerr ode_ytemp ode_ak2 ode_ak3 ode_ak4 ode_ak5 ode_ak6
                    ode_rkqs ode_rkck libc_realpath runswmm'''.split())
    for f in glob.glob(os.path.join(RUNTIME_DIR, 'crt_*.f90')):
        s = open(f).read().lower()
        names |= set(re.findall(r'(?:function|subroutine)\s+(\w+)', s))
        names |= set(re.findall(r'^\s*type\s*::\s*(\w+)', s, re.M))
        names |= set(re.findall(r'^\s*interface\s+(\w+)', s, re.M))
        names |= set(re.findall(r'^\s*module\s+(\w+)', s, re.M))
        for decl in re.findall(r'^\s*(?:integer|real|logical|type\(\w+\)|character)[^:\n]*::\s*([^\n!]+)', s, re.M):
            for part in re.split(r',(?![^(]*\))', decl):
                m = re.match(r'\s*(\w+)', part)
                if m:
                    names.add(m.group(1))
    return names


def flit(s, tg='d'):
    """C floating literal spelling -> Fortran literal of kind dp (or sp)"""
    f = s.rstrip('lL')
    if f[-1:] in 'fF':
        f = f[:-1]
    if f.startswith('.'):
        f = '0' + f
    if 'e' in f.lower():
        m, e = re.split('[eE]', f)
        if m.endswith('.'):
            m += '0'
        if '.' not in m:
            m += '.0'
        f = '%se%s' % (m, e)
    else:
        if f.endswith('.'):
            f += '0'
        if '.' not in f:
            f += '.0'
    return f + ('_sp' if tg == 'f' else '_dp')


def fstring(b):
    """bytes -> Fortran character expression"""
    parts = []
    cur = ''
    for ch in b:
        if 32 <= ch < 127:
            cur += '""' if ch == 34 else chr(ch)
        else:
            if cur:
                parts.append('"%s"' % cur); cur = ''
            parts.append('achar(%d)' % ch)
    if cur or not parts:
        parts.append('"%s"' % cur)
    return ' // '.join(parts)


class FX:
    """a translated expression: Fortran code, tag (see F90Emitter.ftag), whether it is a variable designator,
    and whether it designates a POINTER object"""
    __slots__ = ('code', 'tag', 'var', 'ptr')

    def __init__(self, code, tag, var=False, ptr=False):
        self.code, self.tag, self.var, self.ptr = code, tag, var, ptr

    def __repr__(self):
        return 'FX(%r,%r%s%s)' % (self.code, self.tag, ',var' if self.var else '', ',ptr' if self.ptr else '')


class Ctx:
    """loop or switch being translated (for break/continue)"""
    def __init__(self, kind, label=None):
        self.kind = kind          # 'while' | 'for' | 'do' | 'switch'
        self.label = label        # continue label (loops) or end label (switch)
        self.used = False
        self.plain_cycle = False  # for-loop without increment: continue -> cycle


class F90Emitter(CSEmitter):
    def __init__(self, F):
        CSEmitter.__init__(self, F)
        self.rt_names = runtime_names()
        self.wrappers = collections.OrderedDict()   # Fortran wrapper type name -> component declaration
        self.fps = collections.OrderedDict()        # signature -> (name, function type)
        self.zero_objs = collections.OrderedDict()  # record name -> zero object name
        self.init_lines = []                        # executable lines of swmm5_init
        self.addr_cache = {}
        self.init_cache = {}
        self.callback_groups = self._callback_groups()
        self._fnames()

    # ================================================================== names (Fortran is case-insensitive)
    def _give(self, n):
        n = n.lstrip('@')
        if n.startswith('_'):
            n = 'u' + n
        base = n
        i = 0
        while n.lower() in self.taken:
            i += 1
            n = '%s_%s' % (base, 'c' if i == 1 else str(i))
        self.taken.add(n.lower())
        return n

    def _fnames(self):
        F = self.F
        self.taken = {n.lower() for n in F_RESERVED} | {n.lower() for n in self.rt_names}
        self.rname = {}
        for name in F.records:
            self.rname[name] = self._give(name)
        self.ffname = {}
        for key in F.funcs:
            pref = self.fname[key].lstrip('@')
            if pref.endswith('_') and pref[:-1] in ('S', 'R', 'CPtr', 'CFile', 'Math', 'System', 'Console', 'Program'):
                pref = pref[:-1]
            self.ffname[key] = self._give(pref)
        self.fgname = {}
        for k, c in F.globals.items():
            self.fgname[k] = self._give(self.gname[k].lstrip('@').rstrip('_') if self.gname[k].endswith('_') else self.gname[k])
        self.fenum = {}
        for n in F.enum_consts:
            self.fenum[n] = self._give(n)
        self.fmacro = {}
        for b, m in F.macros.items():
            for n, v in m.items():
                if n in self.macro_global and n not in F.enum_consts and n not in self.fmacro and v[0] in ('int', 'float'):
                    self.fmacro[n] = self._give(n)
        # record components: unique within the record (case-insensitively), no leading underscore
        self.fieldname = {}
        for name, c in F.records.items():
            seen = set()
            for f in kids(c):
                if f.kind != K.FIELD_DECL:
                    continue
                n = f.spelling
                if n.startswith('_'):
                    n = 'u' + n
                base = n; i = 1
                while n.lower() in seen:
                    i += 1; n = '%s_%d' % (base, i)
                seen.add(n.lower())
                self.fieldname[(name, f.spelling)] = n
        self.static_names = {}

    def field(self, f):
        p = f.semantic_parent
        rn = record_name(p.type) if p is not None else None
        return self.fieldname.get((rn, f.spelling), f.spelling)

    def rec(self, t):
        n = record_name(t)
        return self.rname.get(n, n)

    def func_ref(self, d, cur_file):
        keys = self.F.func_by_decl.get(d.spelling)
        if not keys:
            return None
        if len(keys) == 1:
            return self.ffname[keys[0]]
        for k in keys:
            if k[0] == cur_file:
                return self.ffname[k]
        for k in keys:
            if not front.is_static(self.F.funcs[k]):
                return self.ffname[k]
        return self.ffname[keys[0]]

    def global_key(self, d):
        k = decl_key(d)
        if k in self.fgname:
            return k
        for gk, c in self.F.globals.items():
            if c.spelling == d.spelling and not front.is_static(c):
                return gk
        return None

    def macro_name(self, n):
        return self.fmacro.get(n)

    def static_local_name(self, d):
        k = decl_key(d)
        if k not in self.static_names:
            self.static_names[k] = self._give('%s_%s' % (d.semantic_parent.spelling, d.spelling))
        return self.static_names[k]

    def local_name(self, d):
        return self.locals.get(decl_key(d), d.spelling)

    def new_local(self, n):
        if n.startswith('_'):
            n = 'u' + n
        base = n
        i = 0
        while n.lower() in self.taken or n.lower() in self.local_taken:
            i += 1
            n = '%s_%s' % (base, 'l' if i == 1 else str(i))
        self.local_taken.add(n.lower())
        return n

    def declare_local(self, d):
        n = self.new_local(d.spelling)
        self.locals[decl_key(d)] = n
        return n

    def temp(self, spec, prefix='t'):
        """scratch variable declared at the top of the current procedure"""
        self.ntemp += 1
        n = self.new_local('%s%d_' % (prefix, self.ntemp))
        if '(:)' in spec:
            spec, dims = spec.replace('(:)', ''), '(:)'
        elif '(0:0)' in spec:
            spec, dims = spec.replace('(0:0)', ''), '(0:0)'
        else:
            dims = ''
        self.decls.append('%s :: %s%s' % (spec, n, dims))
        return n

    def label(self):
        self.nlabel += 1
        return self.nlabel

    # ================================================================== types
    def ftag(self, t):
        """tag of a C type: i u l ul d f | c (char*) | carr (fixed char array) | arr (fixed array) | rec |
           o (pointer: record/scalar/pointer arrays, objects) | file | vp (void*) | fp (function pointer) | v"""
        t = canon(t)
        k = t.kind
        if k in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            return 'carr' if front.is_char(t.element_type) else 'arr'
        tg = ctag(t)
        if tg in ('c', 'o'):
            cat = ptr_category(t)
            return {'file': 'file', 'void': 'vp', 'func': 'fp', 'char': 'c'}.get(cat, 'o')
        return tg

    def scalar_type(self, t):
        tg = ctag(t)
        return {'i': 'integer(int32)', 'u': 'integer(int64)', 'l': 'integer(int64)', 'ul': 'integer(int64)',
                'd': 'real(dp)', 'f': 'real(sp)'}.get(tg)

    def wrapper(self, comp, hint):
        for n, d in self.wrappers.items():
            if d == comp:
                return n
        n = self._give(hint)
        self.wrappers[n] = comp
        return n

    def elem_ptr_type(self, et):
        """Fortran element type for a C array whose elements are pointers"""
        et = canon(et)
        c = ptr_category(et)
        if c == 'char':
            return 'type(CPtr)'
        if c == 'file':
            return 'type(%s)' % self.wrapper('type(CFile), pointer :: p => null()', 'file_ptr')
        pe = canon(et.get_pointee())
        if c == 'record':
            return 'type(%s)' % self.wrapper('type(%s), pointer :: p => null()' % self.rec(pe), self.rec(pe) + '_ptr')
        if c == 'scalar':
            st = self.scalar_type(pe)
            hint = {'real(dp)': 'dp_row', 'integer(int32)': 'i4_row', 'real(sp)': 'sp_row', 'integer(int64)': 'i8_row'}[st]
            return 'type(%s)' % self.wrapper('%s, pointer :: p(:) => null()' % st, hint)
        if c == 'ptrptr':
            inner = self.elem_ptr_type(pe)
            return 'type(%s)' % self.wrapper('%s, pointer :: p(:) => null()' % inner, inner[5:-1] + '_rows')
        return 'type(c_ptr)'

    def fp_name(self, t):
        t = canon(t)
        if t.kind == T.POINTER:
            t = canon(t.get_pointee())
        sig = (canon(t.get_result()).spelling,) + tuple(canon(a).spelling for a in t.argument_types())
        if sig not in self.fps:
            if sig == ('void', 'double', 'double *', 'double *'):
                n = 'ode_derivs'
            else:
                n = 'fp%d' % len(self.fps)
            self.taken.add(n.lower())
            self.fps[sig] = (n, t)
        return self.fps[sig][0]

    def spec(self, t, mode=None, d=None):
        """(type-spec, [attributes], dims) for a variable of C type t"""
        t = canon(t)
        st = self.scalar_type(t)
        if st:
            return st, [], ''
        if t.kind == T.RECORD:
            return 'type(%s)' % self.rec(t), [], ''
        cat = ptr_category(t)
        if mode is None and d is not None:
            mode = self.P.mode_of(d)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            et = canon(t.element_type)
            n = t.element_count if t.kind == T.CONSTANTARRAY else None
            dims = '(0:%d)' % (n - 1) if n is not None else '(0:)'
            if front.is_char(et):
                return 'integer(int8)', [], dims
            if et.kind == T.CONSTANTARRAY:
                inner = canon(et.element_type)
                d2 = '(0:%d, 0:%d)' % (et.element_count - 1, n - 1)
                if front.is_char(inner):
                    return 'integer(int8)', [], d2
                if inner.kind == T.RECORD:
                    return 'type(%s)' % self.rec(inner), [], d2
                return self.scalar_type(inner), [], d2
            if et.kind == T.POINTER:
                return self.elem_ptr_type(et), [], dims
            s, a, _ = self.spec(et, mode='obj')
            return s, a, dims
        if cat == 'char':
            return 'type(CPtr)', [], ''
        if cat == 'file':
            return 'type(CFile)', ['pointer'], ''
        if cat == 'void':
            return 'type(c_ptr)', [], ''
        if cat == 'func':
            return 'procedure(%s)' % self.fp_name(t), ['pointer'], ''
        e = canon(t.get_pointee())
        if cat == 'record':
            if mode == 'array':
                return 'type(%s)' % self.rec(e), ['pointer'], '(:)'
            return 'type(%s)' % self.rec(e), ['pointer'], ''
        if cat == 'scalar':
            if mode == 'ref':
                return self.scalar_type(e), ['REF'], ''
            return self.scalar_type(e), ['pointer'], '(:)'
        if cat == 'ptrptr':
            if mode == 'ref':
                s, a, dims = self.spec(e, mode='obj' if ptr_category(e) == 'record' else 'array')
                return s, a + ['REF'], dims
            return self.elem_ptr_type(e), ['pointer'], '(:)'
        return 'type(c_ptr)', [], ''

    def decl_line(self, name, t, mode=None, d=None, extra=(), drop=(), dims_override=None):
        s, attrs, dims = self.spec(t, mode, d)
        if dims_override:
            dims = dims_override
        attrs = [a for a in attrs if a != 'REF' and a not in drop] + [a for a in extra if a not in attrs]
        if 'pointer' in attrs and 'target' in attrs:
            attrs.remove('target')
        return '%s%s :: %s%s' % (s, ''.join(', ' + a for a in attrs), name, dims)

    def zero_obj(self, t):
        n = self.rec(t)
        if n not in self.zero_objs:
            self.zero_objs[n] = self._give('zero_' + n)
        return self.zero_objs[n]

    def zero_value(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0_int64', 'l': '0_int64', 'ul': '0_int64', 'd': '0.0_dp', 'f': '0.0_sp'}.get(tg)

    def null_of(self, t):
        tg = self.ftag(t)
        return {'c': 'cnull()', 'vp': 'c_null_ptr'}.get(tg, 'null()')

    def _callback_groups(self):
        """function name -> list of functions bound to the same function-pointer type"""
        groups = collections.defaultdict(list)
        for n in self.P.func_values:
            for fk in self.F.func_by_decl.get(n, []):
                fc = self.F.funcs[fk]
                groups[canon(fc.type).spelling].append(fk)
        out = {}
        for sp, fks in groups.items():
            for fk in fks:
                out[fk] = fks
        return out

    # ================================================================== expressions
    # Every handler returns an FX.  Side effects needed before the value is available go to self.pre.

    def run(self, fn):
        saved = self.pre
        self.pre = []
        try:
            r = fn()
        finally:
            lines = self.pre
            self.pre = saved
        return r, lines

    @staticmethod
    def unparen(s):
        while s.startswith('(') and s.endswith(')') and CSEmitter._balanced(s[1:-1]):
            s = s[1:-1]
        return s

    def problem(self, c, msg):
        loc = '%s:%s' % (os.path.basename(c.location.file.name) if c.location.file else '?', c.location.line)
        self.problems.append('%s %s' % (loc, msg))

    def ex(self, c):
        m = getattr(self, 'f_' + c.kind.name, None)
        if m is None:
            self.problem(c, 'unhandled expression ' + c.kind.name)
            return FX('0', '?')
        return m(c)

    def val(self, c):
        e = self.ex(c)
        if e.tag == 'b' and ctag(c.type) in NUMTAGS:
            return self.b2num(e, ctag(c.type))
        return e

    def b2num(self, e, tg):
        one, zero = {'i': ('1', '0'), 'd': ('1.0_dp', '0.0_dp'), 'f': ('1.0_sp', '0.0_sp')}.get(tg, ('1_int64', '0_int64'))
        return FX('merge(%s, %s, %s)' % (one, zero, self.unparen(e.code)), tg)

    def cond(self, c):
        return self.truth(self.ex(c))

    def truth(self, e):
        tg = e.tag
        if tg == 'b':
            return e.code
        if tg in ('i', 'u', 'l', 'ul'):
            return '(%s /= 0)' % e.code
        if tg == 'd':
            return '(%s /= 0.0_dp)' % e.code
        if tg == 'f':
            return '(%s /= 0.0_sp)' % e.code
        if tg == 'c':
            return '(.not. cisnull(%s))' % e.code
        if tg == 'vp':
            return 'c_associated(%s)' % e.code
        if tg == 'n':
            return '.false.'
        if tg == 'fp' and not e.ptr:
            return '.true.'
        return 'associated(%s)' % e.code

    def is_int_lit(self, code):
        return re.fullmatch(r'\(?-?\d+\)?(_int64)?', code) is not None

    def int_lit_value(self, code):
        return int(re.sub(r'[()]|_int64', '', code))

    def conv(self, e, src_t, dst_t):
        """C conversion of value e (C type src_t) to C type dst_t"""
        d = ctag(dst_t)
        s = e.tag
        if s == 'b' and d in NUMTAGS:
            return self.b2num(e, d)
        if d not in NUMTAGS:
            if e.tag == 'n' or (canon(dst_t).kind == T.POINTER and self.is_int_lit(e.code) and self.int_lit_value(e.code) == 0
                                and s in NUMTAGS):
                return FX(self.null_of(dst_t), 'n')
            return e
        if s == d or s not in NUMTAGS:
            return e if s in NUMTAGS else FX(e.code, d)
        lit = self.is_int_lit(e.code)
        if d == 'i':
            if s == 'd':
                return FX('d2i(%s)' % self.unparen(e.code), 'i')
            if s == 'f':
                return FX('f2i(%s)' % self.unparen(e.code), 'i')
            if s == 'u':
                return FX('u2i(%s)' % self.unparen(e.code), 'i')
            if lit and -2**31 <= self.int_lit_value(e.code) < 2**31:
                return FX(str(self.int_lit_value(e.code)) if self.int_lit_value(e.code) >= 0 else '(%d)' % self.int_lit_value(e.code), 'i')
            return FX('int(%s, int32)' % self.unparen(e.code), 'i')
        if d in ('l', 'ul'):
            if s == 'd':
                return FX('d2l(%s)' % self.unparen(e.code), d)
            if s == 'f':
                return FX('d2l(real(%s, dp))' % self.unparen(e.code), d)
            if s in ('l', 'ul', 'u'):
                return FX(e.code, d)
            if lit:
                v = self.int_lit_value(e.code)
                return FX('%d_int64' % v if v >= 0 else '(%d_int64)' % v, d)
            return FX('int(%s, int64)' % self.unparen(e.code), d)
        if d == 'u':
            if s in ('d', 'f'):
                return FX('i2u(d2l(real(%s, dp)))' % self.unparen(e.code), 'u')
            if lit and self.int_lit_value(e.code) >= 0:
                return FX('%d_int64' % self.int_lit_value(e.code), 'u')
            return FX('i2u(int(%s, int64))' % self.unparen(e.code), 'u')
        if d == 'd':
            if lit:
                v = self.int_lit_value(e.code)
                return FX('%d.0_dp' % v if v >= 0 else '(%d.0_dp)' % v, 'd')
            return FX('real(%s, dp)' % self.unparen(e.code), 'd')
        if d == 'f':
            if lit:
                v = self.int_lit_value(e.code)
                return FX('%d.0_sp' % v if v >= 0 else '(%d.0_sp)' % v, 'f')
            return FX('real(%s, sp)' % self.unparen(e.code), 'f')
        return e

    # --- leaves
    def f_INTEGER_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'\d+[uUlL]*', toks[0]):
            v = int(re.sub(r'[uUlL]+$', '', toks[0]))
        elif len(toks) == 1 and self.macro_name(toks[0]):
            return FX(self.macro_name(toks[0]), tg)
        else:
            r = evaluate(c)
            v = r[1] if r else 0
        if tg in ('l', 'u', 'ul') or v > 2147483647:
            return FX('%d_int64' % v if v >= 0 else '(%d_int64)' % v, tg)
        return FX(str(v) if v >= 0 else '(%d)' % v, tg)

    def f_FLOATING_LITERAL(self, c):
        toks = [t.spelling for t in c.get_tokens()]
        tg = ctag(c.type)
        if len(toks) == 1 and re.fullmatch(r'(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?[fFlL]?', toks[0]):
            return FX(flit(toks[0], tg), tg)
        if len(toks) == 1 and self.macro_name(toks[0]):
            return FX(self.macro_name(toks[0]), tg)
        r = evaluate(c)
        return FX(flit(repr(r[1]), tg), tg)

    def f_CHARACTER_LITERAL(self, c):
        r = evaluate(c)
        return FX(str(r[1] if r else 0), 'i')

    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = self._give('lit_%d' % len(self.lits))
        return self.lits[b]

    def f_STRING_LITERAL(self, c):
        return FX(self.lit(self.string_bytes(c)), 'c', var=True)

    def is_ptr_decl(self, d):
        s, attrs, dims = self.spec(d.type, d=d)
        return 'pointer' in attrs

    def f_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return FX(c.spelling, '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums or d.spelling not in self.fenum:
                return FX(str(d.enum_value) if d.enum_value >= 0 else '(%d)' % d.enum_value, 'i')
            return FX(self.fenum[d.spelling], 'i')
        if d.kind == K.FUNCTION_DECL:
            n = self.func_ref(d, self.cur_file)
            if n is None:
                self.problem(c, 'function value %s' % d.spelling)
                return FX(d.spelling, 'fp')
            return FX(n, 'fp')
        if d.kind == K.VAR_DECL and d.spelling in ('stdout', 'stderr') and not self.F.in_src(d):
            return FX('c_stdout', 'file', var=True, ptr=True)
        tg = self.ftag(d.type)
        local = d.kind == K.PARM_DECL or (d.kind == K.VAR_DECL and d.semantic_parent is not None and
                                          d.semantic_parent.kind == K.FUNCTION_DECL and
                                          d.storage_class != front.ci.StorageClass.STATIC and
                                          d.storage_class != front.ci.StorageClass.EXTERN)
        if local:
            name = self.local_name(d)
        elif d.kind == K.VAR_DECL and d.semantic_parent is not None and d.semantic_parent.kind == K.FUNCTION_DECL and \
                d.storage_class == front.ci.StorageClass.STATIC:
            name = self.static_local_name(d)
        else:
            k = self.global_key(d)
            name = self.fgname[k] if k else d.spelling
        if tg == 'o' and ptr_category(d.type) == 'scalar' and self.P.mode_of(d) == 'ref' and d.kind == K.PARM_DECL:
            return FX(name, 'ref', var=True)
        if tg == 'fp' and d.kind == K.PARM_DECL:
            return FX(name, 'fp', var=True, ptr=False)
        return FX(name, tg, var=True, ptr=self.is_ptr_decl(d) if tg in ('o', 'file', 'fp') else False)

    def f_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        if e.tag in NUMTAGS or e.tag == 'b':
            return FX('(%s)' % e.code if not e.code.startswith('(') or not self._balanced(e.code[1:-1]) else e.code, e.tag)
        return e

    def f_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if not ch:
            z = self.zero_value(c.type)
            return FX(z, ctag(c.type)) if z else FX(self.null_of(c.type), 'n')
        if len(ch) != 1:
            self.problem(c, 'unexposed with %d children' % len(ch))
        x = ch[0]
        src, dst = x.type, c.type
        st, dt = self.ftag(src), self.ftag(dst)
        if canon(src).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return self.ex(x)
        e = self.ex(x)
        if st == 'carr' and dt == 'c':
            if e.tag == 'c':
                return e
            return FX('cview(%s)' % e.code, 'c')
        if st == 'arr' and dt == 'o':
            return FX(e.code, 'o', var=True)
        return self.conv(e, src, dst)

    def f_CSTYLE_CAST_EXPR(self, c):
        inner = kids(c)[-1]
        if ctag(c.type) == 'v':
            return self.ex(inner)
        s = strip(inner)
        if s.kind == K.CALL_EXPR and s.spelling in ('malloc', 'calloc', 'realloc'):
            self.problem(c, 'allocation outside an assignment')
            return FX('null()', 'n')
        e = self.ex(inner)
        dt = self.ftag(c.type)
        if e.tag == 'n' or (dt in ('o', 'c', 'file', 'vp', 'fp') and self.is_int_lit(e.code) and e.tag in NUMTAGS):
            return FX(self.null_of(c.type), 'n')
        if dt == 'o' and self.ftag(inner.type) == 'vp':
            # (T*) voidptr: give the address a typed pointer
            s_, attrs, dims = self.spec(c.type, mode='obj')
            t = self.temp('%s, pointer' % s_, 'p')
            self.pre.append('call c_f_pointer(%s, %s)' % (e.code, t))
            return FX(t, 'o', var=True, ptr=True)
        if dt in ('o', 'c', 'file', 'vp', 'fp'):
            return e
        return self.conv(e, inner.type, c.type)

    def f_CXX_UNARY_EXPR(self, c):
        r = evaluate(c)
        return FX('%d_int64' % (r[1] if r else 8), 'ul')

    # --- operators
    def f_UNARY_OPERATOR(self, c):
        op = unop(c)
        a = kids(c)[0]
        if op == '&':
            return self.addr_of(a)
        if op == '*':
            return self.deref(a)
        if op == '!':
            return FX('(.not. %s)' % self.cond(a), 'b')
        if op in ('pre++', 'pre--', 'post++', 'post--'):
            lv = self.lvalue(a)
            tg = self.ftag(a.type)
            if op.startswith('post'):
                t = self.temp(self.decl_line('', a.type, mode='obj').split(' ::')[0], 'v')
                self.pre.append('%s = %s' % (t, lv))
                self.pre.extend(self.incdec_lines(a, '+' if '++' in op else '-'))
                return FX(t, tg, var=True)
            self.pre.extend(self.incdec_lines(a, '+' if '++' in op else '-'))
            return FX(lv, tg, var=True)
        e = self.val(a)
        if op == '-':
            if e.tag == 'u':
                return FX('i2u(-%s)' % e.code, 'u')
            return FX('(-%s)' % e.code, e.tag)
        if op == '+':
            return e
        if op == '~':
            if e.tag == 'u':
                return FX('iand(not(%s), MASK32)' % self.unparen(e.code), 'u')
            return FX('not(%s)' % self.unparen(e.code), e.tag)
        self.problem(c, 'unary ' + op)
        return e

    def array_designator(self, sa):
        """True if expression sa denotes a whole array (pointer used as array, or fixed array)"""
        sa = strip(sa)
        t = canon(sa.type)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            return True
        if sa.kind in (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR) and sa.referenced is not None:
            return self.P.mode_of(sa.referenced) == 'array'
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            # element of an array of pointers that is itself an array (jagged row)
            return ptr_category(t) == 'scalar' and canon(t).kind == T.POINTER and self.elem_is_row(sa)
        if sa.kind == K.CALL_EXPR:
            return False
        return False

    def elem_is_row(self, sa):
        base = kids(sa)[0]
        bt = canon(strip(base).type)
        return bt.kind in (T.POINTER, T.CONSTANTARRAY, T.INCOMPLETEARRAY) and ptr_category(bt) == 'ptrptr' or \
            (bt.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY) and canon(bt.element_type).kind == T.POINTER)

    def deref(self, a):
        sa = strip(a)
        cat = ptr_category(a.type)
        if cat == 'func':
            return self.ex(a)
        if cat == 'char':
            k = self.char_elem_parts_deref(a)
            return FX('cget(%s, 0)' % k, 'i')
        pt = canon(canon(a.type).get_pointee())
        if cat == 'record':
            e = self.ex(a)
            if self.array_designator(sa):
                return FX('%s(0)' % e.code, 'rec', var=True)
            return FX(e.code, 'rec', var=True)
        if cat == 'scalar':
            if sa.kind == K.BINARY_OPERATOR and binop(sa) in ('+', '-') and canon(sa.type).kind == T.POINTER:
                l, r = kids(sa)
                b = self.ex(l)
                i = self.val(r)
                ic = i.code if binop(sa) == '+' else '(-%s)' % i.code
                return FX('%s(%s)' % (b.code, self.unparen(ic)), self.ftag(pt), var=True)
            e = self.ex(a)
            if e.tag == 'ref':
                return FX(e.code, self.ftag(pt), var=True)
            return FX('%s(0)' % e.code, self.ftag(pt), var=True)
        if cat == 'ptrptr':
            e = self.ex(a)
            mode = self.mode_of_expr(sa)
            pt_tag = self.ftag(pt)
            if mode == 'ref':
                return FX(e.code, pt_tag, var=True, ptr=pt_tag != 'c')
            if pt_tag == 'c':
                return FX('%s(0)' % e.code, 'c', var=True)
            return FX('%s(0)%%p' % e.code, pt_tag, var=True, ptr=True)
        self.problem(a, 'deref of ' + str(cat))
        return self.ex(a)

    def char_elem_parts_deref(self, a):
        e = self.ex(a)
        return e.code

    def addr_of(self, a):
        sa = strip(a)
        if canon(sa.type).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
            return self.ex(sa)
        t = self.ftag(sa.type)
        if t == 'rec':
            e = self.ex(sa)
            return FX(e.code, 'o', var=True)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sa)
            if front.is_char(sa.type):
                kind, x, y = self.char_elem(sa)
                if kind == 'fixed':
                    arr, i = x, y
                    return FX('cadd(cview(%s), %s)' % (arr, i) if i != '0' else 'cview(%s)' % arr, 'c')
                return FX('cadd(%s, %s)' % (x, y) if y != '0' else x, 'c')
            e = self.ex(sa)
            if t in NUMTAGS:
                return FX(e.code, 'ref', var=True)
            if t == 'carr':
                return FX('cview(%s)' % e.code, 'c')
            if t == 'arr':
                return FX(e.code, 'o', var=True)
            return FX(e.code, 'refp', var=True, ptr=e.ptr)
        e = self.ex(sa)
        if t in NUMTAGS:
            return FX(e.code, 'refc' if front.is_char(sa.type) else 'ref', var=True)
        if t == 'carr':
            return FX('cview(%s)' % e.code, 'c')
        if t == 'arr':
            return FX(e.code, 'o', var=True)
        return FX(e.code, 'refp', var=True, ptr=e.ptr)

    FOPS = {'==': '==', '!=': '/=', '<': '<', '>': '>', '<=': '<=', '>=': '>='}

    def f_BINARY_OPERATOR(self, c):
        op = binop(c)
        l, r = kids(c)
        if op == '=':
            lines = self.assign_lines(l, r)
            self.pre.extend(lines)
            e = self.ex(l)
            return FX(e.code, e.tag, var=True, ptr=e.ptr)
        if op in ('&&', '||'):
            return self.logic(op, l, r)
        if op == ',':
            self.pre.extend(self.expr_stmt(l))
            return self.ex(r)
        if op in self.FOPS:
            le, re_ = self.val(l), self.val(r)
            ptags = ('c', 'o', 'n', 'file', 'vp', 'fp', 'ref', 'refp')
            if le.tag in ptags or re_.tag in ptags:
                return FX(self.ptr_compare(le, re_, op), 'b')
            return FX('(%s %s %s)' % (self.unparen(le.code) if le.code.startswith('(') and False else le.code, self.FOPS[op], re_.code), 'b')
        tg = ctag(c.type)
        lt, rt = canon(l.type), canon(r.type)
        if self.ftag(c.type) == 'c':
            le, re_ = self.val(l), self.val(r)
            if self.ftag(l.type) == 'c':
                return FX('cadd(%s, %s)' % (le.code, re_.code if op == '+' else '(-%s)' % re_.code), 'c')
            return FX('cadd(%s, %s)' % (re_.code, le.code), 'c')
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            return FX('cdiff(%s, %s)' % (self.val(l).code, self.val(r).code), 'l')
        if op in ('<<', '>>'):
            le = self.val(l)
            re_ = self.val(r)
            if op == '<<':
                code = 'ishft(%s, %s)' % (self.unparen(le.code), self.unparen(re_.code))
                if tg == 'u':
                    code = 'iand(%s, MASK32)' % code
            else:
                code = ('ishft(%s, -%s)' if tg in ('u', 'ul') else 'shifta(%s, %s)') % (self.unparen(le.code), self.paren(re_.code))
            return FX(code, tg)
        le = self.conv(self.val(l), l.type, c.type)
        re_ = self.conv(self.val(r), r.type, c.type)
        a, b = le.code, re_.code
        if op in ('+', '-', '*', '/'):
            code = '(%s %s %s)' % (a, op, b)
        elif op == '%':
            code = 'mod(%s, %s)' % (self.unparen(a), self.unparen(b))
        elif op == '&':
            code = 'iand(%s, %s)' % (self.unparen(a), self.unparen(b))
        elif op == '|':
            code = 'ior(%s, %s)' % (self.unparen(a), self.unparen(b))
        elif op == '^':
            code = 'ieor(%s, %s)' % (self.unparen(a), self.unparen(b))
        else:
            self.problem(c, 'binary ' + op)
            code = '(%s %s %s)' % (a, op, b)
        if tg == 'u' and op in ('+', '-', '*'):
            code = 'iand(%s, MASK32)' % code
        return FX(code, tg)

    def ptr_compare(self, le, re_, op):
        def isnull(e):
            return e.tag == 'n' or e.code in ('null()', 'cnull()', 'c_null_ptr')
        neg = op == '!='
        if op not in ('==', '!='):
            if le.tag == 'c' or re_.tag == 'c':
                return '(%s%%o %s %s%%o)' % (le.code, self.FOPS[op], re_.code)
            self.problem_noloc('relational compare of pointers %s %s %s' % (le.code, op, re_.code))
            return '.false.'
        if isnull(le) and isnull(re_):
            return '.false.' if neg else '.true.'
        if isnull(le) or isnull(re_):
            x = re_ if isnull(le) else le
            if x.tag == 'c':
                s = 'cisnull(%s)' % x.code
            elif x.tag == 'fp' and not x.ptr:
                s = '.false.'
            elif x.tag == 'vp':
                s = '(.not. c_associated(%s))' % x.code
            else:
                s = '(.not. associated(%s))' % x.code
            return '(.not. %s)' % s if neg else s
        if le.tag == 'c' or re_.tag == 'c':
            s = 'ceq(%s, %s)' % (le.code, re_.code)
        elif le.tag == 'vp' or re_.tag == 'vp':
            s = 'c_associated(%s, %s)' % (le.code, re_.code)
        else:
            p, q = (le, re_) if le.ptr or not re_.ptr else (re_, le)
            if q.ptr:
                s = '(associated(%s, %s) .or. (.not. associated(%s) .and. .not. associated(%s)))' % (p.code, q.code, p.code, q.code)
            else:
                s = 'associated(%s, %s)' % (p.code, q.code)
        return '(.not. %s)' % s if neg else s

    def problem_noloc(self, msg):
        self.problems.append('%s:%s %s' % (self.cur_file, getattr(self, 'cur_func', '?'), msg))

    def logic(self, op, l, r):
        lc = self.cond(l)
        rc, rpre = self.run(lambda: self.cond(r))
        fop = '.and.' if op == '&&' else '.or.'
        if not rpre and self.safe(r):
            return FX('(%s %s %s)' % (lc, fop, rc), 'b')
        t = self.temp('logical', 'b')
        self.pre.append('%s = %s' % (t, self.unparen(lc)))
        self.pre.append(('if (%s) then' if op == '&&' else 'if (.not. %s) then') % t)
        self.pre.extend(IND + x for x in rpre + ['%s = %s' % (t, self.unparen(rc))])
        self.pre.append('end if')
        return FX(t, 'b', var=True)

    MATHF = {'fabs', 'sqrt', 'floor', 'ceil', 'exp', 'log', 'log10', 'sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'pow'}

    def safe(self, c):
        """evaluating c cannot fault and has no side effects (so Fortran may evaluate it unconditionally)"""
        k = c.kind
        if k in (K.INTEGER_LITERAL, K.FLOATING_LITERAL, K.CHARACTER_LITERAL, K.STRING_LITERAL, K.DECL_REF_EXPR,
                 K.CXX_UNARY_EXPR):
            return True
        if k in (K.PAREN_EXPR, K.UNEXPOSED_EXPR):
            return all(self.safe(x) for x in kids(c))
        if k == K.CSTYLE_CAST_EXPR:
            inner = kids(c)[-1]
            if self.ftag(c.type) == 'o' and self.ftag(inner.type) == 'vp':
                return False
            return self.safe(inner)
        if k == K.UNARY_OPERATOR:
            op = unop(c)
            a = kids(c)[0]
            if op in ('-', '+', '!', '~'):
                return self.safe(a)
            if op == '&':
                sa = strip(a)
                return sa.kind in (K.DECL_REF_EXPR,) or (sa.kind == K.MEMBER_REF_EXPR and self.safe(sa))
            return False
        if k == K.BINARY_OPERATOR:
            op = binop(c)
            if op in ('=', ','):
                return False
            l, r = kids(c)
            if op in ('/', '%') and ctag(c.type) in ('i', 'u', 'l', 'ul'):
                v = evaluate(strip(r)) if strip(r).kind in (K.INTEGER_LITERAL, K.CHARACTER_LITERAL) else None
                if not v or v[1] == 0:
                    return False
            return self.safe(l) and self.safe(r)
        if k == K.CONDITIONAL_OPERATOR:
            return all(self.safe(x) for x in kids(c))
        if k == K.MEMBER_REF_EXPR:
            base = kids(c)[0]
            if canon(base.type).kind == T.POINTER:
                return False
            return self.safe(base)
        if k == K.CALL_EXPR:
            if c.spelling in self.MATHF and c.referenced is not None and not self.F.func_by_decl.get(c.spelling):
                return all(self.safe(a) for a in c.get_arguments())
            return False
        return False

    def f_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        l, r = kids(c)
        self.pre.extend(self.compound_lines(c))
        e = self.ex(l)
        return FX(e.code, e.tag, var=True)

    def f_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        tg = self.ftag(c.type)
        ccode = self.cond(cc)
        ea, pa = self.run(lambda: self.conv(self.val(a), a.type, c.type))
        eb, pb = self.run(lambda: self.conv(self.val(b), b.type, c.type))
        if tg == 'c':
            ea = FX('cnull()', 'c') if ea.tag == 'n' else ea
            eb = FX('cnull()', 'c') if eb.tag == 'n' else eb
        if tg in NUMTAGS or tg == 'c':
            if not pa and not pb and self.safe(a) and self.safe(b):
                return FX('merge(%s, %s, %s)' % (self.unparen(ea.code), self.unparen(eb.code), self.unparen(ccode)), tg)
            s_, attrs, dims = self.spec(c.type)
            t = self.temp(s_, 'v')
            self.pre.append('if (%s) then' % self.unparen(ccode))
            self.pre.extend(IND + x for x in pa + ['%s = %s' % (t, self.unparen(ea.code))])
            self.pre.append('else')
            self.pre.extend(IND + x for x in pb + ['%s = %s' % (t, self.unparen(eb.code))])
            self.pre.append('end if')
            return FX(t, tg, var=True)
        if tg in ('o', 'file', 'fp'):
            s_, attrs, dims = self.spec(c.type, mode='array' if self.array_designator(a) or self.array_designator(b) else 'obj')
            t = self.temp('%s, pointer%s' % (s_, '(:)' if dims == '(:)' else ''), 'p')
            def pa_line(e):
                return 'nullify(%s)' % t if e.tag == 'n' else '%s => %s' % (t, e.code)
            self.pre.append('if (%s) then' % self.unparen(ccode))
            self.pre.extend(IND + x for x in pa + [pa_line(ea)])
            self.pre.append('else')
            self.pre.extend(IND + x for x in pb + [pa_line(eb)])
            self.pre.append('end if')
            return FX(t, tg, var=True, ptr=True)
        self.problem(c, 'conditional of type ' + tg)
        return ea

    # --- element access
    def row_parts(self, sa):
        """sa = X[i] where X is a 2-D fixed array: (designator of X, code of i)"""
        base, idx = kids(sa)
        return self.ex(base).code, self.unparen(self.val(idx).code)

    def is_row(self, sa):
        sa = strip(sa)
        return sa.kind == K.ARRAY_SUBSCRIPT_EXPR and canon(sa.type).kind == T.CONSTANTARRAY

    def char_elem(self, sa):
        """sa = p[i] with char elements: ('fixed', designator, index) or ('ptr', cptr code, index)"""
        base, idx = kids(sa)
        i = self.unparen(self.val(idx).code)
        sb = strip(base)
        bt = canon(sb.type)
        if bt.kind == T.CONSTANTARRAY and front.is_char(bt.element_type):
            if self.is_row(sb):
                arr, row = self.row_parts(sb)
                return ('fixed2', arr, (i, row))
            return ('fixed', self.ex(sb).code, i)
        return ('ptr', self.ex(base).code, i)

    def f_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, idx = kids(c)
        et = canon(c.type)
        sb = strip(base)
        if front.is_char(et):
            kind, x, y = self.char_elem(c)
            if kind == 'fixed':
                return FX('int(%s(%s), int32)' % (x, y), 'i')
            if kind == 'fixed2':
                return FX('int(%s(%s, %s), int32)' % (x, y[0], y[1]), 'i')
            return FX('cget(%s, %s)' % (x, y), 'i')
        i = self.unparen(self.val(idx).code)
        if self.is_row(sb) and canon(sb.type).kind == T.CONSTANTARRAY:
            arr, row = self.row_parts(sb)
            return FX('%s(%s, %s)' % (arr, i, row), self.ftag(et), var=True)
        b = self.ex(base)
        tg = self.ftag(et)
        if b.tag == 'ref':
            return FX(b.code if i == '0' else '%s(%s)' % (b.code, i), tg, var=True)
        if et.kind == T.CONSTANTARRAY:
            # a row of a 2-D array used as an array: column section of the transposed Fortran array
            return FX('%s(:, %s)' % (b.code, i), tg, var=True)
        if et.kind == T.POINTER:
            cat = ptr_category(et)
            if cat == 'char':
                return FX('%s(%s)' % (b.code, i), 'c', var=True)
            if cat in ('record', 'scalar', 'ptrptr', 'file'):
                return FX('%s(%s)%%p' % (b.code, i), tg, var=True, ptr=True)
            return FX('%s(%s)' % (b.code, i), tg, var=True)
        if ptr_category(base.type) == 'record' and self.mode_of_expr(sb) == 'obj' and i == '0':
            return FX(b.code, 'rec', var=True)
        return FX('%s(%s)' % (b.code, i), 'rec' if et.kind == T.RECORD else tg, var=True)

    def f_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        sb = strip(base)
        f = c.referenced
        b = self.ex(base)
        if sb.kind == K.CALL_EXPR:
            # Fortran cannot select a component of a function result: hold it in a pointer first
            s_, attrs, dims = self.spec(sb.type, mode='obj')
            t = self.temp('%s, pointer' % s_, 'p')
            self.pre.append('%s => %s' % (t, b.code))
            b = FX(t, 'o', var=True, ptr=True)
        elif canon(base.type).kind == T.POINTER and self.array_designator(sb):
            b = FX('%s(0)' % b.code, 'rec', var=True)
        tg = self.ftag(c.type)
        ptr = False
        if tg in ('o', 'file', 'fp'):
            s_, attrs, dims = self.spec(f.type, d=f)
            ptr = 'pointer' in attrs
        return FX('%s%%%s' % (b.code, self.field(f)), tg, var=True, ptr=ptr)

    def f_INIT_LIST_EXPR(self, c):
        self.problem(c, 'initializer list outside a declaration')
        return FX('0', '?')

    def f_CALL_EXPR(self, c):
        code, rtag, is_sub, post, rptr = self.call_parts(c)
        if is_sub:
            self.problem(c, 'void call used as a value')
            return FX('0', '?')
        if post:
            s_, attrs, dims = self.result_spec(c)
            t = self.temp(s_, 'r')
            self.pre.append(('%s => %s' if rptr else '%s = %s') % (t, code))
            self.pre.extend(post)
            return FX(t, rtag, var=True, ptr=rptr)
        return FX(code, rtag, ptr=rptr)

    # ================================================================== calls
    def result_spec(self, c):
        """declaration spec for a temporary holding the result of call c"""
        t = canon(c.type)
        d = c.referenced
        mode = None
        if d is not None and d.kind == K.FUNCTION_DECL:
            fdef = self.func_def(d, self.cur_file)
            if fdef is not None:
                mode = self.ret_mode(fdef)
        s_, attrs, dims = self.spec(t, mode=mode or 'obj')
        attrs = [a for a in attrs if a != 'REF']
        return '%s%s%s' % (s_, ''.join(', ' + a for a in attrs), dims), attrs, dims

    def ret_mode(self, fdef):
        """'array' if the pointer a function returns is used as an array, else 'obj'"""
        k = ('ret', decl_key(fdef))
        if k not in self.addr_cache:
            mode = 'obj'
            t = canon(fdef.result_type)
            if t.kind == T.POINTER and ptr_category(t) in ('record', 'scalar', 'ptrptr'):
                for r in self.walk(fdef):
                    if r.kind == K.RETURN_STMT and kids(r):
                        if self.array_designator(kids(r)[0]):
                            mode = 'array'
                        rr = strip(kids(r)[0])
                        if rr.kind == K.CALL_EXPR and rr.spelling in ('calloc', 'malloc') and not front.alloc_count_is_one(rr):
                            mode = 'array'
                    if r.kind == K.CSTYLE_CAST_EXPR and strip(kids(r)[-1]).kind == K.CALL_EXPR and \
                            strip(kids(r)[-1]).spelling in ('calloc',) and not front.alloc_count_is_one(strip(kids(r)[-1])):
                        mode = 'array'
                if fdef.spelling == 'project_createMatrix':
                    mode = 'array'
            self.addr_cache[k] = mode
        return self.addr_cache[k]

    @staticmethod
    def walk(c):
        st = [c]
        while st:
            x = st.pop()
            yield x
            st.extend(x.get_children())

    def call_parts(self, c):
        """(code without CALL, result tag, is_subroutine, post lines, result is pointer)"""
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
            post = []
            codes = [self.arg(a, p, post) for a, p in zip(args, params)]
            rt = self.ftag(fdef.result_type)
            return '%s(%s)' % (n, ', '.join(codes)), rt, rt == 'v', post, rt in ('o', 'file', 'fp')
        # call through a function pointer
        fe = self.ex(callee)
        ft = canon(strip(callee).type)
        if ft.kind == T.POINTER:
            ft = canon(ft.get_pointee())
        rep = self.fp_rep(ft)
        post = []
        if rep is None:
            self.problem(c, 'no function bound to pointer type %s' % ft.spelling)
            codes = [self.val(a).code for a in args]
        else:
            codes = [self.arg(a, p, post) for a, p in zip(args, list(rep.get_arguments()))]
        rt = self.ftag(ft.get_result())
        return '%s(%s)' % (fe.code, ', '.join(codes)), rt, rt == 'v', post, rt in ('o', 'file')

    def fp_rep(self, ft):
        sp = canon(ft).spelling
        for fk in self.callback_groups:
            if canon(self.F.funcs[fk].type).spelling == sp:
                return self.F.funcs[fk]
        return None

    @staticmethod
    def pointee(t):
        t = canon(t)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            return canon(t.element_type)
        return canon(t.get_pointee())

    def param_kind(self, p):
        t = canon(p.type)
        if ctag(t) in NUMTAGS:
            return 'num'
        if t.kind == T.RECORD:
            return 'recval'
        cat = ptr_category(t)
        mode = self.P.mode_of(p)
        if cat == 'char':
            return 'cptr'
        if cat in ('file', 'func'):
            return {'file': 'file', 'func': 'fp'}[cat]
        if cat == 'void':
            return 'vp'
        if cat == 'record':
            return 'arr' if mode == 'array' else 'obj'
        if cat == 'scalar':
            return 'ref' if mode == 'ref' else 'arr'
        if cat == 'ptrptr':
            if self.pointee(t).kind == T.CONSTANTARRAY:
                return 'arr2'
            return 'ppref' if mode == 'ref' else 'pparr'
        return 'vp'

    def arg(self, a, p, post):
        """code for argument a passed to parameter p (of the callee's definition)"""
        kind = self.param_kind(p)
        sa = strip(a)
        while sa.kind == K.CSTYLE_CAST_EXPR and self.ftag(sa.type) in ('o', 'vp', 'c'):
            sa = strip(kids(sa)[-1])
        if kind == 'num':
            return self.unparen(self.conv(self.val(a), a.type, p.type).code)
        if kind == 'cptr':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&' and front.is_char(strip(kids(sa)[0]).type) and \
                    strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR:
                # &charVariable passed as char*: a two-byte buffer, copied back after the call
                lv = self.lvalue(kids(sa)[0])
                tb = self.temp('integer(int8), target', 'cb')
                self.decls[-1] = self.decls[-1] + '(0:1)'
                self.pre.append('%s = 0_int8' % tb)
                self.pre.append('%s(0) = c8(%s)' % (tb, lv))
                post.append('%s = int(%s(0), int32)' % (lv, tb))
                return 'cview(%s)' % tb
            e = self.val(a)
            if e.tag == 'n':
                return 'cnull()'
            return e.code
        if kind == 'recval':
            return self.ex(a).code
        if kind in ('obj', 'file'):
            e = self.ex(a)
            if e.tag == 'n' or self.is_null_cursor(sa):
                return 'null()'
            if kind == 'obj' and self.array_designator(sa) and e.tag != 'rec':
                return '%s(0)' % e.code
            return e.code
        if kind == 'arr':
            if self.is_null_cursor(sa):
                return 'null()'
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = strip(kids(sa)[0])
                if o.kind == K.ARRAY_SUBSCRIPT_EXPR and not self.is_row(o):
                    base, idx = kids(o)
                    b = self.ex(base).code
                    i = self.unparen(self.val(idx).code)
                    if i == '0':
                        return b
                    s_, attrs, dims = self.spec(p.type, mode='array')
                    t = self.temp('%s, pointer(:)' % s_, 'p')
                    self.pre.append('%s(0:) => %s(%s:)' % (t, b, i))
                    return t
                # &scalar where an array is expected: a one-element array, copied back after the call
                lv = self.lvalue(o)
                s_, attrs, dims = self.spec(self.pointee(p.type))
                t = self.temp('%s, target(0:0)' % s_, 'a')
                self.pre.append('%s(0) = %s' % (t, lv))
                post.append('%s = %s(0)' % (lv, t))
                return t
            e = self.ex(a)
            if e.tag == 'n':
                return 'null()'
            if re.search(r'\(:, [^()]*\)$', e.code) or re.search(r'\(:, .*\)$', e.code):
                s_, attrs, dims = self.spec(p.type, mode='array')
                t = self.temp('%s, pointer(:)' % s_, 'p')
                self.pre.append('%s(0:) => %s' % (t, e.code))
                return t
            return e.code
        if kind == 'ref':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return self.lvalue(kids(sa)[0])
            e = self.ex(a)
            if e.tag == 'ref':
                return e.code
            if self.is_null_cursor(sa) or e.tag == 'n':
                self.problem(a, 'NULL passed to reference parameter %s' % p.spelling)
                s_, attrs, dims = self.spec(self.pointee(p.type))
                return self.temp(s_, 'z')
            return '%s(0)' % e.code
        if kind == 'ppref':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return self.lvalue(kids(sa)[0])
            e = self.ex(a)
            return e.code
        if kind == 'pparr':
            e = self.ex(a)
            if e.tag == 'n' or self.is_null_cursor(sa):
                return 'null()'
            return e.code
        if kind == 'arr2':
            return self.ex(a).code
        if kind == 'vp':
            if self.is_null_cursor(sa):
                return 'c_null_ptr'
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                return 'c_loc(%s)' % self.lvalue(kids(sa)[0])
            e = self.ex(sa)
            if e.tag == 'vp':
                return e.code
            if e.tag == 'n':
                return 'c_null_ptr'
            return 'c_loc(%s)' % e.code
        if kind == 'fp':
            return self.ex(a).code
        self.problem(a, 'argument kind ' + kind)
        return self.val(a).code

    def is_null_cursor(self, sa):
        sa = strip(sa)
        while sa.kind == K.CSTYLE_CAST_EXPR:
            sa = strip(kids(sa)[-1])
        if sa.kind in (K.INTEGER_LITERAL,):
            v = evaluate(sa)
            return v is not None and v[1] == 0
        if sa.kind == K.GNU_NULL_EXPR if hasattr(K, 'GNU_NULL_EXPR') else False:
            return True
        return False

    def lvalue(self, l):
        e = self.ex(l)
        return self.unparen(e.code) if e.tag in NUMTAGS else e.code

    # --- C library
    MATH = {'fabs': 'abs', 'sqrt': 'sqrt', 'exp': 'exp', 'log': 'log', 'log10': 'log10', 'sin': 'sin', 'cos': 'cos',
            'tan': 'tan', 'asin': 'asin', 'acos': 'acos', 'atan': 'atan', 'floor': 'cfloor', 'ceil': 'cceil'}

    def libc(self, c, name, args):
        A = lambda i: self.unparen(self.val(args[i]).code)
        tg = self.ftag(c.type)
        if name in self.MATH:
            return '%s(%s)' % (self.MATH[name], A(0)), 'd', False, [], False
        if name == 'pow':
            return '(%s ** %s)' % (self.fparen(self.val(args[0]).code), self.fparen(self.val(args[1]).code)), 'd', False, [], False
        if name in ('fprintf', 'snprintf', 'sprintf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sprintf': 2}[name]
            head = []
            for i in range(fixed):
                e = self.val(args[i])
                head.append('cnull()' if e.tag == 'n' and i != 0 else self.unparen(e.code))
            rest = [self.vararg(a) for a in args[fixed:]]
            if len(rest) > 20:
                self.problem(c, 'more than 20 printf arguments')
            if name == 'fprintf':
                return 'c_fprintf(%s)' % ', '.join(head + rest), 'i', True, [], False
            if name == 'sprintf':
                head = [head[0], '1000000_int64', head[1]]
            return 'c_snprintf(%s)' % ', '.join(head + rest), 'i', False, [], False
        if name == 'sscanf':
            head = [A(0), A(1)]
            rest = []
            for a in args[2:]:
                rest.append(self.scan_target(a))
            return 'c_sscanf(%s)' % ', '.join(head + rest), 'i', False, [], False
        if name == 'free':
            return None, 'v', True, [], False
        if name in ('calloc', 'malloc', 'realloc'):
            self.problem(c, 'allocation outside an assignment')
            return 'null()', 'o', False, [], True
        if name in ('fwrite', 'fread'):
            return self.freadwrite(c, name, args)
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return 'c_strtod_ep(%s, %s)' % (A(0), self.lvalue(kids(ep)[0])), 'd', False, [], False
            return 'c_atof(%s)' % A(0), 'd', False, [], False
        if name == 'time':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                lv = self.lvalue(kids(a0)[0])
                self.pre.append('%s = c_time()' % lv)
                return lv, 'l', False, [], False
            return 'c_time()', 'l', False, [], False
        if name == 'ctime':
            a0 = strip(args[0])
            if a0.kind == K.UNARY_OPERATOR and unop(a0) == '&':
                return 'c_ctime(%s)' % self.lvalue(kids(a0)[0]), 'c', False, [], False
            return 'c_ctime(%s)' % self.ex(args[0]).code, 'c', False, [], False
        if name == 'difftime':
            return 'real(%s - %s, dp)' % (self.fparen(A(0)), self.fparen(A(1))), 'd', False, [], False
        if name == 'memset':
            return self.memset(c, args)
        if name == 'fseeko':
            name = 'fseek'
        rt = {'strlen': 'ul', 'atoi': 'i', 'strcmp': 'i', 'feof': 'i', 'fclose': 'i', 'atof': 'd', 'ftell': 'l',
              'strcspn': 'ul', 'toupper': 'i', 'fseek': 'i', 'remove': 'i', 'fflush': 'i', 'mkstemp': 'i',
              'strcpy': 'c', 'strcat': 'c', 'strchr': 'c', 'strrchr': 'c', 'strstr': 'c', 'strtok': 'c', 'fgets': 'c',
              'fopen': 'file', 'rewind': 'v'}
        if name in rt:
            codes = []
            for i in range(len(args)):
                e = self.val(args[i])
                codes.append(('cnull()' if e.tag == 'n' and self.ftag(args[i].type) in ('c',) else
                              'null()' if e.tag == 'n' else self.unparen(e.code)))
            fn = 'strlen' if name == 'strlen' else 'c_' + name
            return '%s(%s)' % (fn, ', '.join(codes)), rt[name], rt[name] == 'v', [], rt[name] == 'file'
        self.problem(c, 'libc ' + name)
        return 'c_%s(%s)' % (name, ', '.join(A(i) for i in range(len(args)))), tg, False, [], False

    def fparen(self, s):
        if re.fullmatch(r'[\w%]+(\([^()]*\))?', s) or re.fullmatch(r'\d+(\.\d*)?(e[-+]?\d+)?_dp', s):
            return s
        if s.startswith('(') and s.endswith(')') and self._balanced(s[1:-1]):
            return s
        return '(%s)' % s

    def vararg(self, a):
        e = self.val(a)
        if e.tag == 'n':
            return 'cnull()'
        if e.tag == 'b':
            return self.b2num(e, 'i').code
        return self.unparen(e.code)

    def scan_target(self, a):
        """sscanf target: a variable (Fortran passes it by reference)"""
        sa = strip(a)
        if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
            o = strip(kids(sa)[0])
            return self.lvalue(o)
        e = self.ex(a)
        if e.tag == 'ref':
            return e.code
        if e.tag == 'c':
            if e.var:
                return e.code
            t = self.temp('type(CPtr)', 's')
            self.pre.append('%s = %s' % (t, e.code))
            return t
        self.problem(a, 'sscanf target ' + e.tag)
        return e.code

    def memset(self, c, args):
        dst = strip(args[0])
        while dst.kind == K.CSTYLE_CAST_EXPR:
            dst = strip(kids(dst)[-1])
        if dst.kind == K.UNARY_OPERATOR and unop(dst) == '&' and ctag(strip(kids(dst)[0]).type) == 'rec':
            o = strip(kids(dst)[0])
            self.pre.append('%s = %s' % (self.lvalue(o), self.zero_obj(o.type)))
            return None, 'v', True, [], False
        e = self.ex(args[0])
        et = canon(dst.type)
        if self.ftag(dst.type) == 'c':
            self.pre.append('call c_memset(%s, %s, %s)' % (e.code, self.unparen(self.val(args[1]).code),
                                                            self.unparen(self.val(args[2]).code)))
            return None, 'v', True, [], False
        pt = canon(et.get_pointee()) if et.kind == T.POINTER else canon(et.element_type)
        size = max(pt.get_size(), 1)
        n = self.unparen(self.val(args[2]).code)
        v = self.unparen(self.val(args[1]).code)
        if v != '0':
            self.problem(c, 'memset with nonzero value')
        z = self.zero_value(pt) or 'cnull()'
        self.pre.append('%s(0:int((%s) / %d) - 1) = %s' % (e.code, n, size, z))
        return None, 'v', True, [], False

    def freadwrite(self, c, name, args):
        buf, size, cnt, f = args
        fcode = self.unparen(self.val(f).code)
        sb = strip(buf)
        while sb.kind == K.CSTYLE_CAST_EXPR:
            sb = strip(kids(sb)[-1])
        kind = None
        if sb.kind == K.UNARY_OPERATOR and unop(sb) == '&':
            o = strip(kids(sb)[0])
            if o.kind == K.ARRAY_SUBSCRIPT_EXPR and not front.is_char(o.type):
                base, idx = kids(o)
                et = canon(o.type)
                target = self.ex(base).code
                ie = self.val(idx)
                off = self.unparen(ie.code) if ie.tag == 'i' else 'int(%s, int32)' % self.unparen(ie.code)
                kind = 'arr'
            elif front.is_char(o.type):
                kind = 'chr'
                target = self.addr_of(o).code
                et = canon(o.type)
            else:
                et = canon(o.type)
                kind = 'one'
                target = self.lvalue(o)
        else:
            e = self.ex(sb)
            bt = canon(sb.type)
            if e.tag == 'ref':
                et = canon(bt.get_pointee())
                kind = 'one'
                target = e.code
            elif e.tag == 'c' or (bt.kind in (T.CONSTANTARRAY,) and front.is_char(bt.element_type)):
                kind = 'chr'
                et = None
                target = e.code if e.tag == 'c' else 'cview(%s)' % e.code
            else:
                et = canon(bt.get_pointee()) if bt.kind == T.POINTER else canon(bt.element_type)
                kind = 'arr'
                target = e.code
                off = '0'
        sz = evaluate(strip(size))
        n = self.unparen(self.val(cnt).code)
        if kind == 'chr':
            nb = '%s * %s' % (self.fparen(self.unparen(self.val(size).code)), self.fparen(n))
            return 'c_%s_c(%s, int(%s, int64), %s)' % (name, target, nb, fcode), 'ul', False, [], False
        tn = {T.DOUBLE: 'r8', T.FLOAT: 'r4', T.INT: 'i4', T.LONG: 'i8', T.UINT: 'i4', T.ENUM: 'i4'}.get(et.kind)
        if tn is None:
            self.problem(c, '%s of %s' % (name, et.spelling))
            tn = 'xx'
        if kind == 'one':
            if sz and sz[0] == 'int' and sz[1] != max(et.get_size(), 1):
                return 'c_%s_lo(%s, %d, %s)' % (name, target, sz[1], fcode), 'ul', False, [], False
            return 'c_%s_%s(%s, %s)' % (name, tn, target, fcode), 'ul', False, [], False
        return 'c_%s_%sa(%s, %s, int(%s, int32), %s)' % (name, tn, target, off if kind == 'arr' else '0', n, fcode), 'ul', False, [], False

    # ================================================================== assignment
    def is_alloc(self, r):
        s = strip(r)
        while s.kind == K.CSTYLE_CAST_EXPR:
            s = strip(kids(s)[-1])
        return s if (s.kind == K.CALL_EXPR and s.spelling in ('malloc', 'calloc', 'realloc')) else None

    def alloc_lines(self, lhs, call, lt, lhs_cursor=None):
        args = list(call.get_arguments())
        lt = canon(lt)
        et = canon(lt.get_pointee())
        name = call.spelling
        if name == 'calloc':
            n = self.count_expr(args[0], args[1], et, mul=True)
        elif name == 'malloc':
            n = self.count_expr(args[0], None, et, mul=False)
        else:
            self.problem(call, 'realloc')
            n = self.count_expr(args[1], None, et, mul=False)
        tg = self.ftag(lt)
        if tg == 'c':
            return ['%s = cbuf(%s)' % (lhs, n)]
        mode = self.P.mode_of(lhs_cursor) if lhs_cursor is not None else None
        if et.kind == T.RECORD and (front.alloc_count_is_one(call) or mode == 'obj') and mode != 'array':
            return ['allocate(%s)' % lhs]
        lines = ['allocate(%s(0:%s - 1))' % (lhs, self.fparen(n))]
        if ctag(et) in NUMTAGS:
            lines.append('%s = %s' % (lhs, self.zero_value(et)))
        return lines

    def int_code(self, x):
        e = self.val(x)
        return self.unparen(e.code)

    def count_expr(self, a, b, et, mul):
        size = max(canon(et).get_size(), 1)
        def is_sizeof(x):
            return strip(x).kind == K.CXX_UNARY_EXPR
        if mul:
            if is_sizeof(b):
                return self.int_code(a)
            if is_sizeof(a):
                return self.int_code(b)
            return '(%s * %s) / %d' % (self.fparen(self.int_code(a)), self.fparen(self.int_code(b)), size)
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

    def assign_lines(self, l, r):
        """C assignment l = r as Fortran statements"""
        lt = canon(l.type)
        sl = strip(l)
        # char element on the left
        if front.is_char(lt) and (sl.kind == K.ARRAY_SUBSCRIPT_EXPR or (sl.kind == K.UNARY_OPERATOR and unop(sl) == '*')):
            v, pre = self.run(lambda: self.conv(self.val(r), r.type, l.type))
            return pre + self.char_store(sl, self.unparen(v.code))
        lref = sl.referenced if sl.kind in (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR) else None
        al = self.is_alloc(r)
        if al is not None:
            lhs, pre = self.run(lambda: self.ex(l))
            return pre + self.alloc_lines(lhs.code, al, lt, lref)
        (lhs, rhs), pre = self.run(lambda: (self.ex(l), self.rhs_for(l.type, r)))
        return pre + self.store(lhs, l.type, rhs)

    def rhs_for(self, lt, r):
        tg = self.ftag(lt)
        if tg in NUMTAGS:
            e = self.conv(self.val(r), r.type, lt)
            if canon(lt).kind in (T.CHAR_S, T.SCHAR) and not front.is_char(r.type) and not self.is_int_lit(e.code):
                e = FX('int(c8(%s), int32)' % self.unparen(e.code), 'i')
            return e
        if tg == 'rec':
            return self.ex(r)
        e = self.val(r)
        if tg == 'c' and e.tag == 'n':
            return FX('cnull()', 'n')
        return e

    def store(self, lhs, lt, rhs):
        tg = self.ftag(lt)
        lc = self.unparen(lhs.code) if lhs.tag in NUMTAGS else lhs.code
        if tg in NUMTAGS or tg in ('c', 'rec'):
            if tg == 'c' and rhs.tag == 'n':
                return ['%s = cnull()' % lc]
            return ['%s = %s' % (lc, self.unparen(rhs.code))]
        if tg == 'vp':
            if rhs.tag == 'n':
                return ['%s = c_null_ptr' % lc]
            if rhs.tag == 'vp':
                return ['%s = %s' % (lc, rhs.code)]
            return ['%s = c_loc(%s)' % (lc, rhs.code)]
        if tg in ('o', 'file', 'fp'):
            if rhs.tag == 'n' or rhs.code == 'null()':
                return ['nullify(%s)' % lc]
            if rhs.tag == 'ref':
                return ['%s => %s' % (lc, rhs.code)]
            return ['%s => %s' % (lc, rhs.code)]
        if tg == 'carr':
            self.problem_noloc('assignment to char array %s' % lc)
        return ['%s = %s' % (lc, rhs.code)]

    def char_store(self, sl, v):
        """store char value code v into the char lvalue sl (p[i] or *p)"""
        if sl.kind == K.UNARY_OPERATOR:
            p = self.ex(kids(sl)[0]).code
            return ['call cset(%s, 0, %s)' % (p, v)]
        kind, x, y = self.char_elem(sl)
        if kind == 'fixed':
            return ['%s(%s) = c8(%s)' % (x, y, v)]
        if kind == 'fixed2':
            return ['%s(%s, %s) = c8(%s)' % (x, y[0], y[1], v)]
        return ['call cset(%s, %s, %s)' % (x, y, v)]

    def compound_lines(self, c):
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        sl = strip(l)
        if front.is_char(l.type) and sl.kind == K.ARRAY_SUBSCRIPT_EXPR:
            self.problem(c, 'compound assignment to char element')
        (lhs, re_), pre = self.run(lambda: (self.ex(l), self.val(r)))
        lc = self.unparen(lhs.code)
        if self.ftag(l.type) == 'c':
            n = self.unparen(re_.code)
            return pre + ['%s%%o = %s%%o %s %s' % (lc, lc, op, n if self.is_int_lit(n) or re_.tag == 'i' else 'int(%s, int32)' % n)]
        cur = FX(lc, lt)
        if rt in ('d', 'f') and lt not in ('d', 'f') or (rt == 'd' and lt == 'f'):
            common = rt
        elif lt in ('d', 'f'):
            common = lt
        elif lt in ('l', 'ul') or rt in ('l', 'ul'):
            common = 'l' if 'ul' not in (lt, rt) else 'ul'
        elif lt == 'u' or rt == 'u':
            common = 'u'
        else:
            common = 'i'
        ctype = {'d': 'double', 'f': 'float'}
        a = self.conv_tag(cur, common)
        b = self.conv_tag(re_, common)
        if op in ('+', '-', '*', '/'):
            v = '(%s %s %s)' % (a.code, op, b.code)
        elif op == '%':
            v = 'mod(%s, %s)' % (a.code, b.code)
        elif op == '&':
            v = 'iand(%s, %s)' % (a.code, b.code)
        elif op == '|':
            v = 'ior(%s, %s)' % (a.code, b.code)
        elif op == '^':
            v = 'ieor(%s, %s)' % (a.code, b.code)
        elif op == '<<':
            v = 'ishft(%s, %s)' % (a.code, b.code)
        elif op == '>>':
            v = 'shifta(%s, %s)' % (a.code, b.code)
        else:
            self.problem(c, 'compound ' + op)
            v = a.code
        if common == 'u' and op in ('+', '-', '*', '<<'):
            v = 'iand(%s, MASK32)' % v
        res = self.conv_tag(FX(v, common), lt)
        return pre + ['%s = %s' % (lc, self.unparen(res.code))]

    def conv_tag(self, e, d):
        """conversion between tags (no C type at hand)"""
        s = e.tag
        if s == d:
            return e
        return self._conv_tags(e, s, d)

    def _conv_tags(self, e, s, d):
        c = self.unparen(e.code)
        if d == 'i':
            return FX({'d': 'd2i(%s)', 'f': 'f2i(%s)', 'u': 'u2i(%s)', 'l': 'int(%s, int32)', 'ul': 'int(%s, int32)'}[s] % c, 'i')
        if d in ('l', 'ul'):
            return FX({'d': 'd2l(%s)', 'f': 'd2l(real(%s, dp))', 'i': 'int(%s, int64)', 'u': '%s', 'l': '%s', 'ul': '%s'}[s] % c, d)
        if d == 'u':
            return FX({'d': 'i2u(d2l(%s))', 'f': 'i2u(d2l(real(%s, dp)))', 'i': 'i2u(int(%s, int64))', 'l': 'i2u(%s)',
                       'ul': 'i2u(%s)'}[s] % c, 'u')
        if d == 'd':
            return FX('real(%s, dp)' % c, 'd')
        if d == 'f':
            return FX('real(%s, sp)' % c, 'f')
        return e

    def incdec_lines(self, a, sign):
        sa = strip(a)
        tg = self.ftag(a.type)
        if front.is_char(a.type) and sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            v = self.ex(sa).code
            return self.char_store(sa, '%s %s 1' % (v, sign))
        lv = self.lvalue(a)
        if tg == 'c':
            return ['%s%%o = %s%%o %s 1' % (lv, lv, sign)]
        one = {'i': '1', 'l': '1_int64', 'ul': '1_int64', 'u': '1_int64', 'd': '1.0_dp', 'f': '1.0_sp'}.get(tg)
        if one is None:
            self.problem(a, '++ on ' + tg)
            return []
        if tg == 'u':
            return ['%s = iand(%s %s 1_int64, MASK32)' % (lv, lv, sign)]
        return ['%s = %s %s %s' % (lv, lv, sign, one)]

    # ================================================================== statements
    @staticmethod
    def ind(lines):
        return [IND + l for l in lines]

    def stmt(self, c):
        k = c.kind
        if k == K.COMPOUND_STMT:
            out = []
            for ch in kids(c):
                out += self.stmt(ch)
            return out
        if k == K.DECL_STMT:
            out = []
            for d in kids(c):
                out += self.local_decl(d)
            return out
        if k == K.IF_STMT:
            return self.if_stmt(c)
        if k == K.WHILE_STMT:
            return self.while_stmt(c)
        if k == K.DO_STMT:
            return self.do_stmt(c)
        if k == K.FOR_STMT:
            return self.for_stmt(c)
        if k == K.SWITCH_STMT:
            return self.switch(c)
        if k == K.BREAK_STMT:
            ctx = self.ctx[-1] if self.ctx else None
            if ctx is None:
                self.problem(c, 'break outside loop')
                return []
            if ctx.kind == 'switch':
                ctx.used = True
                return ['goto %d' % ctx.label]
            return ['exit']
        if k == K.CONTINUE_STMT:
            loops = [x for x in self.ctx if x.kind != 'switch']
            if not loops:
                self.problem(c, 'continue outside loop')
                return []
            lp = loops[-1]
            if lp.kind == 'while' or (lp.kind == 'for' and lp.plain_cycle):
                return ['cycle']
            lp.used = True
            return ['goto %d' % lp.label]
        if k == K.RETURN_STMT:
            return self.return_stmt(c)
        if k == K.NULL_STMT:
            return []
        if k in (K.CASE_STMT, K.DEFAULT_STMT, K.LABEL_STMT, K.GOTO_STMT):
            self.problem(c, 'unsupported statement ' + k.name)
            return []
        return self.expr_stmt(c)

    def is_true_const(self, c):
        s = strip(c)
        if s.kind == K.INTEGER_LITERAL:
            v = evaluate(s)
            return v is not None and v[1] != 0
        return False

    def if_stmt(self, c):
        ch = kids(c)
        cc, pre = self.run(lambda: self.cond(ch[0]))
        out = pre + ['if (%s) then' % self.unparen(cc)] + self.ind(self.stmt(ch[1]))
        els = ch[2] if len(ch) > 2 else None
        while els is not None:
            if els.kind == K.IF_STMT:
                ec = kids(els)
                cc2, pre2 = self.run(lambda: self.cond(ec[0]))
                if not pre2:
                    out.append('else if (%s) then' % self.unparen(cc2))
                    out += self.ind(self.stmt(ec[1]))
                    els = ec[2] if len(ec) > 2 else None
                    continue
            out.append('else')
            out += self.ind(self.stmt(els))
            break
        out.append('end if')
        return out

    def while_stmt(self, c):
        ch = kids(c)
        cc, pre = self.run(lambda: self.cond(ch[0]))
        ctx = Ctx('while')
        self.ctx.append(ctx)
        body = self.stmt(ch[1])
        self.ctx.pop()
        if self.is_true_const(ch[0]):
            return ['do'] + self.ind(body) + ['end do']
        if not pre:
            return ['do while (%s)' % self.unparen(cc)] + self.ind(body) + ['end do']
        return ['do'] + self.ind(pre + ['if (.not. %s) exit' % self.fparen(cc)]) + self.ind(body) + ['end do']

    def do_stmt(self, c):
        ch = kids(c)
        ctx = Ctx('do', self.label())
        self.ctx.append(ctx)
        body = self.stmt(ch[0])
        self.ctx.pop()
        cc, pre = self.run(lambda: self.cond(ch[1]))
        out = ['do'] + self.ind(body)
        if ctx.used:
            out.append(IND + '%d continue' % ctx.label)
        out += self.ind(pre + ['if (.not. %s) exit' % self.fparen(cc)]) + ['end do']
        return out

    def for_parts(self, c):
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
            if o < semis[0]:
                init = x
            elif o < semis[1]:
                cond = x
            else:
                inc = x
        return init, cond, inc, body

    def for_stmt(self, c):
        init, cond, inc, body = self.for_parts(c)
        out = []
        if init is not None:
            if init.kind == K.DECL_STMT:
                for d in kids(init):
                    out += self.local_decl(d)
            else:
                out += self.expr_stmt(init)
        if cond is not None:
            cc, pre = self.run(lambda: self.cond(cond))
        else:
            cc, pre = None, []
        inc_lines = self.expr_stmt(inc) if inc is not None else []
        ctx = Ctx('for', self.label())
        ctx.plain_cycle = not inc_lines and (cond is None or not pre or True)
        self.ctx.append(ctx)
        b = self.stmt(body)
        self.ctx.pop()
        if cond is None or self.is_true_const(cond):
            head, condl = ['do'], []
        elif not pre:
            head, condl = ['do while (%s)' % self.unparen(cc)], []
        else:
            head, condl = ['do'], self.ind(pre + ['if (.not. %s) exit' % self.fparen(cc)])
        out += head + condl + self.ind(b)
        if ctx.used:
            out.append(IND + '%d continue' % ctx.label)
        out += self.ind(inc_lines) + ['end do']
        return out

    def switch(self, c):
        ch = kids(c)
        sel, pre = self.run(lambda: self.val(ch[0]))
        selcode = self.unparen(sel.code)
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
                        v = evaluate(xc[0])
                        labels.append(str(v[1]) if v is not None and v[0] == 'int' else self.unparen(self.val(xc[0]).code))
                        x = xc[1]
                    else:
                        labels.append('default')
                        x = xc[0]
                if sections and not sections[-1][1]:
                    sections[-1][0].extend(labels)
                else:
                    sections.append([labels, []])
                sections[-1][1].append(x)
            elif sections:
                sections[-1][1].append(it)
        ctx = Ctx('switch', self.label())
        self.ctx.append(ctx)
        clean = all(self.terminates(stmts) for _, stmts in sections[:-1])

        def case_line(labels):
            if 'default' in labels:
                return 'case default'
            return 'case (%s)' % ', '.join(l if not l.startswith('(') else self.unparen(l) for l in labels)
        out = pre + ['select case (%s)' % selcode]
        if clean:
            for labels, stmts in sections:
                out.append(case_line(labels))
                st = stmts[:-1] if stmts and stmts[-1].kind == K.BREAK_STMT else stmts
                lines = []
                for s in st:
                    lines += self.stmt(s)
                out += self.ind(lines)
            out.append('end select')
        else:
            labs = [self.label() for _ in sections]
            for (labels, stmts), L in zip(sections, labs):
                out.append(case_line(labels))
                out.append(IND + 'goto %d' % L)
            out.append('end select')
            if not any('default' in ls for ls, _ in sections):
                out.append('goto %d' % ctx.label)
                ctx.used = True
            for (labels, stmts), L in zip(sections, labs):
                out.append('%d continue' % L)
                for s in stmts:
                    out += self.stmt(s)
        self.ctx.pop()
        if ctx.used:
            out.append('%d continue' % ctx.label)
        return out

    def return_stmt(self, c):
        ch = kids(c)
        if not ch:
            return ['return']
        if self.is_sub:
            return self.expr_stmt(ch[0]) + ['return']
        rt = self.ftag(self.cur_ret)
        al = self.is_alloc(ch[0])
        if al is not None:
            return self.alloc_lines('res_', al, self.cur_ret) + ['return']
        e, pre = self.run(lambda: self.rhs_for(self.cur_ret, ch[0]))
        return pre + self.store(FX('res_', rt, var=True, ptr=True), self.cur_ret, e) + ['return']

    def expr_stmt(self, c):
        s = c
        while s.kind in (K.PAREN_EXPR, K.UNEXPOSED_EXPR) and len(kids(s)) == 1:
            s = kids(s)[0]
        if s.kind == K.CSTYLE_CAST_EXPR and ctag(s.type) == 'v':
            return self.expr_stmt(kids(s)[-1])
        k = s.kind
        if k == K.BINARY_OPERATOR:
            op = binop(s)
            l, r = kids(s)
            if op == '=':
                return self.assign_lines(l, r)
            if op == ',':
                return self.expr_stmt(l) + self.expr_stmt(r)
            if op in ('&&', '||'):
                lc, pre = self.run(lambda: self.cond(l))
                rl = self.expr_stmt(r)
                return pre + [('if (%s) then' if op == '&&' else 'if (.not. %s) then') % self.fparen(lc)] + self.ind(rl) + ['end if']
        if k == K.COMPOUND_ASSIGNMENT_OPERATOR:
            return self.compound_lines(s)
        if k == K.UNARY_OPERATOR and unop(s) in ('pre++', 'pre--', 'post++', 'post--'):
            lines, pre = self.run(lambda: self.incdec_lines(kids(s)[0], '+' if '++' in unop(s) else '-'))
            return pre + lines
        if k == K.CALL_EXPR:
            return self.call_stmt(s)
        if k == K.CONDITIONAL_OPERATOR:
            cc, a, b = kids(s)
            ccode, pre = self.run(lambda: self.cond(cc))
            return pre + ['if (%s) then' % self.unparen(ccode)] + self.ind(self.expr_stmt(a)) + ['else'] + \
                self.ind(self.expr_stmt(b)) + ['end if']
        e, pre = self.run(lambda: self.ex(s))
        return pre

    def call_stmt(self, c):
        (code, rtag, is_sub, post, rptr), pre = self.run(lambda: self.call_parts(c))
        d = c.referenced
        is_libc = d is not None and self.func_def(d, self.cur_file) is None
        if code is None:
            if c.spelling == 'free':
                return pre + ['! ' + ' '.join(t.spelling for t in c.get_tokens()).replace(' ( ', '(').replace(' )', ')')]
            return pre + post
        if is_libc and c.spelling == 'time':
            return pre
        if is_sub:
            return pre + ['call %s' % code] + post
        s_, attrs, dims = self.result_spec(c)
        dn = self.dums.get(s_)
        if dn is None:
            dn = self.temp(s_, 'dum')
            self.dums[s_] = dn
        return pre + [('%s => %s' if rptr else '%s = %s') % (dn, code)] + post

    # ================================================================== declarations
    def init_cursor(self, d):
        """the initializer expression of a variable declaration (not an array-size expression)"""
        k = decl_key(d)
        if k in self.init_cache:
            return self.init_cache[k]
        eq = None
        depth = 0
        for t in d.get_tokens():
            sp = t.spelling
            if sp in ('[', '('):
                depth += 1
            elif sp in (']', ')'):
                depth -= 1
            elif sp == '=' and depth == 0:
                eq = t.extent.start.offset
                break
        r = None
        if eq is not None:
            ch = [x for x in kids(d) if x.kind.is_expression() and x.extent.start.offset > eq]
            r = ch[-1] if ch else None
        self.init_cache[k] = r
        return r

    def local_decl(self, d):
        if d.kind != K.VAR_DECL:
            return []
        if d.storage_class == front.ci.StorageClass.EXTERN:
            return []
        if d.storage_class == front.ci.StorageClass.STATIC:
            self.static_locals.append((d, self.cur_file))
            self.static_local_name(d)
            return []
        nm = self.declare_local(d)
        tg = self.ftag(d.type)
        extra = ['target'] if (tg in ('rec', 'arr', 'carr') or decl_key(d) in self.addr_taken) else []
        self.decls.append(self.decl_line(nm, d.type, d=d, extra=extra, dims_override=self.sentinel_dims(d)))
        return self.init_value(nm, d, self.init_cursor(d))

    def sentinel_dims(self, d):
        """char* table whose initializer fills it with literals and no NULL: C's findmatch() reads one past
        the end; EPA's build finds a zero word there, so the table gets the NULL the C source forgot"""
        t = canon(d.type)
        init = self.init_cursor(d)
        if t.kind != T.CONSTANTARRAY or init is None or strip(init).kind != K.INIT_LIST_EXPR:
            return None
        et = canon(t.element_type)
        items = kids(strip(init))
        if et.kind == T.POINTER and front.is_char(et.get_pointee()) and items and \
                strip(items[-1]).kind == K.STRING_LITERAL and len(items) == t.element_count:
            if decl_key(d) not in self.sentinel_done:
                self.sentinel_done.add(decl_key(d))
                self.defects.append('%s:%d string table without NULL sentinel' % (os.path.basename(d.location.file.name), d.location.line))
            return '(0:%d)' % t.element_count
        return None

    def zero_lines(self, nm, t):
        t = canon(t)
        tg = self.ftag(t)
        if tg in NUMTAGS:
            return ['%s = %s' % (nm, self.zero_value(t))]
        if tg == 'c':
            return ['%s = cnull()' % nm]
        if tg == 'vp':
            return ['%s = c_null_ptr' % nm]
        if tg in ('o', 'file', 'fp'):
            return ['nullify(%s)' % nm]
        if tg == 'rec':
            return ['%s = %s' % (nm, self.zero_obj(t))]
        if tg == 'carr':
            return ['%s = 0_int8' % nm]
        if tg == 'arr':
            et = canon(t.element_type)
            while et.kind == T.CONSTANTARRAY:
                et = canon(et.element_type)
            if ctag(et) in NUMTAGS:
                return ['%s = %s' % (nm, self.zero_value(et))]
            if et.kind == T.RECORD:
                return ['%s = %s' % (nm, self.zero_obj(et))]
            et_tag = self.ftag(et)
            if et_tag == 'c':
                return ['%s = cnull()' % nm]
            w = self.elem_ptr_type(et)
            return ['%s = %s()' % (nm, w[5:-1])]
        return []

    def init_value(self, nm, d, init):
        t = canon(d.type)
        tg = self.ftag(t)
        if init is None:
            return self.zero_lines(nm, t)
        si = strip(init)
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if si.kind == K.INIT_LIST_EXPR:
                return self.zero_lines(nm, t) + self.init_list_lines(nm, t, si)
            if si.kind == K.STRING_LITERAL and tg == 'carr':
                return ['call cinit(%s, %s)' % (nm, self.lit(self.string_bytes(si)))]
            self.problem(d, 'array initializer')
            return self.zero_lines(nm, t)
        if tg == 'rec':
            if si.kind == K.INIT_LIST_EXPR:
                return self.zero_lines(nm, t) + self.record_init_lines(nm, t, si)
            e, pre = self.run(lambda: self.ex(init))
            return pre + ['%s = %s' % (nm, e.code)]
        al = self.is_alloc(init)
        if al is not None:
            return self.alloc_lines(nm, al, t, d)
        rhs, pre = self.run(lambda: self.rhs_for(d.type, init))
        s_, attrs, dims = self.spec(d.type, d=d)
        return pre + self.store(FX(nm, tg, var=True, ptr='pointer' in attrs), d.type, rhs)

    def item_value(self, it, et):
        """code for one initializer item of element type et"""
        si = strip(it)
        tg = self.ftag(et)
        if tg == 'c':
            if si.kind == K.STRING_LITERAL:
                return self.lit(self.string_bytes(si))
            e = self.val(it)
            return 'cnull()' if e.tag == 'n' or self.is_null_cursor(si) else e.code
        e = self.conv(self.val(it), it.type, et)
        return self.unparen(e.code)

    def init_list_lines(self, nm, t, il):
        t = canon(t)
        et = canon(t.element_type)
        items = kids(il)
        lines = []
        tg = self.ftag(et)
        if et.kind == T.CONSTANTARRAY and not front.is_char(et.element_type):
            inner = canon(et.element_type)
            for i, row in enumerate(items):
                sr = strip(row)
                if sr.kind != K.INIT_LIST_EXPR:
                    self.problem(il, '2-D initializer row')
                    continue
                vals = [self.item_value(x, inner) for x in kids(sr)]
                lines += self.chunked('%s(%%d:%%d, %d)' % (nm, i), vals)
            return lines
        if tg == 'carr':
            for i, it in enumerate(items):
                si = strip(it)
                if si.kind == K.STRING_LITERAL:
                    lines.append('call cinit(%s(:, %d), %s)' % (nm, i, self.lit(self.string_bytes(si))))
            return lines
        if et.kind == T.RECORD:
            for i, it in enumerate(items):
                si = strip(it)
                if si.kind == K.INIT_LIST_EXPR:
                    lines += self.record_init_lines('%s(%d)' % (nm, i), et, si)
                else:
                    lines.append('%s(%d) = %s' % (nm, i, self.ex(it).code))
            return lines
        if tg in NUMTAGS:
            vals = [self.item_value(x, et) for x in items]
            return self.chunked('%s(%%d:%%d)' % nm, vals)
        if tg == 'c':
            return ['%s(%d) = %s' % (nm, i, self.item_value(x, et)) for i, x in enumerate(items)]
        for i, it in enumerate(items):
            e = self.val(it)
            if e.tag == 'n' or self.is_null_cursor(strip(it)):
                continue
            lines.append('%s(%d)%%p => %s' % (nm, i, e.code))
        return lines

    @staticmethod
    def chunked(pattern, vals, size=8):
        lines = []
        for i in range(0, len(vals), size):
            part = vals[i:i + size]
            lines.append('%s = [%s]' % (pattern % (i, i + len(part) - 1), ', '.join(part)))
        return lines

    def record_init_lines(self, nm, t, il):
        fields = [f for f in canon(t).get_declaration().get_children() if f.kind == K.FIELD_DECL]
        lines = []
        for f, it in zip(fields, kids(il)):
            sub = '%s%%%s' % (nm, self.field(f))
            si = strip(it)
            ft = canon(f.type)
            if si.kind == K.INIT_LIST_EXPR:
                if ft.kind == T.RECORD:
                    lines += self.record_init_lines(sub, ft, si)
                else:
                    lines += self.init_list_lines(sub, ft, si)
            elif ft.kind == T.CONSTANTARRAY and front.is_char(ft.element_type) and si.kind == K.STRING_LITERAL:
                lines.append('call cinit(%s, %s)' % (sub, self.lit(self.string_bytes(si))))
            else:
                rhs = self.rhs_for(f.type, it)
                s_, attrs, dims = self.spec(f.type, d=f)
                lines += self.store(FX(sub, self.ftag(ft), var=True, ptr='pointer' in attrs), f.type, rhs)
        return lines

    # ================================================================== procedures
    def scan_function(self, c):
        """decl keys whose address is taken, and decl keys assigned, in function c"""
        addr, assigned = set(), set()
        for x in self.walk(c):
            if x.kind == K.UNARY_OPERATOR:
                op = unop(x)
                a = strip(kids(x)[0])
                if op == '&' and a.kind == K.DECL_REF_EXPR and a.referenced is not None:
                    addr.add(decl_key(a.referenced))
                if op in ('pre++', 'pre--', 'post++', 'post--') and a.kind == K.DECL_REF_EXPR and a.referenced is not None:
                    assigned.add(decl_key(a.referenced))
            elif x.kind == K.BINARY_OPERATOR and binop(x) == '=':
                a = strip(kids(x)[0])
                if a.kind == K.DECL_REF_EXPR and a.referenced is not None:
                    assigned.add(decl_key(a.referenced))
            elif x.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
                a = strip(kids(x)[0])
                if a.kind == K.DECL_REF_EXPR and a.referenced is not None:
                    assigned.add(decl_key(a.referenced))
        return addr, assigned

    def addr_info(self, key):
        if key not in self.addr_cache:
            self.addr_cache[key] = self.scan_function(self.F.funcs[key])
        return self.addr_cache[key]

    def param_addr(self, key, i):
        """address of parameter i taken in this function, or in any function bound to the same pointer type"""
        keys = self.callback_groups.get(key, [key])
        for k in keys:
            ps = list(self.F.funcs[k].get_arguments())
            if i < len(ps) and decl_key(ps[i]) in self.addr_info(k)[0]:
                return True
        return False

    def param_decl(self, prm, nm, kind, addr):
        """(dummy declaration, needs a local copy because C reassigns it)"""
        t = canon(prm.type)
        if kind == 'num':
            return '%s, value%s :: %s' % (self.scalar_type(t), ', target' if addr else '', nm)
        if kind == 'cptr':
            return 'type(CPtr), value :: %s' % nm
        if kind == 'recval':
            return 'type(%s), value%s :: %s' % (self.rec(t), ', target' if addr else '', nm)
        if kind == 'obj':
            return 'type(%s), pointer, intent(in) :: %s' % (self.rec(self.pointee(t)), nm)
        if kind == 'arr':
            e = self.pointee(t)
            s_ = 'type(%s)' % self.rec(e) if e.kind == T.RECORD else self.scalar_type(e)
            return '%s, pointer, intent(in) :: %s(:)' % (s_, nm)
        if kind == 'ref':
            return '%s, intent(inout), target :: %s' % (self.scalar_type(self.pointee(t)), nm)
        if kind == 'pparr':
            return '%s, pointer, intent(in) :: %s(:)' % (self.elem_ptr_type(self.pointee(t)), nm)
        if kind == 'arr2':
            row = self.pointee(t)
            return '%s, intent(inout), target :: %s(0:, 0:)' % (self.scalar_type(canon(row.element_type)), nm)
        if kind == 'ppref':
            e = self.pointee(t)
            s_, attrs, dims = self.spec(e, mode='obj' if ptr_category(e) == 'record' else 'array')
            if 'pointer' in attrs:
                return '%s, pointer :: %s%s' % (s_, nm, dims)
            return '%s, intent(inout) :: %s' % (s_, nm)
        if kind == 'file':
            return 'type(CFile), pointer, intent(in) :: %s' % nm
        if kind == 'vp':
            return 'type(c_ptr), value :: %s' % nm
        if kind == 'fp':
            return 'procedure(%s) :: %s' % (self.fp_name(t), nm)
        return 'type(c_ptr), value :: %s' % nm

    def result_decl(self, fdef):
        rt = canon(fdef.result_type)
        tg = self.ftag(rt)
        s_, attrs, dims = self.spec(rt, mode=self.ret_mode(fdef))
        attrs = [a for a in attrs if a != 'REF']
        decl = '%s%s :: res_%s' % (s_, ''.join(', ' + a for a in attrs), dims)
        if tg in NUMTAGS:
            init = 'res_ = %s' % self.zero_value(rt)
        elif tg == 'c':
            init = 'res_ = cnull()'
        elif tg == 'vp':
            init = 'res_ = c_null_ptr'
        elif tg == 'rec':
            init = 'res_ = %s' % self.zero_obj(rt)
        else:
            init = 'nullify(res_)'
        return decl, init

    def begin_proc(self, cur_file, name):
        self.cur_file = cur_file
        self.cur_func = name
        self.locals = {}
        self.local_taken = set()
        self.decls = []
        self.ntemp = 0
        self.nlabel = 99
        self.pre = []
        self.ctx = []
        self.dums = {}
        self.addr_taken = set()

    def function(self, key, c, header_only=False):
        b, n = key
        fname = self.ffname[key]
        self.begin_proc(b, fname)
        self.cur_ret = c.result_type
        self.addr_taken, assigned = self.addr_info(key)
        params = list(c.get_arguments())
        dummies, pdecls, entry = [], [], []
        for i, prm in enumerate(params):
            nm = self.declare_local(prm)
            kind = self.param_kind(prm)
            line = self.param_decl(prm, nm, kind, self.param_addr(key, i))
            if kind in ('obj', 'arr', 'pparr', 'file') and decl_key(prm) in assigned:
                dn = self.new_local(nm + '_in')
                pdecls.append(line.replace(':: %s' % nm, ':: %s' % dn, 1))
                local = line.replace(', intent(in)', '')
                self.decls.append(local)
                entry.append('%s => %s' % (nm, dn))
                dummies.append(dn)
            else:
                pdecls.append(line)
                dummies.append(nm)
        self.is_sub = self.ftag(c.result_type) == 'v'
        if header_only:
            rd = [] if self.is_sub else [self.result_decl(c)[0]]
            return dummies, pdecls + rd
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        lines = self.stmt(body)
        if self.is_sub:
            head = 'recursive subroutine %s(%s)' % (fname, ', '.join(dummies))
            tail = 'end subroutine %s' % fname
            rdecl, rinit = [], []
        else:
            head = 'recursive function %s(%s) result(res_)' % (fname, ', '.join(dummies))
            tail = 'end function %s' % fname
            d_, i_ = self.result_decl(c)
            rdecl, rinit = [d_], [i_]
        out = ['! %s:%d' % (b, c.location.line), head]
        out += self.ind(pdecls + rdecl + self.decls + entry + rinit + lines)
        out.append(tail)
        return out

    def interface(self, name, ft):
        """abstract interface for a function-pointer type, from a function bound to it"""
        rep = None
        for fk in self.callback_groups:
            if canon(self.F.funcs[fk].type).spelling == canon(ft).spelling:
                rep = fk
                break
        if rep is None:
            self.problems.append('no function bound to pointer type %s (%s)' % (name, ft.spelling))
            return []
        c = self.F.funcs[rep]
        dummies, decls = self.function(rep, c, header_only=True)
        sub = self.ftag(c.result_type) == 'v'
        ren = {d: 'a%d' % i for i, d in enumerate(dummies)}
        def rn(line):
            return re.sub(r':: (\w+)', lambda m: ':: ' + ren.get(m.group(1), m.group(1)), line)
        head = ('recursive subroutine %s(%s)' if sub else 'recursive function %s(%s) result(res_)') % (
            name, ', '.join('a%d' % i for i in range(len(dummies))))
        return ['abstract interface', IND + head, IND * 2 + 'import'] + [IND * 2 + rn(d) for d in decls] + \
            [IND + ('end subroutine %s' if sub else 'end function %s') % name, 'end interface']

    # ================================================================== records
    def component(self, f):
        t = canon(f.type)
        nm = self.field(f)
        s_, attrs, dims = self.spec(t, d=f)
        if 'REF' in attrs:
            attrs = ['pointer']
            dims = ''
        if 'pointer' in attrs:
            if s_.startswith('procedure'):
                return '%s, pointer, nopass :: %s => null()' % (s_, nm)
            return '%s, pointer :: %s%s => null()' % (s_, nm, dims)
        if s_ == 'integer(int8)':
            return '%s :: %s%s = 0_int8' % (s_, nm, dims)
        z = {'integer(int32)': '0', 'integer(int64)': '0_int64', 'real(dp)': '0.0_dp', 'real(sp)': '0.0_sp'}.get(s_)
        if z:
            return '%s :: %s%s = %s' % (s_, nm, dims, z)
        if s_ == 'type(c_ptr)':
            return '%s :: %s%s = c_null_ptr' % (s_, nm, dims)
        return '%s :: %s%s' % (s_, nm, dims)

    def record_types(self):
        deps = {}
        for name, c in self.F.records.items():
            d = set()
            for f in kids(c):
                if f.kind != K.FIELD_DECL:
                    continue
                t = canon(f.type)
                while t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
                    t = canon(t.element_type)
                if t.kind == T.RECORD:
                    d.add(record_name(t))
            deps[name] = d
        order, done = [], set()
        def visit(n, stack=()):
            if n in done or n not in deps:
                return
            if n in stack:
                raise SystemExit('recursive record by value: %s' % n)
            for m in sorted(deps[n]):
                visit(m, stack + (n,))
            done.add(n)
            order.append(n)
        for n in self.F.records:
            visit(n)
        out = []
        for name in order:
            c = self.F.records[name]
            out.append('type :: %s' % self.rname[name])
            comps = [self.component(f) for f in kids(c) if f.kind == K.FIELD_DECL]
            out += self.ind(comps or ['integer(int32) :: unused_ = 0'])
            out.append('end type %s' % self.rname[name])
        return out

    # ================================================================== globals
    def global_decl(self, name, c, owner):
        t = canon(c.type)
        tg = self.ftag(t)
        self.cur_file = owner
        line = self.decl_line(name, c.type, d=c, extra=['target'], dims_override=self.sentinel_dims(c))
        if 'pointer' in line.split('::')[0]:
            line += ' => null()'
        elif tg in NUMTAGS:
            line += ' = %s' % self.zero_value(t)
        elif tg == 'carr':
            line += ' = 0_int8'
        elif tg == 'arr':
            et = canon(t.element_type)
            while et.kind == T.CONSTANTARRAY:
                et = canon(et.element_type)
            if ctag(et) in NUMTAGS:
                line += ' = %s' % self.zero_value(et)
        elif tg == 'vp':
            line += ' = c_null_ptr'
        init = self.init_cursor(c)
        if init is not None:
            self.init_lines += ['! %s' % c.spelling] + self.init_value(name, c, init)
        return line

    # ================================================================== driver
    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        self.static_locals = []
        self.sentinel_done = set()
        procs = []
        sigs = []
        for key, c in self.F.funcs.items():
            if key[0] in SKIP_FILES:
                continue
            if key in OVERRIDES:
                dummies, decls = self.function(key, c, header_only=True)
                sigs.append('%s(%s): %s' % (self.ffname[key], ', '.join(dummies), ' | '.join(decls)))
                continue
            try:
                procs += self.function(key, c) + ['']
            except Exception as ex:
                import traceback; traceback.print_exc()
                self.problems.append('%s:%s CRASH %s' % (key[0], key[1], ex))
        # signatures of the overridden C functions that runtime/overrides.inc must match
        for fk in ('odesolve.c', 'mempool.c'):
            for key, c in self.F.funcs.items():
                if key[0] == fk:
                    dummies, decls = self.function(key, c, header_only=True)
                    sigs.append('%s(%s): %s' % (self.ffname[key], ', '.join(dummies), ' | '.join(decls)))
        # globals and static locals (their initialization runs in swmm5_init)
        self.begin_proc(None, 'swmm5_init')
        gdecls = []
        for k, c in self.F.globals.items():
            b = self.F.global_owner[k]
            if b in SKIP_FILES:
                continue
            gdecls.append(self.global_decl(self.fgname[k], c, b))
        seen = set()
        for d, b in self.static_locals:
            if decl_key(d) in seen:
                continue
            seen.add(decl_key(d))
            gdecls.append(self.global_decl(self.static_local_name(d), d, b))
        init_decls = self.decls
        init_body = self.init_lines
        # interfaces (may add types), then types
        ifaces = []
        done = set()
        while len(done) < len(self.fps):
            for sig, (name, ft) in list(self.fps.items()):
                if name not in done:
                    done.add(name)
                    ifaces += self.interface(name, ft)
        types = self.record_types()
        wraps = []
        for n, comp in self.wrappers.items():
            wraps += ['type :: %s' % n, IND + comp, 'end type %s' % n]
        out = ['! swmm5_engine.f90 - EPA SWMM 5.2.4 translated to Fortran 2008 by tools/c2x/emit_f90.py.',
               '! Generated file: fix the translator or f90/runtime/ instead of editing this.',
               '! Written by Claude (Anthropic); see AI-USE.md.',
               'module swmm5_engine',
               IND + 'use iso_fortran_env, only: int8, int32, int64, real32, real64',
               IND + 'use iso_c_binding, only: c_ptr, c_null_ptr, c_loc, c_f_pointer, c_associated',
               IND + 'use crt_base', IND + 'use crt_format', IND + 'use crt_io',
               IND + 'implicit none', '']
        out.append(IND + '! ---- enum constants')
        for n, v in self.F.enum_consts.items():
            out.append(IND + 'integer(int32), parameter :: %s = %d' % (self.fenum[n], v))
        out.append(IND + '! ---- #define constants')
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, sp) in m.items():
                if n in self.fmacro and n not in done:
                    done.add(n)
                    if kind == 'int':
                        v = int(re.sub(r'[uUlL]+$', '', sp))
                        isl = bool(re.search(r'[lLuU]$', sp)) or not (-2**31 <= v < 2**31)
                        out.append(IND + '%s, parameter :: %s = %s' % ('integer(int64)' if isl else 'integer(int32)', self.fmacro[n],
                                                                        ('%d_int64' % v) if isl else str(v)))
                    else:
                        tg = 'f' if sp.endswith(('f', 'F')) else 'd'
                        out.append(IND + '%s, parameter :: %s = %s' % ('real(sp)' if tg == 'f' else 'real(dp)', self.fmacro[n],
                                                                        ('-' if sp.startswith('-') else '') + flit(sp.lstrip('-').strip(), tg)))
        out.append('')
        out += self.ind(wraps + types) + ['']
        out += self.ind(ifaces) + ['']
        out.append(IND + '! ---- zeroed objects (C memset / value initialization)')
        for rn_, zn in self.zero_objs.items():
            out.append(IND + 'type(%s), save :: %s' % (rn_, zn))
        out.append(IND + '! ---- string literals')
        names = list(self.lits.values())
        for i in range(0, len(names), 12):
            out.append(IND + 'type(CPtr), save :: ' + ', '.join(names[i:i + 12]))
        out.append(IND + '! ---- globals')
        out += self.ind(gdecls)
        out += [IND + "include 'overrides_decl.inc'"]
        out += ['', 'contains', '']
        lit_init = ['%s = clit(%s)' % (n, fstring(b)) for b, n in self.lits.items()]
        out += ['subroutine swmm5_init()'] + self.ind(init_decls + ['call crt_init()'] + lit_init + init_body) + \
            ['end subroutine swmm5_init', '']
        out += ["include 'overrides.inc'", '']
        out += procs
        out.append('end module swmm5_engine')
        open(os.path.join(outdir, 'swmm5_engine.f90'), 'w').write('\n'.join(out) + '\n')
        open(os.path.join(outdir, 'override_signatures.txt'), 'w').write('\n'.join(sigs) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = F90Emitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, '../../f90/gen'))
    print('%d problems' % len(probs))
    for p in probs[:300]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
