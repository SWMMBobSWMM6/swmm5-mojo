"""
emit_py.py - EPA SWMM 5.2.4 C  ->  pure Python (one module, swmm5/engine.py)

Reuses the C# emitter's analysis (pointer modes, names, literals) and replaces the syntax.
Python-specific mapping:
  int division / remainder      -> _idiv / _imod (C truncation)        double->int -> D2I (x86 semantics)
  float (REAL4) results         -> F32()  (round to IEEE single after each float-typed operation)
  scalar pointer parameters     -> Box/FieldRef/ElemRef objects with .v ; locals whose address is taken are boxed
  char* / char[]                -> CPtr (bytearray + offset), NULL -> None
  structs                       -> classes with __slots__, clone() = C value copy
  switch                        -> if/elif, or a one-pass `while True` loop when cases fall through
  for(;;)                       -> while loop with the increment repeated before every continue
"""
import os, re, sys, collections, keyword, struct
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, binop, unop, evaluate, ptr_category, record_name, decl_key
from emit_cs import CSEmitter, Ex, ctag, NUMTAGS, OVERRIDES, SKIP_FILES, is_null

PY_RESERVED = set(keyword.kwlist) | {'abs', 'float', 'int', 'len', 'range', 'min', 'max', 'str', 'list', 'type', 'object',
                                     'math', 'struct', 'sys', 'os', 'True', 'False', 'None', 'print', 'open', 'round',
                                     'pow', 'sum', 'id', 'input', 'format', 'iter', 'next', 'bytes', 'chr', 'ord',
                                     'Box', 'FieldRef', 'ElemRef', 'CPtr', 'CFile', 'D2I', 'D2L', 'F32', 'lit', 'rt'}


def pyident(n):
    return n + '_' if n in PY_RESERVED or n.startswith('_') else n


class PyEmitter(CSEmitter):
    def __init__(self, F):
        super().__init__(F)
        # rename: C# names -> python names
        self.fname = {k: pyident(v.lstrip('@').rstrip('_') if v.endswith('_') and v[:-1] in ('S', 'R') else v.lstrip('@')) for k, v in self.fname.items()}
        self.gname = {k: pyident(c.spelling if not self._mangled(k) else self.gname[k].lstrip('@')) for k, c in F.globals.items()}
        self.boxed_globals = set()
        self._find_boxed_globals()

    def _mangled(self, k):
        return self.gname[k].lstrip('@') != self.F.globals[k].spelling

    def _find_boxed_globals(self):
        """global scalars whose address is taken (&G) are stored in a Box"""
        for k, c in self.F.globals.items():
            u = self.P.uses.get(k, set())
        self.addr_taken = set()

        def walk(c):
            if c.location.file is not None and not self.F.in_src(c):
                return
            if c.kind == K.UNARY_OPERATOR and unop(c) == '&':
                o = strip(kids(c)[0])
                if o.kind == K.DECL_REF_EXPR and o.referenced is not None and o.referenced.kind in (K.VAR_DECL, K.PARM_DECL):
                    if ctag(o.referenced.type) in NUMTAGS or canon(o.referenced.type).kind == T.POINTER:
                        self.addr_taken.add(decl_key(o.referenced))
            for ch in c.get_children():
                walk(ch)
        for b, tu in self.F.tus.items():
            walk(tu.cursor)
        for k in self.F.globals:
            if k in self.addr_taken:
                self.boxed_globals.add(k)

    # ================================================================== naming
    def global_ref(self, d):
        k = decl_key(d)
        if k in self.gname:
            return self.gname[k]
        for gk, c in self.F.globals.items():
            if c.spelling == d.spelling and not front.is_static(c):
                return self.gname[gk]
        return pyident(d.spelling)

    def global_key(self, d):
        k = decl_key(d)
        if k in self.gname:
            return k
        for gk, c in self.F.globals.items():
            if c.spelling == d.spelling and not front.is_static(c):
                return gk
        return None

    def lit(self, b):
        if b not in self.lits:
            self.lits[b] = 'L%d' % len(self.lits)
        return self.lits[b]

    def macro_name(self, n):
        for b, m in self.F.macros.items():
            if n in m and m[n][0] in ('int', 'float') and n in self.macro_global:
                return pyident(n)
        return None

    def static_local_name(self, d):
        return pyident('%s_%s' % (d.semantic_parent.spelling, d.spelling))

    # ================================================================== conversions
    def to_ctype(self, e, t):
        want = ctag(t)
        if e.tag == 'L' and want in NUMTAGS:
            return Ex('(1 if %s else 0)' % e.code, want)
        if e.tag == 'b' and want in NUMTAGS:
            return Ex(e.code, want)  # Python bools are ints
        return e

    def as_bool(self, e):
        if e.tag in ('b', 'L', 'i', 'u', 'l', 'ul', 'd', 'f'):
            return e.code
        return '(%s is not None)' % e.code

    def conv(self, e, src_t, dst_t):
        s, d = ctag(src_t), ctag(dst_t)
        if e.tag == 'L' and d in NUMTAGS:
            e = Ex('(1 if %s else 0)' % e.code, 'i'); s = 'i'
        if s == d or d in ('v', '?', 'rec'):
            return Ex(e.code, d if d not in ('?',) else e.tag)
        if d == 'i':
            if s in ('d', 'f'):
                return Ex('D2I(%s)' % e.code, 'i')
            if s in ('l', 'u', 'ul'):
                return Ex('_i32(%s)' % e.code, 'i')
            return Ex(e.code, 'i')
        if d == 'l':
            if s in ('d', 'f'):
                return Ex('D2L(%s)' % e.code, 'l')
            return Ex(e.code, 'l')
        if d == 'u':
            if s in ('d', 'f'):
                return Ex('(D2L(%s) & 0xFFFFFFFF)' % e.code, 'u')
            return Ex('(%s & 0xFFFFFFFF)' % self.paren(e.code), 'u')
        if d == 'ul':
            if s in ('d', 'f'):
                return Ex('(D2L(%s) & 0xFFFFFFFFFFFFFFFF)' % e.code, 'ul')
            return Ex('(%s & 0xFFFFFFFFFFFFFFFF)' % self.paren(e.code), 'ul')
        if d == 'd':
            return Ex(e.code, 'd')
        if d == 'f':
            return Ex('F32(%s)' % e.code, 'f')
        if d in ('c', 'o'):
            if is_null(e.code) or e.code == 'None' or e.tag == 'n':
                return Ex('None', d)
            return Ex(e.code, d)
        return e

    def zero(self, t):
        tg = ctag(t)
        return {'i': '0', 'u': '0', 'l': '0', 'ul': '0', 'd': '0.0', 'f': '0.0'}.get(tg, 'None')

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
        if len(toks) == 1 and re.fullmatch(r'(\d+\.?\d*|\.\d+)([eE][-+]?\d+)?[lL]?', toks[0]):
            s = toks[0].rstrip('lL')
            if s.startswith('.'):
                s = '0' + s
            if '.' not in s and 'e' not in s.lower():
                s += '.0'
            return Ex(s, tg)
        if len(toks) == 1 and self.macro_name(toks[0]) and tg != 'f':
            return Ex(self.macro_name(toks[0]), tg)
        v = evaluate(c)
        x = v[1] if v else 0.0
        if tg == 'f':
            x = struct.unpack('<f', struct.pack('<f', x))[0]
        return Ex(repr(x), tg)

    def x_CHARACTER_LITERAL(self, c):
        v = evaluate(c)
        return Ex(str(v[1] if v else 0), 'i')

    def x_STRING_LITERAL(self, c):
        return Ex(self.lit(self.string_bytes(c)), 'c')

    def x_DECL_REF_EXPR(self, c):
        d = c.referenced
        if d is None:
            return Ex(pyident(c.spelling), '?')
        if d.kind == K.ENUM_CONSTANT_DECL:
            if d.spelling in self.F.ambiguous_enums:
                return Ex(str(d.enum_value), 'i')
            return Ex(pyident(d.spelling), 'i')
        if d.kind == K.FUNCTION_DECL:
            n = self.func_ref(d, self.cur_file)
            if n is None:
                self.problem(c, 'function value %s' % d.spelling)
                return Ex(pyident(d.spelling), 'o')
            return Ex(n, 'o')
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
        return Ex(pyident(c.spelling), ctag(c.type))

    def x_UNEXPOSED_EXPR(self, c):
        ch = kids(c)
        if len(ch) != 1:
            if not ch:
                return Ex(self.zero(c.type), ctag(c.type))
            return self.ex(ch[0])
        e = self.ex(ch[0])
        if canon(c.type).kind == T.POINTER and e.tag == 'i' and e.code == '0':
            return Ex('None', ctag(c.type))
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
        if (e.tag == 'i' and e.code == '0' and canon(c.type).kind == T.POINTER) or is_null(e.code) or e.code == 'None':
            return Ex('None', ctag(c.type))
        if ctag(c.type) == 'o' and ctag(inner.type) == 'o':
            return e
        tgt, src = ctag(c.type), ctag(inner.type)
        if tgt == 'd' and src in ('i', 'l', 'u', 'ul'):
            return Ex('float(%s)' % e.code, 'd')
        return self.conv(e, inner.type, c.type)

    def x_CXX_UNARY_EXPR(self, c):
        v = evaluate(c)
        return Ex(str(v[1]) if v else '8', 'ul')

    def x_PAREN_EXPR(self, c):
        e = self.ex(kids(c)[0])
        return Ex('(%s)' % e.code, e.tag)

    # ================================================================== operators
    def x_UNARY_OPERATOR(self, c):
        op = unop(c)
        a = kids(c)[0]
        if op == '&':
            return self.addr_of(a, c)
        if op == '*':
            return self.deref(a)
        if op == '!':
            return Ex('(not %s)' % self.paren(self.cond(a)), 'b')
        if op in ('pre++', 'pre--', 'post++', 'post--'):
            return self.incdec_expr(a, op)
        e = self.val(a)
        if op == '-':
            return Ex('-%s' % self.paren(e.code), e.tag)
        if op == '+':
            return e
        if op == '~':
            return Ex('~%s' % self.paren(e.code), e.tag)
        self.problem(c, 'unary ' + op)
        return e

    def incdec_expr(self, a, op):
        """++/-- used as a value"""
        d = '+' if '++' in op else '-'
        tg = ctag(a.type)
        lv = self.lvalue(a)
        if tg == 'c':
            if op.startswith('pre'):
                return self._assign_value(a, '%s %s 1' % (lv, d), 'c')
            return Ex('_postp(%s, %s1)' % (self.ref_of(a), d), 'c')
        if op.startswith('pre'):
            nv = '%s %s 1' % (lv, d)
            return self._assign_value(a, 'F32(%s)' % nv if tg == 'f' else nv, tg)
        if tg in ('i', 'l', 'u', 'ul'):
            return Ex('(%s %s 1)' % (self._assign_value(a, '%s %s 1' % (lv, d), tg).code, '-' if d == '+' else '+'), tg)
        return Ex('_post(%s, %s1)' % (self.ref_of(a), d), tg)

    def _assign_value(self, l, rhs, tg):
        """assignment used as an expression value"""
        sl = strip(l)
        lv = self.lvalue(l)
        if sl.kind == K.DECL_REF_EXPR and not lv.endswith('.v') and '.' not in lv:
            return Ex('(%s := %s)' % (lv, rhs), tg)
        if sl.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sl)
            return Ex('_seti(%s, %s, %s)' % (self.ex(base).code, self.val(idx).code, rhs), tg)
        if sl.kind == K.MEMBER_REF_EXPR or lv.endswith('.v'):
            obj, attr = lv.rsplit('.', 1)
            return Ex('_seta(%s, %r, %s)' % (obj, attr, rhs), tg)
        return Ex('_seta(%s, "v", %s)' % (lv, rhs), tg)

    def ref_of(self, a, inc=None):
        """a reference object for lvalue a"""
        sa = strip(a)
        lv = self.lvalue(a)
        if lv.endswith('.v'):
            return lv[:-2]
        if sa.kind == K.MEMBER_REF_EXPR:
            obj, attr = lv.rsplit('.', 1)
            return 'FieldRef(%s, %r)' % (obj, attr)
        if sa.kind == K.ARRAY_SUBSCRIPT_EXPR:
            base, idx = kids(sa)
            return 'ElemRef(%s, %s)' % (self.ex(base).code, self.val(idx).code)
        if sa.kind == K.DECL_REF_EXPR:
            d = sa.referenced
            if d.kind == K.VAR_DECL and (d.semantic_parent is None or d.semantic_parent.kind != K.FUNCTION_DECL):
                return 'GlobalRef(globals(), %r)' % lv
            if d.kind == K.VAR_DECL and d.storage_class == front.ci.StorageClass.STATIC:
                return 'GlobalRef(globals(), %r)' % lv
        self.problem(a, 'reference to unboxed local %s' % lv)
        return 'Box(%s)' % lv

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
            return Ex(e.code + '.v', ctag(canon(a.type).get_pointee()))
        if sa.kind == K.BINARY_OPERATOR:
            l, r = kids(sa)
            return Ex('%s[%s]' % (self.ex(l).code, self.val(r).code), ctag(canon(a.type).get_pointee()))
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
                return Ex(b if i == '0' else '(%s + %s)' % (b, i), 'c')
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
                return self._assign_value(l, '%s.clone()' % self.ex(r).code, 'rec')
            re_ = self.conv(self.val(r), r.type, l.type)
            return self._assign_value(l, re_.code, ctag(l.type))
        if op in ('&&', '||'):
            return Ex('(%s %s %s)' % (self.paren(self.cond(l)), 'and' if op == '&&' else 'or', self.paren(self.cond(r))), 'L')
        if op == ',':
            return Ex('_comma(%s, %s)' % (self.val(l).code, self.val(r).code), ctag(c.type))
        lt, rt = canon(l.type), canon(r.type)
        le, re_ = self.val(l), self.val(r)
        if op in ('==', '!=', '<', '>', '<=', '>='):
            if le.tag in ('c', 'o', 'n') or re_.tag in ('c', 'o', 'n'):
                nl, nr = le.code == 'None' or is_null(le.code), re_.code == 'None' or is_null(re_.code)
                if op in ('==', '!=') and (nl or nr):
                    x = le.code if not nl else re_.code
                    return Ex('(%s %s None)' % (self.paren(x), 'is' if op == '==' else 'is not'), 'b')
                if ptr_category(l.type) == 'char' or ptr_category(r.type) == 'char':
                    return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
                return Ex('(%s %s %s)' % (le.code, 'is' if op == '==' else 'is not', re_.code), 'b')
            return Ex('(%s %s %s)' % (le.code, op, re_.code), 'b')
        tg = ctag(c.type)
        if tg == 'c':
            return Ex('(%s %s %s)' % (le.code, op, re_.code), 'c')
        if lt.kind == T.POINTER and rt.kind == T.POINTER and op == '-':
            return Ex('CPtr.diff(%s, %s)' % (le.code, re_.code), 'l')
        intlike = tg in ('i', 'u', 'l', 'ul')
        if op == '/' and intlike:
            code = '_idiv(%s, %s)' % (le.code, re_.code)
        elif op == '%' and intlike:
            code = '_imod(%s, %s)' % (le.code, re_.code)
        elif op == '/' and not self.const_nonzero(r):
            code = '_fdiv(%s, %s)' % (le.code, re_.code)
        else:
            code = '(%s %s %s)' % (le.code, op, re_.code)
        if tg == 'u':
            code = '(%s & 0xFFFFFFFF)' % code
        elif tg == 'ul':
            code = '(%s & 0xFFFFFFFFFFFFFFFF)' % code
        elif tg == 'f':
            code = 'F32%s' % code if code.startswith('(') else 'F32(%s)' % code
        return Ex(code, tg)

    def x_COMPOUND_ASSIGNMENT_OPERATOR(self, c):
        lv, rhs, tg = self.compound_parts(c)
        l = kids(c)[0]
        return self._assign_value(l, rhs, tg)

    def compound_parts(self, c):
        """(lvalue, new value expression, tag) for lhs op= rhs, with C conversions"""
        op = binop(c)[:-1]
        l, r = kids(c)
        lt, rt = ctag(l.type), ctag(r.type)
        lv = self.lvalue(l)
        re_ = self.val(r)
        if lt == 'c':
            return lv, '%s %s %s' % (lv, op, re_.code), 'c'
        common = 'd' if 'd' in (lt, rt) else ('f' if 'f' in (lt, rt) else lt)
        intlike = common in ('i', 'u', 'l', 'ul')
        if op == '/' and intlike:
            v = '_idiv(%s, %s)' % (lv, re_.code)
        elif op == '%' and intlike:
            v = '_imod(%s, %s)' % (lv, re_.code)
        elif op == '/' and not self.const_nonzero(r):
            v = '_fdiv(%s, %s)' % (lv, re_.code)
        else:
            v = '%s %s %s' % (lv, op, self.paren(re_.code))
        if lt in ('i', 'l') and common in ('d', 'f'):
            v = ('D2I(%s)' if lt == 'i' else 'D2L(%s)') % v
        elif lt == 'u':
            v = '(%s) & 0xFFFFFFFF' % v
        elif lt == 'ul':
            v = '(%s) & 0xFFFFFFFFFFFFFFFF' % v
        elif lt == 'f':
            v = 'F32(%s)' % v
        return lv, v, lt

    def const_nonzero(self, e):
        v = evaluate(strip(e))
        return v is not None and v[0] in ('int', 'float') and v[1] != 0

    def x_CONDITIONAL_OPERATOR(self, c):
        cc, a, b = kids(c)
        ea = self.conv(self.val(a), a.type, c.type)
        eb = self.conv(self.val(b), b.type, c.type)
        return Ex('(%s if %s else %s)' % (ea.code, self.cond(cc), eb.code), ctag(c.type))

    def x_ARRAY_SUBSCRIPT_EXPR(self, c):
        base, idx = kids(c)
        b = self.ex(base)
        i = self.val(idx)
        return Ex('%s[%s]' % (self.paren(b.code), i.code), ctag(c.type))

    def x_MEMBER_REF_EXPR(self, c):
        base = kids(c)[0]
        b = self.ex(base)
        return Ex('%s.%s' % (self.paren(b.code), pyident(c.referenced.spelling)), ctag(c.type))

    def paren(self, s):
        if re.fullmatch(r'[\w.\[\]]+', s) or (s.startswith('(') and s.endswith(')') and self._balanced(s[1:-1])):
            return s
        return '(' + s + ')'

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
                vals.append(self.zero(et) if ctag(et) != 'rec' else '%s()' % self.rec(et))
            return Ex('[%s]' % ', '.join(vals), 'o')
        if t.kind == T.RECORD:
            fields = [f for f in t.get_declaration().get_children() if f.kind == K.FIELD_DECL]
            parts = []
            for f, it in zip(fields, items):
                parts.append('%s=%s' % (pyident(f.spelling), self.conv(self.val(it), it.type, f.type).code))
            return Ex('%s(%s)' % (self.rec(t), ', '.join(parts)), 'rec')
        if len(items) == 1:
            return self.val(items[0])
        return Ex('None', '?')

    def rec(self, t):
        return pyident(record_name(t))

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
                    return Ex('_arr1(%s, lambda __a: %s(%s))' % (self.ref_of(kids(sa)[0]), n, ', '.join(codes)), ctag(c.type))
                if (ptr_category(p.type) == 'char' and sa.kind == K.UNARY_OPERATOR and unop(sa) == '&'
                        and front.is_char(strip(kids(sa)[0]).type) and strip(kids(sa)[0]).kind != K.ARRAY_SUBSCRIPT_EXPR):
                    codes = [self.arg(x, q) if j != i else '__c' for j, (x, q) in enumerate(zip(args, params))]
                    return Ex('_chr1(%s, lambda __c: %s(%s))' % (self.ref_of(kids(sa)[0]), n, ', '.join(codes)), ctag(c.type))
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
            if is_null(e.code) or e.code == 'None':
                return 'None'
            return 'ElemRef(%s, 0)' % e.code
        if cat == 'scalar' and pmode == 'array':
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = strip(kids(sa)[0])
                if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                    base, idx = kids(o)
                    return self.ex(base).code
        e = self.conv(self.val(a), a.type, p.type)
        return e.code

    MATH1 = {'fabs': 'math.fabs', 'sqrt': '_sqrt', 'floor': '_floor', 'exp': '_exp', 'log10': '_log10',
             'sin': '_sin', 'cos': '_cos', 'acos': '_acos', 'log': '_log', 'tan': '_tan',
             'asin': '_asin', 'atan': 'math.atan', 'ceil': '_ceil'}

    def libc(self, c, name, args):
        A = lambda i: self.val(args[i]).code
        tg = ctag(c.type)
        if name in self.MATH1:
            return Ex('%s(%s)' % (self.MATH1[name], A(0)), 'd')
        if name == 'pow':
            return Ex('_pow(%s, %s)' % (A(0), A(1)), 'd')
        if name in ('fprintf', 'snprintf', 'sscanf'):
            fixed = {'fprintf': 2, 'snprintf': 3, 'sscanf': 2}[name]
            head = [A(i) for i in range(fixed)]
            rest = [self.vararg(a, name == 'sscanf') for a in args[fixed:]]
            return Ex('rt.%s(%s)' % (name, ', '.join(head + rest)), 'i')
        if name == 'free':
            return Ex('None', 'v')
        if name in ('calloc', 'malloc', 'realloc'):
            return self.alloc(c, c.type)
        if name in ('fwrite', 'fread'):
            return self.freadwrite(c, name, args)
        if name == 'memset':
            return Ex('rt.memset(%s, %s, %s)' % (A(0), A(1), A(2)), 'v')
        if name == 'strtod':
            ep = strip(args[1])
            if ep.kind == K.UNARY_OPERATOR and unop(ep) == '&':
                return Ex('rt.strtod(%s, %s)' % (A(0), self.ref_of(kids(ep)[0])), 'd')
            return Ex('rt.strtod(%s, None)' % A(0), 'd')
        if name == 'time':
            return Ex('rt.time_()', 'l')
        if name == 'ctime':
            a0 = strip(args[0])
            return Ex('rt.ctime(%s)' % (self.ex(kids(a0)[0]).code if a0.kind == K.UNARY_OPERATOR else A(0)), 'c')
        if name == 'difftime':
            return Ex('float(%s - %s)' % (A(0), A(1)), 'd')
        if name == 'fseeko':
            name = 'fseek'
        return Ex('rt.%s(%s)' % (name, ', '.join(A(i) for i in range(len(args)))), tg)

    def vararg(self, a, scanf):
        sa = strip(a)
        if scanf:
            if sa.kind == K.UNARY_OPERATOR and unop(sa) == '&':
                o = kids(sa)[0]
                t = ctag(strip(o).type)
                return '(%r, %s)' % ({'i': 'i', 'd': 'd', 'f': 'f', 'l': 'l'}.get(t, 'i'), self.ref_of(o))
            # a number pointer passed straight through (e.g. rain.c parseStdLine's int *year): the runtime
            # needs the same (tag, box) pair it gets for &x, or it indexes the box and dies
            if ptr_category(sa.type) == 'scalar':
                t = ctag(canon(sa.type).get_pointee())
                if t in ('i', 'u', 'l', 'ul', 'd', 'f'):
                    return '(%r, %s)' % ({'u': 'i', 'ul': 'l'}.get(t, t), self.val(a).code)
            return self.val(a).code
        return self.val(a).code

    def alloc(self, call, t):
        args = list(call.get_arguments())
        t = canon(t)
        if t.kind != T.POINTER:
            return Ex('None', 'o')
        et = canon(t.get_pointee())
        name = call.spelling
        if name == 'calloc':
            n = self.count_expr(args[0], args[1], et, mul=True)
        elif name == 'malloc':
            n = self.count_expr(args[0], None, et, mul=False)
        else:
            n = self.count_expr(args[1], None, et, mul=False)
            return Ex('rt.realloc(%s, %s)' % (self.val(args[0]).code, n), 'o' if ctag(t) != 'c' else 'c')
        if ctag(t) == 'c':
            return Ex('CPtr.buf(%s)' % n, 'c')
        if et.kind == T.RECORD:
            if n == '1' or front.alloc_count_is_one(call):
                return Ex('%s()' % self.rec(et), 'o')
            return Ex('[%s() for _ in range(%s)]' % (self.rec(et), n), 'o')
        if et.kind == T.POINTER:
            return Ex('[None] * (%s)' % n, 'o')
        return Ex('[%s] * (%s)' % (self.zero(et), n), 'o')

    def count_expr(self, a, b, et, mul):
        r = CSEmitter.count_expr(self, a, b, et, mul)
        return r.replace('/', '//')

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
                return Ex('rt.%s_arr(%r, %d, %s, %s, %s, %s)' % (name, self.code_of(et), sz, self.ex(base).code, self.val(idx).code, self.val(cnt).code, fc), 'ul')
            if name == 'fwrite':
                return Ex('rt.fwrite1(%r, %d, %s, %s)' % (self.code_of(et), sz, self.ex(o).code, fc), 'ul')
            return Ex('rt.fread1(%r, %d, %s, %s)' % (self.code_of(et), sz, self.ref_of(o), fc), 'ul')
        if self.mode_of_expr(sb) == 'ref':
            et = canon(canon(sb.type).get_pointee())
            if name == 'fwrite':
                return Ex('rt.fwrite1(%r, %d, %s.v, %s)' % (self.code_of(et), sz, self.ex(sb).code, fc), 'ul')
            return Ex('rt.fread1(%r, %d, %s, %s)' % (self.code_of(et), sz, self.ex(sb).code, fc), 'ul')
        bt = canon(sb.type)
        et = canon(bt.get_pointee()) if bt.kind == T.POINTER else canon(bt.element_type)
        return Ex('rt.%s_arr(%r, %d, %s, 0, %s, %s)' % (name, self.code_of(et), sz, self.ex(sb).code, self.val(cnt).code, fc), 'ul')

    def code_of(self, et):
        return {T.DOUBLE: 'd', T.FLOAT: 'f', T.INT: 'i', T.LONG: 'q', T.CHAR_S: 'c', T.SCHAR: 'c', T.UINT: 'I', T.ENUM: 'i'}.get(canon(et).kind, '?')

    # ================================================================== statements
    def local_name(self, d):
        return self.locals.get(decl_key(d), pyident(d.spelling))

    def declare_local(self, d):
        n = d.spelling
        nn = n
        if n in self.used_names:
            i = 2
            while '%s_%d' % (n, i) in self.used_names:
                i += 1
            nn = '%s_%d' % (n, i)
        self.used_names.add(nn)
        self.locals[decl_key(d)] = pyident(nn)
        return pyident(nn)

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
            out = [p + 'if %s:' % self.cond(ch[0])]
            out += self.body(ch[1], ind + 1)
            e = ch[2] if len(ch) > 2 else None
            while e is not None:
                if e.kind == K.IF_STMT:
                    ec = kids(e)
                    out.append(p + 'elif %s:' % self.cond(ec[0]))
                    out += self.body(ec[1], ind + 1)
                    e = ec[2] if len(ec) > 2 else None
                else:
                    out.append(p + 'else:')
                    out += self.body(e, ind + 1)
                    e = None
            return out
        if k == K.WHILE_STMT:
            ch = kids(c)
            self.loops.append(('while', None))
            out = [p + 'while %s:' % self.cond(ch[0])] + self.body(ch[1], ind + 1)
            self.loops.pop()
            return out
        if k == K.DO_STMT:
            ch = kids(c)
            cnd = self.cond(ch[1])
            self.loops.append(('do', cnd))
            out = [p + 'while True:'] + self.body(ch[0], ind + 1, keep_empty=True) + [p + '    if not %s:' % self.paren(cnd), p + '        break']
            self.loops.pop()
            return out
        if k == K.FOR_STMT:
            return self.for_stmt(c, ind)
        if k == K.SWITCH_STMT:
            return self.switch(c, ind)
        if k == K.BREAK_STMT:
            ctx = self.loops[-1] if self.loops else None
            if ctx and ctx[0] == 'switch-if':
                return []           # if/elif switch: section-final break is dropped
            return [p + 'break']
        if k == K.CONTINUE_STMT:
            return self.continue_stmt(ind)
        if k == K.RETURN_STMT:
            ch = kids(c)
            if not ch:
                return [p + 'return']
            if ctag(self.cur_ret) == 'rec':
                return [p + 'return %s.clone()' % self.ex(ch[0]).code]
            e = self.conv(self.val(ch[0]), ch[0].type, self.cur_ret)
            return [p + 'return %s' % e.code]
        if k == K.NULL_STMT:
            return [p + 'pass']
        return [p + self.expr_stmt_code(c)]

    def continue_stmt(self, ind):
        p = '    ' * ind
        out = []
        for i in range(len(self.loops) - 1, -1, -1):
            kind, info = self.loops[i]
            if kind == 'switch-loop':
                self.switch_continue[-1] = True
                return [p + '_cont = True', p + 'break']
            if kind == 'switch-if':
                continue
            if kind == 'for' and info:
                out += [p + x for x in info]
            elif kind == 'do':
                return [p + 'if not %s:' % self.paren(info), p + '    break', p + 'continue']
            return out + [p + 'continue']
        return out + [p + 'continue']

    def body(self, c, ind, keep_empty=False):
        lines = self.stmt(c, ind)
        if not [l for l in lines if l.strip()]:
            return ['    ' * ind + 'pass']
        return lines

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
                return '%s = %s.clone()' % (lv, self.ex(r).code)
            rr = strip(r)
            if rr.kind == K.BINARY_OPERATOR and binop(rr) == '=':
                rhs = self.conv(self.val(r), r.type, l.type).code
                return '%s = %s' % (lv, rhs)
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
            if ctag(a.type) == 'f':
                return '%s = F32(%s %s 1)' % (lv, lv, d)
            if ctag(a.type) == 'c':
                return '%s = %s %s 1' % (lv, lv, d)
            return '%s %s= 1' % (lv, d)
        e = self.ex(c)
        code = e.code
        while code.startswith('(') and code.endswith(')') and self._balanced(code[1:-1]):
            code = code[1:-1]
        return code

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
        body_lines = self.body(body, ind + 1)
        self.loops.pop()
        out.append(p + 'while %s:' % (self.cond(cond) if cond is not None else 'True'))
        out += body_lines
        out += [p + '    ' + x for x in inc_lines]
        return out

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
                        labels.append(self.val(xc[0]).code); x = xc[1]
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
        pre = []
        if not re.fullmatch(r'[\w.]+', sv):
            self.sw_count += 1
            tmp = '_sw%d' % self.sw_count
            pre = [p + '%s = %s' % (tmp, sv)]
            sv = tmp
        allvals = [l for sec in sections for l in sec[0] if l is not None]

        def test(labels):
            vals = [l for l in labels if l is not None]
            conds = []
            if vals:
                conds.append('%s == %s' % (sv, vals[0]) if len(vals) == 1 else '%s in (%s)' % (sv, ', '.join(vals)))
            if None in labels:
                conds.append('%s not in (%s,)' % (sv, ', '.join(allvals)) if allvals else 'True')
            return ' or '.join(conds)

        simple = all(self.ends_clean(sec[1]) for sec in sections[:-1]) and all(not self.inner_break(sec[1]) for sec in sections)
        if simple:
            out = list(pre)
            first = True
            ordered = [s for s in sections if None not in s[0]] + [s for s in sections if None in s[0]]
            for labels, stmts in ordered:
                if None in labels:
                    head = (p + 'else:') if not first else (p + 'if True:')
                else:
                    head = p + ('if %s:' if first else 'elif %s:') % test(labels)
                first = False
                self.loops.append(('switch-if', None))
                lines = []
                for s_ in stmts:
                    lines += self.stmt(s_, ind + 1)
                self.loops.pop()
                if not [l for l in lines if l.strip()]:
                    lines = [p + '    pass']
                out += [head] + lines
            return out
        # general case: one-pass loop, fall-through via a flag
        self.switch_continue.append(False)
        self.loops.append(('switch-loop', None))
        out = list(pre) + [p + '_ft = False', p + 'while True:']
        for si, (labels, stmts) in enumerate(sections):
            lines = []
            for s_ in stmts:
                lines += self.stmt(s_, ind + 2)
            out.append(p + '    if _ft or %s:' % test(labels))
            out += lines or [p + '        pass']
            if not self.terminates(stmts):
                out.append(p + '        _ft = True')
        out.append(p + '    break')
        self.loops.pop()
        if self.switch_continue.pop():
            out = [p + '_cont = False'] + out + [p + 'if _cont:'] + self.continue_stmt(ind + 1)
        return out

    def ends_clean(self, stmts):
        if not stmts:
            return False
        last = stmts[-1]
        if last.kind in (K.BREAK_STMT, K.RETURN_STMT):
            return True
        if last.kind == K.COMPOUND_STMT:
            return self.ends_clean(kids(last))
        if last.kind == K.IF_STMT:
            ch = kids(last)
            return len(ch) == 3 and self.ends_clean([ch[1]]) and self.ends_clean([ch[2]])
        return False

    def inner_break(self, stmts):
        """a switch-level break that is not the final statement of its section"""
        def has_break(c):
            if c.kind == K.BREAK_STMT:
                return True
            if c.kind in (K.FOR_STMT, K.WHILE_STMT, K.DO_STMT, K.SWITCH_STMT):
                return False
            return any(has_break(x) for x in kids(c))
        for i, s_ in enumerate(stmts):
            last = i == len(stmts) - 1
            if s_.kind == K.BREAK_STMT:
                if not last:
                    return True
                continue
            if s_.kind == K.COMPOUND_STMT:
                if self.inner_break(kids(s_)):
                    return True
                continue
            if s_.kind == K.IF_STMT and last and self.ends_clean([s_]):
                ch = kids(s_)
                if self.inner_break([ch[1]]) or (len(ch) == 3 and self.inner_break([ch[2]])):
                    return True
                continue
            if has_break(s_):
                return True
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
                return [p + '%s = %s.clone()' % (name, self.ex(init[-1]).code)]
            return [p + '%s = %s()' % (name, self.rec(t))]
        v = self.conv(self.val(init[-1]), init[-1].type, d.type).code if init else self.zero(d.type)
        if boxed:
            return [p + '%s = Box(%s)' % (name, v)]
        return [p + '%s = %s' % (name, v)]

    def new_array(self, t):
        t = canon(t)
        et = canon(t.element_type)
        n = t.element_count
        if et.kind == T.RECORD:
            return '[%s() for _ in range(%d)]' % (self.rec(et), n)
        if ctag(et) == 'c' and et.kind == T.CONSTANTARRAY:
            return '[CPtr.buf(%d) for _ in range(%d)]' % (et.element_count, n)
        if et.kind == T.CONSTANTARRAY:
            return '[[%s] * %d for _ in range(%d)]' % (self.zero(et.element_type), et.element_count, n)
        if et.kind == T.POINTER:
            return '[None] * %d' % n
        return '[%s] * %d' % (self.zero(et), n)

    # ================================================================== functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.loops = []
        self.switch_continue = []
        self.sw_count = 0
        self.cur_ret = c.result_type
        self.boxed_locals = set()
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]
        # locals and params whose address is taken
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
        out = ['# %s:%d' % (b, c.location.line), 'def %s(%s):' % (self.fname[key], ', '.join(ps))]
        lines = []
        for prm, nm in zip(params, ps):
            if decl_key(prm) in self.boxed_locals:
                lines.append('    %s = Box(%s)' % (nm, nm))
        lines += self.stmt(body, 1)
        gl = sorted(self.assigned_globals(lines))
        if gl:
            out.append('    global ' + ', '.join(gl))
        if not [l for l in lines if l.strip()]:
            lines = ['    pass']
        return out + lines

    def assigned_globals(self, lines):
        names = set()
        for l in lines:
            for m in re.finditer(r'(?:^\s*|;\s*)([A-Za-z_]\w*)\s*(?:=(?!=)|\+=|-=|\*=|/=|%=|&=|\|=|\^=|<<=|>>=)', l):
                names.add(m.group(1))
            for m in re.finditer(r'\(([A-Za-z_]\w*) :=', l):
                names.add(m.group(1))
        return {n for n in names if n in self.global_names and n not in self.locals.values()}

    # ================================================================== records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = pyident(name)
        out = ['class %s:' % nm, '    __slots__ = (%s)' % ''.join('%r, ' % pyident(f.spelling) for f in fields), '',
               '    def __init__(self):']
        clone = ['    def clone(self):', '        c = %s.__new__(%s)' % (nm, nm)]
        for f in fields:
            t = canon(f.type)
            fn = pyident(f.spelling)
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    out.append('        self.%s = CPtr.buf(%d)' % (fn, t.element_count))
                    clone.append('        c.%s = self.%s.copy()' % (fn, fn))
                else:
                    out.append('        self.%s = %s' % (fn, self.new_array(t)))
                    if et.kind == T.RECORD:
                        clone.append('        c.%s = [x.clone() for x in self.%s]' % (fn, fn))
                    elif et.kind == T.CONSTANTARRAY:
                        clone.append('        c.%s = [list(x) for x in self.%s]' % (fn, fn))
                    else:
                        clone.append('        c.%s = list(self.%s)' % (fn, fn))
            elif t.kind == T.RECORD:
                out.append('        self.%s = %s()' % (fn, self.rec(t)))
                clone.append('        c.%s = self.%s.clone()' % (fn, fn))
            else:
                out.append('        self.%s = %s' % (fn, self.zero(f.type)))
                clone.append('        c.%s = self.%s' % (fn, fn))
        if not fields:
            out.append('        pass')
        clone.append('        return c')
        return out + [''] + clone + ['', '']

    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        self.boxed_locals = set(); self.locals = {}
        t = canon(c.type)
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return '%s = %s' % (name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return '%s = CPtr.buf_from(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return '%s = CPtr.buf(%d)' % (name, t.element_count)
            return '%s = %s' % (name, self.new_array(t))
        if t.kind == T.RECORD:
            return '%s = %s()' % (name, self.rec(t))
        v = self.conv(self.val(init[-1]), init[-1].type, c.type).code if init else self.zero(c.type)
        if k in self.boxed_globals:
            return '%s = Box(%s)' % (name, v)
        return '%s = %s' % (name, v)

    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        self.static_locals = []
        self.cur_file = None
        self.boxed_locals = set(); self.locals = {}
        self.global_names = set(self.gname.values())
        funcs = []
        for key, c in self.F.funcs.items():
            if key[0] in SKIP_FILES or key in OVERRIDES:
                continue
            try:
                funcs += self.function(key, c) + ['', '']
            except Exception as ex:
                import traceback; traceback.print_exc()
                self.problems.append('%s:%s CRASH %s' % (key[0], key[1], ex))
        # statics declared inside functions become module globals (names known before functions are emitted)
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
                glob.append('%s = %s' % (name, self.init_list(strip(init[-1]), t).code))
            elif ctag(t) == 'c' and t.kind == T.CONSTANTARRAY:
                glob.append('%s = CPtr.buf_from(%s, %d)' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count))
            elif init:
                glob.append('%s = %s' % (name, self.val(init[-1]).code))
            else:
                glob.append('%s = %s' % (name, self.zero(d.type)))
        out = ['# Generated from EPA SWMM 5.2.4 by tools/c2x/emit_py.py. Do not edit by hand;',
               '# fix the translator or swmm5/crt.py instead.',
               'import math',
               'from .crt import *',
               'from . import crt as rt', '', '']
        for n, v in self.F.enum_consts.items():
            out.append('%s = %d' % (pyident(n), v))
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, s) in m.items():
                if n in self.macro_global and n not in done and kind in ('int', 'float') and n not in self.F.enum_consts:
                    done.add(n)
                    v = re.sub(r'[uUlL]+$', '', s) if kind == 'int' else s.rstrip('fFlL')
                    if v.startswith('.'):
                        v = '0' + v
                    if kind == 'int' and len(v) > 1 and v.startswith('0'):
                        v = str(int(v, 8))
                    out.append('%s = %s' % (pyident(n), v))
        out.append('')
        for bts, name in self.lits.items():
            out.append('%s = lit(%r)' % (name, bts))
        out += ['', '']
        for name, c in self.F.records.items():
            out += self.record(name, c)
        out += glob + ['', '']
        out += funcs
        out += ['', 'from .overrides import *  # hand-ported odesolve.c, mempool.c and six helpers', '']
        open(os.path.join(outdir, 'engine.py'), 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = PyEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_py')
    print('%d problems' % len(probs))
    for p in probs[:100]:
        print(' ', p)
