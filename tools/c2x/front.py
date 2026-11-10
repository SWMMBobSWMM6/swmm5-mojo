"""
front.py - shared C front end for the SWMM5 ports (C# / Python / Fortran).

Parses EPA SWMM 5.2.4's solver with libclang and gives the back ends:
  * the parsed translation units (one per .c file)
  * operator kinds for binary/unary expressions (via libclang's C API)
  * literal values, object-like numeric macros per file
  * whole-program tables: records (structs/unions), enums, globals, functions
  * pointer classification for every declaration that has pointer type

Nothing here is language specific.
"""
import ctypes, glob, os, re, collections
import clang.cindex as ci

K = ci.CursorKind
T = ci.TypeKind
SRC_DEFAULT = os.path.join(os.path.dirname(__file__), '../../ref/epa524/solver')
CLANG_ARGS = ['-I/usr/lib/llvm-18/lib/clang/18/include', '-std=gnu17']

_lib = ci.conf.lib
_lib.clang_getCursorBinaryOperatorKind.argtypes = [ci.Cursor]
_lib.clang_getCursorBinaryOperatorKind.restype = ctypes.c_int
_lib.clang_getCursorUnaryOperatorKind.argtypes = [ci.Cursor]
_lib.clang_getCursorUnaryOperatorKind.restype = ctypes.c_int
_lib.clang_Cursor_Evaluate.argtypes = [ci.Cursor]
_lib.clang_Cursor_Evaluate.restype = ctypes.c_void_p
_lib.clang_EvalResult_getKind.argtypes = [ctypes.c_void_p]
_lib.clang_EvalResult_getKind.restype = ctypes.c_int
_lib.clang_EvalResult_getAsLongLong.argtypes = [ctypes.c_void_p]
_lib.clang_EvalResult_getAsLongLong.restype = ctypes.c_longlong
_lib.clang_EvalResult_getAsDouble.argtypes = [ctypes.c_void_p]
_lib.clang_EvalResult_getAsDouble.restype = ctypes.c_double
_lib.clang_EvalResult_getAsStr.argtypes = [ctypes.c_void_p]
_lib.clang_EvalResult_getAsStr.restype = ctypes.c_char_p
_lib.clang_EvalResult_dispose.argtypes = [ctypes.c_void_p]

BINOPS = {3: '*', 4: '/', 5: '%', 6: '+', 7: '-', 8: '<<', 9: '>>', 11: '<', 12: '>', 13: '<=', 14: '>=',
          15: '==', 16: '!=', 17: '&', 18: '^', 19: '|', 20: '&&', 21: '||', 22: '=', 23: '*=', 24: '/=',
          25: '%=', 26: '+=', 27: '-=', 28: '<<=', 29: '>>=', 30: '&=', 31: '^=', 32: '|=', 33: ','}
UNOPS = {1: 'post++', 2: 'post--', 3: 'pre++', 4: 'pre--', 5: '&', 6: '*', 7: '+', 8: '-', 9: '~', 10: '!'}


def binop(c):
    return BINOPS[_lib.clang_getCursorBinaryOperatorKind(c)]


def unop(c):
    return UNOPS[_lib.clang_getCursorUnaryOperatorKind(c)]


def evaluate(c):
    """('int', v) | ('float', v) | ('str', bytes) | None"""
    r = _lib.clang_Cursor_Evaluate(c)
    if not r:
        return None
    try:
        k = _lib.clang_EvalResult_getKind(r)
        if k == 1:
            return ('int', _lib.clang_EvalResult_getAsLongLong(r))
        if k == 2:
            return ('float', _lib.clang_EvalResult_getAsDouble(r))
        if k in (3, 4):
            return ('str', _lib.clang_EvalResult_getAsStr(r))
        return None
    finally:
        _lib.clang_EvalResult_dispose(r)


def kids(c):
    return list(c.get_children())


def strip(c):
    """skip implicit casts / parens"""
    while c.kind in (K.UNEXPOSED_EXPR, K.PAREN_EXPR):
        ch = kids(c)
        if len(ch) != 1:
            break
        c = ch[0]
    return c


def canon(t):
    return t.get_canonical()


def is_char(t):
    return canon(t).kind in (T.CHAR_S, T.SCHAR, T.CHAR_U, T.UCHAR)


def is_func_ptr(t):
    t = canon(t)
    return t.kind == T.POINTER and canon(t.get_pointee()).kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO)


def is_file_ptr(t):
    t = canon(t)
    if t.kind != T.POINTER:
        return False
    p = t.get_pointee().get_canonical()
    return p.kind == T.RECORD and p.spelling.replace('struct ', '') in ('_IO_FILE', 'FILE')


def record_name(t):
    """C record (struct/union) name for a canonical record type: prefer the typedef used in the source."""
    t = canon(t)
    d = t.get_declaration()
    return Front.instance.record_names.get(decl_key(d), d.spelling or t.spelling)


def decl_key(d):
    if d is None or d.location.file is None:
        return None
    return (os.path.basename(d.location.file.name), d.location.line, d.location.column, d.spelling)


class Front:
    instance = None

    def __init__(self, src=SRC_DEFAULT, skip=()):
        Front.instance = self
        self.src = os.path.abspath(src)
        self.args = CLANG_ARGS + ['-I' + self.src, '-I' + self.src + '/include']
        idx = ci.Index.create()
        self.tus = {}
        for f in sorted(glob.glob(self.src + '/*.c')):
            b = os.path.basename(f)
            if b in skip:
                continue
            tu = idx.parse(f, args=self.args,
                           options=ci.TranslationUnit.PARSE_DETAILED_PROCESSING_RECORD)
            bad = [d for d in tu.diagnostics if d.severity >= 3]
            if bad:
                raise SystemExit('parse errors in %s: %s' % (b, bad[0]))
            self.tus[b] = tu
        self.record_names = {}
        self.records = collections.OrderedDict()   # name -> cursor (definition)
        self.unions = set()
        self.enum_consts = collections.OrderedDict()  # name -> int (unique names only after _collect)
        self.enum_values = collections.defaultdict(set)
        self.macros = collections.defaultdict(dict)  # file -> name -> ('int'|'float'|'str', spelling)
        self.globals = collections.OrderedDict()      # key -> cursor (definition)
        self.global_owner = {}                         # key -> .c file that defines it
        self.funcs = collections.OrderedDict()        # name(file-qualified if static) -> cursor
        self.func_by_decl = {}
        self._collect()

    # ------------------------------------------------------------------ tables
    def in_src(self, c):
        return c.location.file is not None and os.path.abspath(c.location.file.name).startswith(self.src)

    def _collect(self):
        # pass 1: typedef names of records (a typedef may follow the struct definition)
        def typedefs(c):
            for x in c.get_children():
                if x.location.file is not None and not self.in_src(x):
                    continue
                if x.kind == K.TYPEDEF_DECL:
                    ut = x.underlying_typedef_type.get_canonical()
                    if ut.kind == T.RECORD:
                        d = ut.get_declaration()
                        k = decl_key(d)
                        if k and k not in self.record_names:
                            self.record_names[k] = x.spelling
                if x.kind in (K.FUNCTION_DECL, K.COMPOUND_STMT, K.DECL_STMT):
                    typedefs(x)
        for b, tu in self.tus.items():
            typedefs(tu.cursor)
        # records defined inside function bodies
        def local_records(x):
            for y in x.get_children():
                if y.kind in (K.STRUCT_DECL, K.UNION_DECL) and y.is_definition():
                    self._add_record(y)
                elif y.kind == K.TYPEDEF_DECL:
                    for z in y.get_children():
                        if z.kind in (K.STRUCT_DECL, K.UNION_DECL) and z.is_definition():
                            self._add_record(z)
                if y.kind in (K.COMPOUND_STMT, K.DECL_STMT):
                    local_records(y)
        for b, tu in self.tus.items():
            for c in tu.cursor.get_children():
                if self.in_src(c) and c.kind == K.FUNCTION_DECL and c.is_definition():
                    local_records(c)
        for b, tu in self.tus.items():
            for c in tu.cursor.get_children():
                if not self.in_src(c):
                    continue
                fname = os.path.basename(c.location.file.name)
                if c.kind in (K.STRUCT_DECL, K.UNION_DECL) and c.is_definition():
                    self._add_record(c)
                if c.kind == K.TYPEDEF_DECL:
                    for ch in c.get_children():
                        if ch.kind in (K.STRUCT_DECL, K.UNION_DECL) and ch.is_definition():
                            self._add_record(ch)
                if c.kind == K.ENUM_DECL or (c.kind == K.TYPEDEF_DECL and any(
                        ch.kind == K.ENUM_DECL for ch in c.get_children())):
                    e = c if c.kind == K.ENUM_DECL else [ch for ch in c.get_children() if ch.kind == K.ENUM_DECL][0]
                    for ec in e.get_children():
                        if ec.kind == K.ENUM_CONSTANT_DECL:
                            self.enum_values[ec.spelling].add(ec.enum_value)
                            self.enum_consts[ec.spelling] = ec.enum_value
                if c.kind == K.VAR_DECL and (c.is_definition() or c.storage_class != ci.StorageClass.EXTERN):
                    k = decl_key(c)
                    if c.linkage == ci.LinkageKind.INTERNAL:
                        # file statics, including those in included data files (xsect.dat)
                        if fname == b or not fname.endswith('.h'):
                            self.globals[k] = c
                            self.global_owner[k] = b
                    elif fname == b or not fname.endswith('.h'):
                        self.globals[k] = c
                        self.global_owner[k] = b
                    elif fname.endswith('.h') and b == 'swmm5.c':
                        self.globals[k] = c  # EXTERN globals defined by swmm5.c's #define EXTERN
                        self.global_owner[k] = b
                if c.kind == K.FUNCTION_DECL and c.is_definition() and fname == b:
                    self.funcs[(b, c.spelling)] = c
                if c.kind == K.MACRO_DEFINITION:
                    self._add_macro(b, c)
        for k, c in self.funcs.items():
            self.func_by_decl[c.spelling] = self.func_by_decl.get(c.spelling, []) + [k]
        # enum constants defined with different values in different files are emitted as numbers
        self.ambiguous_enums = {n for n, v in self.enum_values.items() if len(v) > 1}
        for n in self.ambiguous_enums:
            self.enum_consts.pop(n, None)

    def _add_record(self, c):
        k = decl_key(c)
        name = self.record_names.get(k, c.spelling)
        if not name or name in self.records:
            return
        self.records[name] = c
        if c.kind == K.UNION_DECL:
            self.unions.add(name)

    def _add_macro(self, b, c):
        toks = [t.spelling for t in c.get_tokens()]
        if len(toks) < 2:
            return
        name, body = toks[0], toks[1:]
        # object-like only: definition range has no '(' immediately after the name
        if len(toks) >= 2 and toks[1] == '(':
            ext = list(c.get_tokens())
            if ext[1].extent.start.offset == ext[0].extent.end.offset:
                return
        txt = ' '.join(body)
        if re.fullmatch(r'-?\s*\d+[uUlL]*', txt):
            self.macros[b][name] = ('int', txt.replace(' ', ''))
        elif re.fullmatch(r'-?\s*(\d+\.\d*|\.\d+|\d+)([eE][-+]?\d+)?[fF]?', txt) and ('.' in txt or 'e' in txt.lower()):
            self.macros[b][name] = ('float', txt.replace(' ', ''))
        elif len(body) == 1 and body[0].startswith('"'):
            self.macros[b][name] = ('str', body[0])

    def file_of(self, c):
        return os.path.basename(c.location.file.name) if c.location.file else None


# ---------------------------------------------------------------------- pointers
SCALAR_KINDS = (T.INT, T.UINT, T.LONG, T.ULONG, T.DOUBLE, T.FLOAT, T.SHORT, T.USHORT, T.LONGLONG, T.ULONGLONG)


def ptr_category(t):
    """'char' | 'func' | 'file' | 'void' | 'record' | 'scalar' | 'ptrptr' | None for a pointer/array type"""
    t = canon(t)
    if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
        e = canon(t.element_type)
    elif t.kind == T.POINTER:
        e = canon(t.get_pointee())
    else:
        return None
    if is_file_ptr(t):
        return 'file'
    if e.kind in (T.CHAR_S, T.SCHAR, T.CHAR_U, T.UCHAR):
        return 'char'
    if e.kind in (T.FUNCTIONPROTO, T.FUNCTIONNOPROTO):
        return 'func'
    if e.kind == T.VOID:
        return 'void'
    if e.kind == T.RECORD:
        return 'record'
    if e.kind in SCALAR_KINDS or e.kind == T.ENUM:
        return 'scalar'
    if e.kind in (T.POINTER, T.CONSTANTARRAY, T.INCOMPLETEARRAY):
        return 'ptrptr'
    return None


def alloc_count_is_one(call):
    a = list(call.get_arguments())
    def one(x):
        x = strip(x)
        v = evaluate(x) if x.kind == K.INTEGER_LITERAL else None
        return v is not None and v[1] == 1
    if call.spelling == 'malloc':
        return strip(a[0]).kind == K.CXX_UNARY_EXPR
    if call.spelling == 'calloc':
        return one(a[0]) and strip(a[1]).kind == K.CXX_UNARY_EXPR
    return False


def is_static(c):
    return c.linkage == ci.LinkageKind.INTERNAL


class PtrInfo:
    """Usage facts for every pointer-typed declaration (var, param, field)."""
    def __init__(self, front):
        self.f = front
        self.uses = collections.defaultdict(set)     # declkey -> {'index','deref','arrow','arith','addr','malloc',...}
        self.flows = collections.defaultdict(set)    # declkey -> {declkey of source pointer}  (p = q, f(q))
        self.decl = {}                               # declkey -> cursor
        self.callee_offsets = set()
        self.func_values = set()                     # names of functions used as values (callbacks)
        for b, tu in front.tus.items():
            self._walk(tu.cursor, b)
        self.mode = {}
        self._solve()

    def key(self, d):
        if d is None:
            return None
        if d.kind == K.FIELD_DECL:
            p = d.semantic_parent
            return ('field', record_name(p.type) if p is not None else '?', d.spelling)
        return decl_key(d)

    def ref_decl(self, e):
        e = strip(e)
        if e.kind in (K.DECL_REF_EXPR, K.MEMBER_REF_EXPR):
            d = e.referenced
            if d is not None and d.kind in (K.VAR_DECL, K.PARM_DECL, K.FIELD_DECL) and ptr_category(d.type):
                k = self.key(d)
                self.decl[k] = d
                return k
        return None

    def _walk(self, c, b):
        if c.location.file is not None and not self.f.in_src(c):
            return
        if c.kind in (K.VAR_DECL, K.PARM_DECL, K.FIELD_DECL) and ptr_category(c.type):
            k = self.key(c)
            self.decl[k] = c
            if canon(c.type).kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
                self.uses[k].add('index')
            ch = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
            if c.kind == K.VAR_DECL and ch:
                self._assign(k, ch[-1])
        if c.kind == K.ARRAY_SUBSCRIPT_EXPR:
            k = self.ref_decl(kids(c)[0])
            if k:
                self.uses[k].add('index')
        elif c.kind == K.UNARY_OPERATOR:
            op = unop(c)
            k = self.ref_decl(kids(c)[0])
            if k:
                if op == '*':
                    self.uses[k].add('deref')
                elif op in ('pre++', 'pre--', 'post++', 'post--'):
                    self.uses[k].add('arith')
                elif op == '&':
                    self.uses[k].add('addr')
        elif c.kind == K.MEMBER_REF_EXPR:
            ch = kids(c)
            if ch:
                toks = [t.spelling for t in c.get_tokens()]
                k = self.ref_decl(ch[0])
                if k and canon(ch[0].type).kind == T.POINTER:
                    self.uses[k].add('arrow')
        elif c.kind == K.BINARY_OPERATOR:
            op = binop(c)
            l, r = kids(c)
            if op in ('+', '-') and canon(c.type).kind == T.POINTER:
                for x in (l, r):
                    k = self.ref_decl(x)
                    if k:
                        self.uses[k].add('arith')
            if op == '=':
                k = self.ref_decl(l)
                if k:
                    self._assign(k, r)
        elif c.kind == K.COMPOUND_ASSIGNMENT_OPERATOR:
            k = self.ref_decl(kids(c)[0])
            if k and canon(c.type).kind == T.POINTER:
                self.uses[k].add('arith')
        elif c.kind == K.DECL_REF_EXPR and c.referenced is not None and c.referenced.kind == K.FUNCTION_DECL:
            if (c.location.file.name, c.location.offset) not in self.callee_offsets:
                self.func_values.add(c.referenced.spelling)
        if c.kind == K.CALL_EXPR:
            ch0 = kids(c)
            if ch0:
                cs = strip(ch0[0])
                if cs.location.file is not None:
                    self.callee_offsets.add((cs.location.file.name, cs.location.offset))
            fd = c.referenced
            args = list(c.get_arguments())
            if fd is not None:
                params = list(fd.get_arguments()) if fd.kind == K.FUNCTION_DECL else []
                # use the definition's params when available
                defs = self.f.func_by_decl.get(fd.spelling)
                if defs:
                    params = list(self.f.funcs[defs[0]].get_arguments())
                for i, a in enumerate(args):
                    if i < len(params) and ptr_category(params[i].type):
                        pk = self.key(params[i])
                        self.decl[pk] = params[i]
                        self._assign(pk, a)
        elif c.kind == K.RETURN_STMT:
            pass
        for ch in c.get_children():
            self._walk(ch, b)

    def _assign(self, k, e):
        s = strip(e)
        if s.kind == K.CSTYLE_CAST_EXPR:
            s = strip(kids(s)[-1])
        if s.kind == K.CALL_EXPR and s.spelling in ('malloc', 'calloc', 'realloc'):
            self.uses[k].add('malloc1' if alloc_count_is_one(s) else 'malloc')
            return
        if s.kind == K.UNARY_OPERATOR and unop(s) == '&':
            o = strip(kids(s)[0])
            if o.kind == K.ARRAY_SUBSCRIPT_EXPR:
                self.uses[k].add('addr_elem')
            else:
                self.uses[k].add('addr_scalar')
            return
        src = self.ref_decl(s)
        if src:
            self.flows[k].add(src)

    def _solve(self):
        # a pointer is an 'array' if it is indexed/arith/malloc'd, or flows to/from an array
        arr = {k for k, u in self.uses.items() if u & {'index', 'arith', 'malloc'}}
        changed = True
        while changed:
            changed = False
            for k, srcs in self.flows.items():
                for s in srcs:
                    if s in arr and k not in arr:
                        arr.add(k); changed = True
                    if k in arr and s not in arr and ptr_category(self.decl[s].type) in ('scalar',):
                        # passing an array into a param that is only dereferenced keeps both arrays
                        pass
        # callbacks bound to one function-pointer type must share parameter modes:
        # a scalar pointer parameter that is an array in any of them is an array in all
        groups = collections.defaultdict(list)
        for n in self.func_values:
            for fk in self.f.func_by_decl.get(n, []):
                fc = self.f.funcs[fk]
                groups[canon(fc.type).spelling].append(fc)
        for sp, fcs in groups.items():
            nparams = len(list(fcs[0].get_arguments()))
            for i in range(nparams):
                keys = []
                for fc in fcs:
                    ps = list(fc.get_arguments())
                    if i < len(ps) and ptr_category(ps[i].type) == 'scalar':
                        k = self.key(ps[i]); self.decl[k] = ps[i]; keys.append(k)
                if any(k in arr for k in keys):
                    arr.update(keys)
        for k, d in self.decl.items():
            cat = ptr_category(d.type)
            u = self.uses.get(k, set())
            if cat == 'scalar':
                if k in arr:
                    self.mode[k] = 'array'
                elif u & {'deref', 'addr_scalar', 'addr_elem'} or d.kind == K.PARM_DECL:
                    self.mode[k] = 'ref'
                else:
                    self.mode[k] = 'array'
            elif cat == 'record':
                self.mode[k] = 'array' if k in arr else 'obj'
            elif cat == 'ptrptr':
                self.mode[k] = 'array' if k in arr else 'ref'
            else:
                self.mode[k] = cat

    def mode_of(self, d):
        return self.mode.get(self.key(d))
