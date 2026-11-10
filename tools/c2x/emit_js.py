"""
emit_js.py - EPA SWMM 5.2.4 C  ->  plain JavaScript (one CommonJS module, js/swmm5/engine.js), run by Node.

The TypeScript back end (emit_ts.py) already writes every expression and statement in a form that is valid
JavaScript: TypeScript only adds type annotations to declarations. This back end therefore subclasses
TSEmitter and replaces only the methods that write declarations (functions, hoisted locals, record classes,
module variables and the module header), so the JavaScript engine computes exactly what the TypeScript one
does, statement for statement, with no TypeScript step: node runs the generated file as it is.

The value model is TypeScript's (and so Python's): numbers are doubles kept exact where C wraps or truncates
(Math.imul, (a / b) | 0, (0 - x) so that no int becomes -0, >>> 0 for unsigned), double -> int through
R.D2I (x86-64's cvttsd2si), float through Math.fround after every float operation, char* as CPtr (a
Uint8Array plus an offset), numeric arrays as typed arrays, a C pointer to one number as an object with .v,
structs as classes with clone(). The math functions are M.* from glibm.js, glibc 2.39's FMA routines
translated from GCC's GIMPLE by tools/libm/gim2x.py's JavaScript back end.

Written by Claude (Anthropic) for Robert Dickinson; see js/README.md.
"""
import os, re, sys, collections
sys.path.insert(0, os.path.dirname(__file__))
import front
from front import K, T, kids, strip, canon, record_name, decl_key
from emit_cs import ctag, NUMTAGS, OVERRIDES, SKIP_FILES
from emit_ts import TSEmitter, TYPED, jsident, js_string

OVERRIDE_NAMES = ['sstrncpy', 'sstrcat', 'getAbsolutePath', 'getTempFileName', 'project_createMatrix',
                  'project_freeMatrix', 'odesolve_open', 'odesolve_close', 'odesolve_integrate', 'AllocInit', 'Alloc',
                  'AllocSetPool', 'AllocReset', 'AllocFreePool']


class JSEmitter(TSEmitter):
    # ------------------------------------------------------------------ functions
    def function(self, key, c):
        b, n = key
        self.cur_file = b
        self.locals = {}
        self.used_names = set()
        self.hoisted = collections.OrderedDict()
        self.cur_ret = c.result_type
        self.boxed_locals = set()
        params = list(c.get_arguments())
        body = [x for x in kids(c) if x.kind == K.COMPOUND_STMT][0]

        def scan(x):
            if x.kind == K.UNARY_OPERATOR and front.unop(x) == '&':
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
            nm = self.declare_local(prm, hoist=False)
            if decl_key(prm) in self.boxed_locals:
                ps.append('__%s' % nm)
                pre.append('  const %s = new R.Box(__%s);' % (nm, nm))
            else:
                ps.append(nm)
        lines = self.stmt(body, 0)
        assert lines[0] == '{' and lines[-1] == '}'
        out = ['// %s:%d' % (b, c.location.line), 'function %s(%s) {' % (self.fname[key], ', '.join(ps))]
        if self.hoisted:
            out.append('  let ' + ', '.join('%s = %s' % (v, z) for v, (ty, z) in self.hoisted.items()) + ';')
        out += pre
        out += lines[1:-1]
        out.append('}')
        self.exported.append(self.fname[key])
        return out

    # ------------------------------------------------------------------ records & globals
    def record(self, name, c):
        fields = [f for f in kids(c) if f.kind == K.FIELD_DECL]
        nm = jsident(name)
        out = ['class %s {' % nm]
        clone = ['  clone() {', '    const c = new %s();' % nm]
        for f in fields:
            t = canon(f.type)
            fn = 'constructor_' if f.spelling == 'constructor' else f.spelling
            if t.kind == T.CONSTANTARRAY:
                et = canon(t.element_type)
                if ctag(t) == 'c':
                    out.append('  %s = R.buf(%d);' % (fn, t.element_count))
                    clone.append('    c.%s = R.copyBuf(this.%s);' % (fn, fn))
                else:
                    out.append('  %s = %s;' % (fn, self.new_array(t)))
                    if et.kind == T.RECORD:
                        clone.append('    c.%s = this.%s.map((x) => x.clone());' % (fn, fn))
                    elif et.kind == T.CONSTANTARRAY:
                        clone.append('    c.%s = R.cloneGrid(this.%s);' % (fn, fn))
                    else:
                        clone.append('    c.%s = this.%s.slice();' % (fn, fn))
            elif t.kind == T.RECORD:
                out.append('  %s = new %s();' % (fn, self.rec(t)))
                clone.append('    c.%s = this.%s.clone();' % (fn, fn))
            else:
                out.append('  %s = %s;' % (fn, self.zero(f.type)))
                clone.append('    c.%s = this.%s;' % (fn, fn))
        clone += ['    return c;', '  }']
        return out + clone + ['}', '']

    def global_decl(self, k, c):
        name = self.gname[k]
        self.cur_file = self.F.global_owner[k]
        self.boxed_locals = set(); self.locals = {}
        t = canon(c.type)
        init = [x for x in kids(c) if x.kind not in (K.TYPE_REF, K.PARM_DECL)]
        if t.kind in (T.CONSTANTARRAY, T.INCOMPLETEARRAY):
            if init and strip(init[-1]).kind == K.INIT_LIST_EXPR:
                return 'let %s = %s;' % (name, self.init_list(strip(init[-1]), t).code)
            if ctag(t) == 'c':
                if init and strip(init[-1]).kind == K.STRING_LITERAL:
                    return 'let %s = R.bufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count)
                return 'let %s = R.buf(%d);' % (name, t.element_count)
            return 'let %s = %s;' % (name, self.new_array(t))
        if t.kind == T.RECORD:
            return 'let %s = new %s();' % (name, self.rec(t))
        v = self.conv(self.val(init[-1]), init[-1].type, c.type).code if init else self.zero(c.type)
        if k in self.boxed_globals:
            return 'let %s = new R.Box(%s);' % (name, v)
        return 'let %s = %s;' % (name, v)

    def emit(self, outdir):
        os.makedirs(outdir, exist_ok=True)
        self.static_locals = []
        self.exported = []
        self.cur_file = None
        self.boxed_locals = set(); self.locals = {}
        self.hoisted = collections.OrderedDict(); self.used_names = set()
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
                glob.append('let %s = %s;' % (name, self.init_list(strip(init[-1]), t).code))
            elif ctag(t) == 'c' and t.kind == T.CONSTANTARRAY:
                if init:
                    glob.append('let %s = R.bufFrom(%s, %d);' % (name, self.lit(self.string_bytes(strip(init[-1]))), t.element_count))
                else:
                    glob.append('let %s = R.buf(%d);' % (name, t.element_count))
            elif t.kind == T.CONSTANTARRAY:
                glob.append('let %s = %s;' % (name, self.new_array(t)))
            elif init:
                glob.append('let %s = %s;' % (name, self.conv(self.val(init[-1]), init[-1].type, d.type).code))
            else:
                glob.append('let %s = %s;' % (name, self.zero(d.type)))
        out = ['// Generated from EPA SWMM 5.2.4 by tools/c2x/emit_js.py. Do not edit by hand;',
               '// fix the translator, crt.js or overrides.js instead.',
               '"use strict";',
               'const R = require("./crt");',
               'const { CPtr, CFile } = R;',
               'const M = require("./glibm");',
               'const { %s } = require("./overrides");' % ', '.join(OVERRIDE_NAMES),
               '']
        for n, v in self.F.enum_consts.items():
            out.append('const %s = %d;' % (jsident(n), v))
        done = set()
        for b, m in self.F.macros.items():
            for n, (kind, s) in m.items():
                if n in self.macro_global and n not in done and kind in ('int', 'float') and n not in self.F.enum_consts:
                    done.add(n)
                    v = re.sub(r'[uUlL]+$', '', s) if kind == 'int' else s.rstrip('fFlL')
                    if v.startswith('.'):
                        v = '0' + v
                    elif v.startswith('-.'):
                        v = '-0' + v[1:]
                    v = re.sub(r'\.([eE])', r'.0\1', v)
                    if v.endswith('.'):
                        v += '0'
                    if kind == 'int' and len(v) > 1 and v.startswith('0'):
                        v = str(int(v, 8))
                    out.append('const %s = %s;' % (jsident(n), v))
        out.append('')
        for bts, name in self.lits.items():
            out.append('const %s = R.lit(%s);' % (name, js_string(bts)))
        out.append('')
        for name, c in self.F.records.items():
            out += self.record(name, c)
        out += glob + ['']
        out += funcs
        out.append('module.exports = {')
        for i in range(0, len(self.exported), 6):
            out.append('  ' + ', '.join(self.exported[i:i + 6]) + ',')
        out.append('};')
        open(os.path.join(outdir, 'engine.js'), 'w').write('\n'.join(out) + '\n')
        return self.problems


if __name__ == '__main__':
    F = front.Front()
    em = JSEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_js')
    print('%d problems' % len(probs))
    for p in probs[:200]:
        print(' ', p)
    for d in em.defects:
        print('  defect:', d)
