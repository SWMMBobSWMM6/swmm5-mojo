"""
emit_hy.py - EPA SWMM 5.2.4 C  ->  Hy (one module, hy/swmm5/engine.hy), run by Hy 1.3.1 on CPython.

Hy is a Lisp that compiles to Python's own syntax tree, so its numbers, objects and calls are Python's. The
questions a translation of C has to answer for such a language (how to hold a C pointer to a number, C's
integer division and 32-bit wraparound, rounding to float after every float operation, a switch with
fall-through, a for loop with continue, division by zero) were answered by the Python back end, emit_py.py,
and its engine was checked against EPA. This back end reuses those answers and changes only the syntax: it
runs PyEmitter (emit_py.py, which reuses the C# back end's analysis of EPA's C) in memory, parses the Python
text it would have written with Python's `ast` module, and writes each node as the Hy form that compiles back
to that node:

    x = e                    (setv x e)                 a[i][j]                  (get a i j)
    x.f = e ; a[i].f = e     (setv x.f e) ; (setv (. (get a i) f) e)              e.f   (. e f)
    x += e                   (+= x e)                   f(a, b) ; o.m(a)         (f a b) ; (.m o a)
    if c: ... (no else)      (when c ...)               a if c else b            (if c a b)
    if / elif / else         (cond c1 (do ...) c2 ... True (do ...)), or (if c (do ...) (do ...))
    while c: ...             (while c ...)              x := e                   (setx x e)
    def f(a): ...            (defn f [a] ... None)      lambda a: e              (fn [a] e)
    class T: ...             (defclass T [] ...)        ~x ; a is not b          (bnot x) ; (is-not a b)
    [T() for _ in range(n)]  (lfor _ (range n) (T))     (a, b)                   #(a b)
    from .crt import *       (import .crt *)            from . import crt as rt  (import . [crt :as rt])

Three rules keep the Hy program the same program:
  - A defn ends with `None` unless its last statement is a return, so Hy's implicit return of the last form
    never hands back a value that the Python function (and the C function) does not return.
  - A name Hy would read as something else gets the suffix `__h` everywhere it appears: a core macro in call
    position (SWMM's own function `match`), or a symbol the Hy reader turns into a number (`NaN`, `Infinity`).
  - `pass` disappears; an empty body is `None`.
check_hy_ast() compiles the written Hy with Hy's compiler and compares its syntax tree, statement by statement,
with the tree of the Python text, after removing what Hy adds (`import hy`, its `_hy_anon_N` temporaries for
the value of an `if`, the `if True:` of a cond's last branch, the final `return None`): hy/test/check_conversion.py
runs it and prints the count of top-level statements that differ (0 for the shipped engine).

The runtime the engine calls (hy/swmm5/crt.hy: C strings, files, printf, strtod and sscanf, libm wrappers) and
the hand ports of odesolve.c, mempool.c and six helpers (hy/swmm5/overrides.hy) are written in Hy by hand.

Written by Claude (Anthropic) for Robert Dickinson; see hy/README.md.
"""
import ast, os, re, sys, tempfile, shutil
sys.path.insert(0, os.path.dirname(__file__))
import front
from emit_py import PyEmitter

# Hy's core macros and special forms (Hy 1.3.1: the keys of builtins._hy_macros, unmangled); a call whose head
# is one of these is that form, not a call, so a C or runtime name equal to one is renamed.
HY_FORMS = {'and', 'annotate', 'assert', 'await', 'bnot', 'break', 'chainc', 'cond', 'continue', 'cut', 'defclass',
            'defmacro', 'defn', 'defreader', 'deftype', 'del', 'dfor', 'do', 'do_mac', 'else', 'eval_and_compile',
            'eval_when_compile', 'except', 'export', 'finally', 'fn', 'for', 'get', 'get_macro', 'gfor', 'global',
            'if', 'import', 'in', 'is', 'is_not', 'let', 'lfor', 'local_macros', 'match', 'nonlocal', 'not', 'not_in',
            'or', 'pragma', 'py', 'pys', 'quasiquote', 'quote', 'raise', 'require', 'return', 'setv', 'setx', 'sfor',
            'try', 'unpack_iterable', 'unpack_mapping', 'unquote', 'unquote_splice', 'when', 'while', 'with', 'yield',
            'hy'}
NUMBER_NAMES = re.compile(r'(?i)^(nan|inf|infinity)$')

BINOPS = {ast.Add: '+', ast.Sub: '-', ast.Mult: '*', ast.Div: '/', ast.FloorDiv: '//', ast.Mod: '%', ast.Pow: '**',
          ast.LShift: '<<', ast.RShift: '>>', ast.BitOr: '|', ast.BitXor: '^', ast.BitAnd: '&'}
CMPOPS = {ast.Eq: '=', ast.NotEq: '!=', ast.Lt: '<', ast.LtE: '<=', ast.Gt: '>', ast.GtE: '>=', ast.Is: 'is',
          ast.IsNot: 'is-not', ast.In: 'in', ast.NotIn: 'not-in'}
SYMPATH = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*')
IND = '  '


def rename(n):
    """the Hy symbol for a Python identifier"""
    if n in HY_FORMS or NUMBER_NAMES.match(n) or (n.startswith('hyx_')):
        return n + '__h'
    return n


def hy_str(s, prefix=''):
    """a Hy string (or bytes, with prefix 'b') literal holding exactly s"""
    out = [prefix, '"']
    for ch in s:
        c = ch if isinstance(ch, int) else ord(ch)
        if c == 0x22:
            out.append('\\"')
        elif c == 0x5c:
            out.append('\\\\')
        elif 0x20 <= c < 0x7f:
            out.append(chr(c))
        elif c < 0x100:
            out.append('\\x%02x' % c)
        else:
            out.append('\\u%04x' % c if c < 0x10000 else '\\U%08x' % c)
    out.append('"')
    return ''.join(out)


class HyWriter:
    """Python syntax tree (the subset the Python back end writes) -> Hy text"""

    def __init__(self, src_lines):
        self.src = src_lines

    # ------------------------------------------------------------------ expressions
    def const(self, v):
        if v is None or v is True or v is False:
            return repr(v)
        if isinstance(v, int):
            return str(v)
        if isinstance(v, float):
            r = repr(v)
            if r in ('inf', '-inf', 'nan'):
                raise ValueError('non-finite float literal %r' % v)
            return r
        if isinstance(v, str):
            return hy_str(v)
        if isinstance(v, bytes):
            return hy_str(v, 'b')
        raise ValueError('constant %r' % (v,))

    def ex(self, n):
        t = type(n)
        if t is ast.Name:
            return rename(n.id)
        if t is ast.Constant:
            return self.const(n.value)
        if t is ast.Attribute:
            b = self.ex(n.value)
            if SYMPATH.fullmatch(b):
                return '%s.%s' % (b, n.attr)
            return '(. %s %s)' % (b, n.attr)
        if t is ast.Subscript:
            keys = []
            x = n
            while type(x) is ast.Subscript:
                if type(x.slice) is ast.Slice:
                    raise ValueError('slice')
                keys.append(self.ex(x.slice))
                x = x.value
            return '(get %s %s)' % (self.ex(x), ' '.join(reversed(keys)))
        if t is ast.Call:
            if n.keywords or any(type(a) is ast.Starred for a in n.args):
                raise ValueError('keyword or starred call')
            args = [self.ex(a) for a in n.args]
            f = n.func
            if type(f) is ast.Attribute:
                b = self.ex(f.value)
                if not SYMPATH.fullmatch(b):
                    return '(.%s %s)' % (f.attr, ' '.join([b] + args))
                head = '%s.%s' % (b, f.attr)
            else:
                head = self.ex(f)
            return '(%s)' % ' '.join([head] + args)
        if t is ast.BinOp:
            return '(%s %s %s)' % (BINOPS[type(n.op)], self.ex(n.left), self.ex(n.right))
        if t is ast.UnaryOp:
            o = type(n.op)
            if o is ast.USub:
                if type(n.operand) is ast.Constant and type(n.operand.value) in (int, float):
                    return '-' + self.const(n.operand.value)
                return '(- %s)' % self.ex(n.operand)
            if o is ast.UAdd:
                return '(+ %s)' % self.ex(n.operand)
            if o is ast.Not:
                return '(not %s)' % self.ex(n.operand)
            if o is ast.Invert:
                return '(bnot %s)' % self.ex(n.operand)
        if t is ast.Compare:
            if len(n.ops) == 1:
                return '(%s %s %s)' % (CMPOPS[type(n.ops[0])], self.ex(n.left), self.ex(n.comparators[0]))
            parts = [self.ex(n.left)]
            for op, c in zip(n.ops, n.comparators):
                parts += [CMPOPS[type(op)], self.ex(c)]
            return '(chainc %s)' % ' '.join(parts)
        if t is ast.BoolOp:
            return '(%s %s)' % ('and' if type(n.op) is ast.And else 'or', ' '.join(self.ex(v) for v in n.values))
        if t is ast.IfExp:
            return '(if %s %s %s)' % (self.ex(n.test), self.ex(n.body), self.ex(n.orelse))
        if t is ast.NamedExpr:
            return '(setx %s %s)' % (self.ex(n.target), self.ex(n.value))
        if t is ast.Lambda:
            return '(fn [%s] %s)' % (' '.join(rename(a.arg) for a in n.args.args), self.ex(n.body))
        if t is ast.ListComp:
            if len(n.generators) != 1 or n.generators[0].ifs:
                raise ValueError('comprehension')
            g = n.generators[0]
            return '(lfor %s %s %s)' % (self.ex(g.target), self.ex(g.iter), self.ex(n.elt))
        if t is ast.List:
            return '[%s]' % ' '.join(self.ex(e) for e in n.elts)
        if t is ast.Tuple:
            return '#(%s)' % ' '.join(self.ex(e) for e in n.elts)
        raise ValueError('expression %s' % ast.dump(n)[:200])

    # ------------------------------------------------------------------ statements
    @staticmethod
    def close(lines):
        lines[-1] += ')'
        return lines

    def body(self, stmts, ind, as_do=False):
        """the lines of a statement list; with as_do, one form (a single statement, `None`, or (do ...))"""
        lines = []
        for s in stmts:
            lines += self.stmt(s, ind + (1 if as_do else 0))
        if not as_do:
            return lines
        if not lines:
            return [IND * ind + 'None']
        if len([s for s in stmts if type(s) is not ast.Pass]) == 1:
            return [l[len(IND):] for l in lines]          # one statement: no (do ...), one level less indent
        return self.close([IND * ind + '(do'] + lines)

    def stmt(self, n, ind):
        p = IND * ind
        t = type(n)
        if t is ast.Assign:
            if len(n.targets) != 1:
                raise ValueError('chained assignment')
            return ['%s(setv %s %s)' % (p, self.ex(n.targets[0]), self.ex(n.value))]
        if t is ast.AugAssign:
            return ['%s(%s= %s %s)' % (p, BINOPS[type(n.op)], self.ex(n.target), self.ex(n.value))]
        if t is ast.Expr:
            return [p + self.ex(n.value)]
        if t is ast.Return:
            return [p + ('(return %s)' % self.ex(n.value) if n.value is not None else '(return)')]
        if t is ast.Break:
            return [p + '(break)']
        if t is ast.Continue:
            return [p + '(continue)']
        if t is ast.Pass:
            return []
        if t is ast.Global:
            return [p + '(global %s)' % ' '.join(rename(x) for x in n.names)]
        if t is ast.If:
            return self.if_stmt(n, ind)
        if t is ast.While:
            if n.orelse:
                raise ValueError('while-else')
            b = self.body(n.body, ind + 1)
            return self.close([p + '(while %s' % self.ex(n.test)] + (b or [p + IND + 'None']))
        if t is ast.FunctionDef:
            return self.defn(n, ind)
        if t is ast.ClassDef:
            if n.decorator_list or n.keywords:
                raise ValueError('class form')
            lines = [p + '(defclass %s [%s]' % (rename(n.name), ' '.join(self.ex(b) for b in n.bases))]
            for s in n.body:
                lines += self.stmt(s, ind + 1)
            return self.close(lines)
        if t is ast.Import:
            return [p + '(import %s)' % ' '.join(a.name if a.asname is None else '%s :as %s' % (a.name, a.asname)
                                                 for a in n.names)]
        if t is ast.ImportFrom:
            mod = '.' * n.level + (n.module or '')
            if len(n.names) == 1 and n.names[0].name == '*':
                return [p + '(import %s *)' % mod]
            items = ' '.join(a.name if a.asname is None else '%s :as %s' % (a.name, a.asname) for a in n.names)
            return [p + '(import %s [%s])' % (mod, items)]
        raise ValueError('statement %s' % ast.dump(n)[:200])

    def defn(self, n, ind):
        p = IND * ind
        a = n.args
        if a.vararg or a.kwarg or a.kwonlyargs or a.defaults or n.decorator_list:
            raise ValueError('function form %s' % n.name)
        lines = []
        if ind == 0 and n.lineno >= 2:
            c = self.src[n.lineno - 2].strip()
            if c.startswith('#'):
                lines.append('; ' + c[1:].strip())
        lines.append(p + '(defn %s [%s]' % (rename(n.name), ' '.join(rename(x.arg) for x in a.args)))
        lines += self.body(n.body, ind + 1)
        if not n.body or type(n.body[-1]) is not ast.Return:
            lines.append(p + IND + 'None')
        return self.close(lines)

    def if_stmt(self, n, ind):
        p = IND * ind
        if not n.orelse:
            return self.close([p + '(when %s' % self.ex(n.test)] + (self.body(n.body, ind + 1) or [p + IND + 'None']))
        if len(n.orelse) == 1 and type(n.orelse[0]) is ast.If:
            # if / elif ... chain -> cond
            pairs = []
            x = n
            while True:
                pairs.append((self.ex(x.test), x.body))
                if len(x.orelse) == 1 and type(x.orelse[0]) is ast.If:
                    x = x.orelse[0]
                    continue
                if x.orelse:
                    pairs.append(('True', x.orelse))
                break
            lines = [p + '(cond']
            for test, b in pairs:
                lines.append(p + IND + test)
                lines += self.body(b, ind + 2, as_do=True)
            return self.close(lines)
        lines = [p + '(if %s' % self.ex(n.test)]
        lines += self.body(n.body, ind + 1, as_do=True)
        lines += self.body(n.orelse, ind + 1, as_do=True)
        return self.close(lines)

    def module(self, tree, header):
        out = list(header)
        for s in tree.body:
            lines = self.stmt(s, 0)
            if type(s) in (ast.FunctionDef, ast.ClassDef):
                out.append('')
            out += lines
        return out


# ---------------------------------------------------------------------- checking the conversion
def _norm_tree(tree, from_hy):
    """the syntax tree with Hy's own additions removed, so a tree compiled from Hy compares with the original"""
    class N(ast.NodeTransformer):
        def generic_visit(self, node):
            super().generic_visit(node)
            for field in ('body', 'orelse'):
                lst = getattr(node, field, None)
                if isinstance(lst, list) and lst and isinstance(lst[0], ast.stmt):
                    new = []
                    for s in lst:
                        if type(s) is ast.Assign and len(s.targets) == 1 and type(s.targets[0]) is ast.Name \
                                and s.targets[0].id.startswith('_hy_anon_'):
                            # Hy's temporary for the value of an if: the value of the branch's last form is
                            # stored instead of discarded; only that evaluation is part of the program
                            if type(s.value) not in (ast.Name, ast.Constant):
                                new += self._ifexp_stmts(s.value)
                            continue
                        if type(s) is ast.Expr and type(s.value) is ast.Constant:
                            continue        # a bare constant (C's free() is `None`) does nothing
                        if type(s) is ast.If and type(s.test) is ast.Constant and s.test.value is True:
                            new += s.body   # cond's final `True` branch is Python's else
                            continue
                        if type(s) is ast.Import and [a.name for a in s.names] == ['hy']:
                            continue
                        if type(s) is ast.Pass:
                            continue
                        new.append(s)
                    setattr(node, field, new)
            if type(node) is ast.FunctionDef and node.body and type(node.body[-1]) is ast.Return \
                    and (node.body[-1].value is None or (type(node.body[-1].value) is ast.Constant and node.body[-1].value.value is None)):
                node.body = node.body[:-1]
            return node

        def visit_Expr(self, node):
            # Hy writes an if whose branches are single expressions as a conditional expression statement
            self.generic_visit(node)
            st = self._ifexp_stmts(node.value)
            return st if st else ast.Pass()

        def _ifexp_stmts(self, v):
            if type(v) is ast.Constant:
                return []
            if type(v) is not ast.IfExp:
                return [ast.Expr(v)]
            if type(v.test) is ast.Constant and v.test.value is True:
                return self._ifexp_stmts(v.body)
            return [ast.If(v.test, self._ifexp_stmts(v.body), self._ifexp_stmts(v.orelse))]

        def visit_UnaryOp(self, node):
            self.generic_visit(node)
            if type(node.op) is ast.USub and type(node.operand) is ast.Constant and type(node.operand.value) in (int, float):
                return ast.Constant(-node.operand.value)
            return node

        def visit_Name(self, node):
            if not from_hy:
                node.id = rename(node.id)
            return node

        def visit_FunctionDef(self, node):
            self.generic_visit(node)
            if not from_hy:
                node.name = rename(node.name)
            return node

        def visit_arg(self, node):
            if not from_hy:
                node.arg = rename(node.arg)
            return node
    return N().visit(tree)


def check_hy_ast(hy_text, py_text):
    """(number of top-level statements compared, list of differences) between Hy's compilation of hy_text and
    Python's parse of py_text"""
    import types, hy, hy.compiler
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 20000))
    module = types.ModuleType('hy_engine_check')
    forms = hy.read_many(hy_text, filename='engine.hy')
    hy_tree = hy.compiler.hy_compile(forms, module, filename='engine.hy', import_stdlib=False)
    a = _norm_tree(hy_tree, True).body
    b = _norm_tree(ast.parse(py_text), False).body
    diffs = []
    for i, (x, y) in enumerate(zip(a, b)):
        dx, dy = ast.dump(x), ast.dump(y)
        if dx != dy:
            k = next(j for j in range(min(len(dx), len(dy)) + 1) if j >= min(len(dx), len(dy)) or dx[j] != dy[j])
            diffs.append((i, getattr(y, 'name', type(y).__name__), 'hy: ' + dx[max(0, k - 150):k + 150],
                          'py: ' + dy[max(0, k - 150):k + 150]))
    if len(a) != len(b):
        diffs.append(('count', len(a), len(b)))
    return len(b), diffs


class HyEmitter(PyEmitter):
    def emit(self, outdir):
        tmp = tempfile.mkdtemp(prefix='emit_hy_')
        try:
            problems = PyEmitter.emit(self, tmp)
            py_text = open(os.path.join(tmp, 'engine.py')).read()
        finally:
            shutil.rmtree(tmp)
        tree = ast.parse(py_text)
        header = ['; Generated from EPA SWMM 5.2.4 by tools/c2x/emit_hy.py (through the Python back end, emit_py.py).',
                  '; Do not edit by hand; fix the translator, swmm5/crt.hy or swmm5/overrides.hy instead.', '']
        hy_lines = HyWriter(py_text.split('\n')).module(tree, header)
        os.makedirs(outdir, exist_ok=True)
        hy_text = '\n'.join(hy_lines) + '\n'
        open(os.path.join(outdir, 'engine.hy'), 'w').write(hy_text)
        self.py_text = py_text
        self.hy_text = hy_text
        return problems


if __name__ == '__main__':
    F = front.Front()
    em = HyEmitter(F)
    probs = em.emit(sys.argv[1] if len(sys.argv) > 1 else 'out_hy')
    print('%d problems' % len(probs))
    for p in probs[:100]:
        print(' ', p)
    if '--check' in sys.argv:
        n, diffs = check_hy_ast(em.hy_text, em.py_text)
        print('conversion check: %d top-level statements, %d differ' % (n, len(diffs)))
        for d in diffs[:10]:
            print(' ', d)
