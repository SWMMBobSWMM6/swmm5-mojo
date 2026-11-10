Java refuses three things C accepts: unreachable statements, expressions as statements, and lambdas over changing locals.

The Java back end (tools/c2x/emit_java.py) is the C# back end's types plus the Python/TypeScript reference
model, and it had to handle:

- `return x; break;` -- Java rejects the unreachable `break`. The emitter applies Java's "can complete
  normally" rules (JLS 14.22) to the C statement and drops what follows a statement that cannot.
- `(void) x;` or `a == b;` -- not statements in Java; they become `R.discard(...)`.
- Lambdas may only capture effectively-final locals, and C locals are reassigned freely. So `&local`
  passed to a pointer parameter uses a box object (DBox, IBox, ...), struct fields use lambdas over the
  object (`__o -> __o.depth`), and the two calls that pass `&x` where the callee indexes an array get a
  one-element array set up before the statement and copied back after it. The lambda parameters are named
  `__o`/`__x` because Java also forbids a lambda parameter named like a local in scope.
