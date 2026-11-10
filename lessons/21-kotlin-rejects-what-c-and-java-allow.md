Kotlin rejects more of C than Java does: no implicit conversions, no assignment expressions, and a bare { } is a lambda.

The Kotlin back end (tools/c2x/emit_kotlin.py) reuses the Java back end's analysis and type model, since both run
on the JVM, but almost none of its text: the rules that make Kotlin safer are exactly the things C code does
without a second thought. Each had to be written into the translator before the first build:

- **No implicit numeric conversion.** Java widens int to double or long by itself; Kotlin does not even compare
  an Int with a Long. Every conversion clang records (its implicit casts are in the AST) is written out
  (`.toDouble()`, `.toLong()`, `R.D2I(...)`), so each operation runs at C's types and nothing is left to the
  target language's own rules. The same applies to integer literals: `-2147483648` is a Long in Kotlin (the
  literal 2147483648 does not fit an Int), so the most negative Int and Long are written as `Int.MIN_VALUE` and
  `Long.MIN_VALUE`, here and in the math translation (tools/libm/gim2x.py kt).
- **Assignments are statements.** `if ((Frain.file = fopen(Frain.name, "w+b")) == NULL)` (rain.c:145),
  `return (ErrorCode = ERR_API_NOT_OPEN);` (swmm5.c:324) and `return qCaptured *= Nsides;` (inlet.c:1320) are C;
  in Kotlin an assignment, `+=` or a pointer `++` used as a value becomes `(v).also { __v -> x = __v }`.
- **Parameters are read-only.** C assigns to its parameters freely; a parameter the body assigns is copied into
  a local of the same name.
- **A bare block is a lambda.** `{ int t; ... }` inside a function would become a lambda that is never called.
  Nested C blocks are flattened; the Java back end already makes local names unique per function.
- **No C for, no switch, no fall-through, no unlabelled jump out of when.** `for` becomes init; while; and
  every `continue` runs the increment first; `switch` becomes `when`, with fall-through written out and a
  labelled `do { } while (false)` when a `break` leaves a case early. Kotlin wants `else` last, so the default
  branch moves to the end (C case values are distinct, so the order does not matter).
- **Null safety.** Every reference type is declared nullable and dereferenced with `!!`, which fails where C
  would.

The one the compiler caught: private top-level declarations in one file clash with public ones of the same name
anywhere in the package. The hand-written odesolve port declared `private const val SAFETY = 0.9` (and five
more); the generated Consts.kt has public `SAFETY` from the same C macro, and the first build stopped with
"conflicting declarations". The hand-written names now carry an `ODE_` prefix. In Java the private field would
simply have shadowed the static import.

What to carry forward: when a target language is stricter than Java, make the translator write out everything
C leaves implicit (conversions, evaluation of assignments, scopes), rather than relying on the target's
defaults. The generated Kotlin compiled without an error on its first build (the only errors were in the
hand-written runtime above), and the first gate run, kt_1, gave 480 of 480 models identical to EPA.
