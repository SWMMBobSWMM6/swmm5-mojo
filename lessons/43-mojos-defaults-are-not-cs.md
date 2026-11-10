Mojo's defaults are not C's: it fuses a*b+c into one FMA, has no global variables, and writes "\xb3" as two bytes.

Building the Mojo port turned up five places where Mojo 1.2.0, as installed from PyPI (`mojo-compiler`), departs from
what a C translation can take for granted. Each was found by a small test before or during the first build, and each
is handled in `tools/c2x/emit_mojo.py` or `mojo/build.sh`:

1. **Contraction is on by default.** `mojo build --help`: "`contract=fast` (default) ... fuses `a + b*c` into an FMA
   across statements". A one-line function `x * y + z` compiled to `vfmadd213sd`. C as EPA's gcc build compiles it
   rounds the product and the sum separately, so every build of the engine passes `--fp-mode contract=off` (and
   `--target-cpu x86-64`, the baseline EPA targets); `objdump -d` of the engine shows no FMA instruction.
2. **No global variables.** `var G: Int32 = 5` at file scope is rejected ("global variables are not supported").
   EPA has 626 globals. They are fields of one `Globals` struct, allocated at start-up, and every translated
   function takes a pointer to it as its first parameter; the runtime's state hangs off it too.
3. **A string literal is UTF-8 text.** `"a\xb3b"` is the bytes 61 C2 B3 62: `\xb3` is the character U+00B3, encoded.
   Four of EPA's report headers contain the byte 0xB3 (the cube in `1000 ft³`, written in Latin-1); the engine builds
   those four strings from their bytes at start-up.
4. **A float literal can lose a subnormal.** `Float32(1e-45)` is 0 in Mojo; C rounds 1e-45 to the smallest
   subnormal float. `Float64(<decimal>)` was right on all 3,011 values tried (random bit patterns, subnormals, the
   halfway case 2.4703282292062328e-324), so double constants are written as decimals; float constants are written
   from their bits.
5. **A function value cannot be a struct field** ("struct fields do not support trait types"), so C function
   pointers are numbers with a generated dispatcher per signature.

Two more facts worth knowing before the next Mojo program: the compiler's memory grows with the size of a single
function (a test `main` of 3,000 `print` calls was killed by the out-of-memory killer at 5.5 GB resident; the same
calls in 25-line functions compiled in 0.56 GB, and the whole engine, 1,013 functions, compiles in 0.53 GB), so the
start-up code that fills EPA's tables is split into small functions; and LLVM folds `pow(1.1, 2.5)` called through
`external_call` at compile time, so the libm wrappers are `@no_inline`.

What to take from it: a new compiler's defaults are part of the program. Before translating anything, compile a
handful of one-line probes (a multiply-add, a global, a non-ASCII string, the smallest subnormal, a function stored
in a struct) and read what comes out.
