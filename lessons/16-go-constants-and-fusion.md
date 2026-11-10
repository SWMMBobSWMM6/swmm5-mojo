In Go, type every float literal and wrap every float operation: constants are exact, and compilers may fuse.

Two Go rules can each change a result in the last bit, and neither shows up on the machine you test on.

**Constants.** Go evaluates constant expressions with unlimited precision and rounds once. Written as two
untyped literals, `0.1 * 3.0` is 0.299999999999999988898 (bits 3fd3333333333333). C rounds 0.1 to a double
first and then multiplies, giving 0.300000000000000044409 (bits 3fd3333333333334). A translator that copies
`0.1 * 3.0` into Go unchanged has changed the program. The Go back end (tools/c2x/emit_go.py) writes every
float literal as `float64(0.1)`, a typed constant, which is rounded immediately, and wraps each operation in
`float64(...)`, so Go rounds after each step as C does. The same rule loses negative zero: the constant
`-0.0` is +0, so C's negation of a zero constant becomes a run-time `R.NegZero`.
Evidence: `go run ./internal/constcheck` in go/, gate/results/go_constants.txt.

**Fusion.** The Go specification lets a compiler fuse `x*y + z` into one FMA, even across statements,
unless the product is explicitly converted: `float64(x*y) + z`. On x86-64, Go 1.24 fuses neither form, even
at GOAMD64=v3. On arm64 it fuses the plain form (`FMADDD`) and not the converted one (`FMULD`, `FADDD`).
A port tested only on x86 would have looked correct and drifted on an ARM machine.
Evidence: gate/check_go_fma.sh and gate/check_go_fma_arm64.sh, results in gate/results/go_fma_check.txt and
go_fma_arm64.txt. Go's own disassembler misreads x86 FMA encodings (it shows the VEX bytes as MOVL), so the
x86 check uses GNU objdump. On arm64, Go's disassembler is right.

The general point: when the target language's rules differ from C's in a way your test machine never
exercises, write the output so the rule cannot matter, then check the generated machine code on a
platform where it would.
