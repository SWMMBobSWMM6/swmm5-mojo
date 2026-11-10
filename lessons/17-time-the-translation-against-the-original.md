Time a translated routine against the original, call for call; a dispatch loop can cost a factor of five.

The math translator (tools/libm/gim2x.py) first wrote every glibc routine for Go the way it writes them for
TypeScript and Java, which have no goto: one loop that picks the next GIMPLE basic block by number, with
every value held across the loop and each PHI chosen by "which block did we come from". The results were
right on all 22 million test arguments. The bit-for-bit test said nothing about speed, and the engine benchmark
only said Go was about twice EPA's CPU time.

A CPU profile of one long model (gate/results/go_pprof_loop.txt) put almost half the time in pow, sin and
cos, and a stopwatch on two million arguments (gate/go_powtime.sh) gave the reason. Go's pow took 93 ns a
call and glibc's own took 17 ns. Go has goto, so the blocks became labels, each edge a jump, and each PHI a
parallel assignment on its edge. pow fell to about 20 ns, with the same bits on every test argument, and the
whole gate ran about 30% faster (go_final1 against go_final in gate/results). `gim2x.py --go-loop` still
writes the old form, so the comparison can be repeated.

What to carry forward: a correctness test and an end-to-end benchmark can both pass while one routine is
five times slower than it should be. Time the hot routines directly against the code they were translated
from. The TypeScript and Java translations still use the loop form because those languages have no goto.
They might gain from structured control flow too; that was not tried.
