PHP's optimizer treats 0.0 and -0.0 as the same constant: with OPcache on, `$neg ? -0.0 : 0.0` returned -0.0 for a false $neg.

The PHP port's runtime check (`php/test/run_crtcheck.sh`, the 1,394,252 glibc cases the other runtimes replay)
found one strtod case wrong, and only when OPcache was on:

    strtod("0x")   glibc: 0000000000000000:1   php: 8000000000000000:1

The code that returns it is `return [$neg ? -0.0 : 0.0, $i + 1];` in `rt_scan_double` (the text "0x" with no hex
digit is the number 0), with `$neg` false. Without OPcache the answer is +0.0. Turning the optimizer's passes off
one bit of `opcache.optimization_level` at a time found the culprit: pass 8 (bit 0x80), sparse conditional constant
propagation, which runs on the SSA form the DFA pass (bit 0x20) builds; with either bit cleared the answer is right.
The likely mechanism (the bisection shows the pass, not the line): when SCCP merges the two arms of the conditional it
compares the constants the way PHP's `===` does, and in PHP `-0.0 === 0.0` is true, so it takes the conditional for
one constant and puts one of the two zeros in its place, here the wrong one. The interpreter alone gives +0.0.

The generated engine has no `-0.0` literal (EPA's C has none), so no gate model could have shown this. But SCCP
can meet the same pair after folding other constants, and C's sign of zero reaches the report ("-0.00"). So
`php/runswmm` runs with `-d opcache.optimization_level=0x7FFEBF7F`, the default with that one bit cleared, and the
runtime and math checks run with the same settings. Clearing it changed the engine's speed by nothing measurable on
the one model timed.

Two more PHP facts the checks turned up, each now handled in the runtime:
- PHP's `floor()` and `ceil()` return a signaling NaN unchanged; glibc's return it quiet (bit 51 set). The engine
  calls `rt_floor`/`rt_ceil`, which quiet a NaN with `x + x` first (`php/test/run_libm_tests.sh`: 0 of 21.3 million
  differ, with and without the JIT). Every other PHP math function EPA needs calls glibc's directly.
- PHP's `-$x` is a multiplication by -1, which leaves a NaN's sign bit alone where C's negation flips it (checked:
  -NaN of 0xfff8000000000000 stays 0xfff8000000000000). The engine negates doubles with `rt_neg`.

What to carry forward: an optimizing compiler or VM can hold its own idea of which numbers are equal. Run the C
library checks with the exact flags the engine runs with (here the OPcache and JIT settings), and bisect the
optimizer's switches when only the optimized run disagrees.
