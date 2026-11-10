The Pascal engine passed 480 of 480 with a strtod that got 115,302 of 200,052 glibc test conversions wrong: check the runtime against the C library directly.

The Pascal runtime converts decimal text to binary in two ways. Numbers with at most 15 significant digits and
a decimal exponent within ±22 take a fast path that is exact (one correctly rounded multiplication or division
of two exactly representable doubles). Everything else goes to a slow path that finds the nearest double by
exact big-integer comparison and bisection. In the first version the bisection kept the wrong half
(`if cmpBits(mid) <= 0 then lo := mid`, where `>= 0` was meant), so slow-path results were wrong.

The first Pascal gate (gate/pas_1_run.txt) ran with that version and passed all 480 models: either no number
in the corpus takes the slow path, or none that does changes an output. The runtime check
(`pascal/test/run_crtcheck.sh`, replaying 1,394,252 printf, strtod and sscanf cases written by glibc through
`tools/crt/test/mkfmt.c`) found it at once: strtod, 115,302 of 200,052 cases differ, for example
`0.1000000000000000055511151231257827` read as 0x3fb99999999999d9 instead of 0x3fb999999999999a. With the
comparison turned round, 0 differ, and the later gates (pas_2, and pas_3, the final one) ran the corrected runtime.

What to carry forward: the gate tests the runtime only through the inputs 480 models happen to contain. A
port's C-library layer needs its own check against the C library, on inputs chosen to reach every path (long
digit strings, huge and tiny exponents, hexadecimal, subnormals), before the gate, not instead of it.
