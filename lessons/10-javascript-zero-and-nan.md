JavaScript integers are doubles: an "int" expression can be -0, and that -0 prints as "-0.00" later.

In C, `-i` for an int i = 0 is 0; in JavaScript it is -0, and `0 * -3`, `-3 % 3` and `Math.trunc(-0.5)` are
-0 too. Nothing goes wrong until the value is converted to double and printed, when glibc's "%.2f" gives
"-0.00". The TypeScript back end therefore emits integer negation as `(0 - x)`, multiplication as
`Math.imul(a, b)`, division as `(a / b) | 0`, remainder as `(a % b) | 0`, and the runtime's D2I ends in `| 0`
-- each of which can only produce +0.

NaN needs the same care in the other direction. x86 produces NaN with the sign bit set ("default NaN"),
which glibc prints as "-nan"; JavaScript's literal `NaN` has the sign bit clear. V8 keeps the hardware's
bits when it computes 0/0 at run time and when it stores a NaN in an array, an object field or a typed array
(tools/libm/test/nan_bits.js, output in results/js_nan_bits.txt), while the literal `NaN` is always the
positive pattern. So the runtime never writes the literal where C would compute one: it builds the x86
pattern from its bits. One model in the corpus
(0ebf0b1c3ce1) prints "-nan" in its report and passes.

glibc's x86-64 log10, asin and acos are still the old SVID wrappers, which return __kernel_standard's NAN
(sign bit clear) for a domain error, not the IEEE routine's (x - x) / (x - x) (sign bit set). The ports'
wrappers say so (tools/libm/gim2x.py, WRAPPERS_TS / WRAPPERS_JAVA).
