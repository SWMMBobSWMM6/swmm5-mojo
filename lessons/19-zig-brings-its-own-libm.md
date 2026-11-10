Zig links its own compiler-rt into every program, and it defines exp, log, sin and cos: an `extern "m"` call silently bound to those, not to glibc.

The first Zig gate (gate/zig_1_run.txt) passed 441 of 480 models and differed in the last digits on 39: a
continuity error of -0.175 % against EPA's -0.170 % (EPA/5_H&H_Elements (1).inp), a control rule firing 47 seconds later than EPA's. Nothing crashed and
the code was right; the numbers came from a different math library. The runtime declared glibc's functions with
`extern "m" fn exp(x: f64) f64;` and linked with `-lm`, and `ldd` showed libm.so.6, but `nm` told the real
story:

    $ nm bin/runswmm | grep -E " (t|T) (exp|log|log10|sin|cos|tan|floor)$"
    000000000111be50 t cos
    000000000111d5e0 t exp
    ...

Zig's compiler-rt (its replacement for libgcc) carries its own exp, log, log10, sin, cos, tan and floor for
targets with no C library, and a definition inside the executable wins over a shared library's. Only pow, asin,
acos and atan, which compiler-rt does not define, reached glibc. Building with `-fno-compiler-rt` leaves every
one of them undefined in the executable, bound to the same versioned glibc symbols EPA imports (exp@GLIBC_2.29,
log@GLIBC_2.29, pow@GLIBC_2.29, sin@GLIBC_2.2.5, ...), and the 39 models then matched (zig_2), then all 480
(zig_3). The one thing compiler-rt was still needed for, a 128-bit division inside std.time, went away by taking
the time from libc's time().

A second, related trap was caught before any gate: LLVM knows what `pow`, `exp` and friends compute. Unless the
build passes `-fno-builtin`, it folds `pow(1.1, 2.5)` at compile time with its own arithmetic, turns `pow(x, 2.0)`
into `x*x` and `pow(2.0, x)` into a call to exp2 (checked in the assembly of a three-line test). Each rewrite is
"as accurate", and each can move the last bit away from what glibc returns.

What to carry forward: "links against libm" is not "calls libm". After building any port that is meant to call
the system library, list the binary's own symbols and its dynamic imports and compare them with EPA's
(`nm -D ref/runswmm`), function by function and version by version.
