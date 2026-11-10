Perl's `**` calls glibc's pow only when it cannot do the power itself, and POSIX::pow is the same `**`.

The brief said "`**` calls pow (prove it)". It does, for most arguments: /usr/bin/perl imports `pow@GLIBC_2.29`, the
symbol EPA imports. But `pp_pow` first looks for two integers (a whole-number double below 2**53 counts, once Perl
has cached it as an integer: lessons/35's integer path) and then computes the power with its own integer
multiplications. The answer is exact, which is not always glibc's:

- the sign of zero: `(-0.0) ** 3.0` is +0.0 in Perl, `pow(-0.0, 3.0)` is -0.0 in C;
- exact midpoints beyond 2**53: `(-214.0) ** 8.0` is 0x43ce8567f888ca30 in Perl (the exact value, an odd
  54-bit integer times 2**8, rounded to even) and 0x43ce8567f888ca31 from glibc's pow, which is accurate to about
  half an ULP but does not promise to round ties to even. On the grid of bases -300 to 300 and exponents 0 to 64,
  18 powers differ this way.

`POSIX::pow` is no way out: POSIX.pm defines it as `$_[0] ** $_[1]`. What does reach glibc is an exponent that
Perl cannot treat as an integer. A string such as "3.0" is cached as an inexact integer (the private IOK flag, not
the public one), and `pp_pow` then takes its floating-point branch and calls `pow()`: `(-0.0) ** '3.0'` is -0.0.

The Perl engine writes C's `pow(x, y)` as

    ((($t = X ** Y) && abs($t) <= 9007199254740992.0) ? $t : rt_cpow(X, Y))

A nonzero result of at most 2**53 is kept: there the integer path's exact answer is a double, and glibc's pow,
whose error bound is 0.52 ULP, can return no other double. Anything else (a zero, a NaN, a result beyond 2**53) is
recomputed by `rt_cpow` in perl/swmm5/crt.pl, which passes a whole-number exponent as the string
`sprintf('%.1f', $y)` and any other exponent as it is. `perl/test/libmcheck.pl` checks this form on glibc's own
pow vectors (1,000,272 random and 700,000 edge cases) and on a million whole-number pairs from
`perl/test/mkexact.c`, each with plain and with integer-cached operands: 0 differ.

The other math functions need no such care: `exp`, `sin`, `cos`, `log` and `sqrt` are Perl built-ins that call
glibc (perl imports `exp@GLIBC_2.29`, `log@GLIBC_2.29`, `sin`, `cos`, `sqrt`), and `tan`, `asin`, `acos`, `atan` and
`log10` come from POSIX.so, which imports them from libm. Perl's `log` and `sqrt` die where C returns -inf or a
NaN, so the engine calls them only for positive arguments and lets the runtime answer the rest.

What to carry forward: "the language calls the C library" is a statement about some arguments, not all of them.
Find the code path of every operator for every kind of operand the engine can give it, and test each path.
