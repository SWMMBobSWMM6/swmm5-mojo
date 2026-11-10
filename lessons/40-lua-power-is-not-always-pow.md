Lua 5.4's `x ^ 2` is `x * x`, not pow, and `math.atan(x)` is `atan2(x, 1)`, not atan: both differ from glibc's answers.

The brief for the Lua port said Lua's math library calls the C library. It does, but two of the calls are not the
ones C programs make. In Lua 5.4's source (llimits.h):

    #define luai_numpow(L,a,b)  \
      ((void)L, (b == 2) ? (a)*(a) : l_mathop(pow)(a,b))

so `x ^ y` calls `pow` except when `y` is 2; and `math.atan(y [, x])` (lmathlib.c) calls `atan2(y, x)`, with `x` = 1
when one argument is given. `x * x` is the correctly rounded square; glibc's pow is accurate to within about half an
ulp but not correctly rounded, so now and then it rounds the other way. `atan(x)` and `atan2(x, 1.0)` are different
routines with different rounding errors. Counted on 20,000,000 arguments (`lua/test/pow2_atan2.c`,
`lua/results/pow2_atan2.txt`):

    pow(x, 2) differs from x * x in 12,953;  atan(x) differs from atan2(x, 1) in 539
    e.g. pow(-0x1.413019a6be445p-3, 2) = 0x1.92f9a95dca40ap-6, x * x = 0x1.92f9a95dca40bp-6, and Lua's x ^ 2.0 gives the second

EPA raises model values to exponents read from the model (a storage curve's `pow(d, n)` in node.c, an LID drain's
`pow(head, theLidProc->drain.expon)` in lidproc.c, a power-law cross-section's `pow(y, xsect->sBot)`), any of which
can be 2, and its math expressions (treatment functions, custom groundwater flow, control-rule expressions) offer
`atan`; either difference changes a result in the last bit, and the next time step carries it on. The Lua port
computes both with glibc's own code: the translator writes `x ^ c` only when `c` is a constant other than 2, and
`R.pow` otherwise, which sends `y == 2` to glibc's pow translated from GIMPLE (`lua/swmm5/glibm.lua`, the Lua back end
of `tools/libm/gim2x.py`); `atan` always goes to the translated atan. Every other function the engine needs is Lua's
math library calling glibc, which `lua/test/run_libm_tests.sh` checks bit for bit. That check found one more case:
lupa's library imports `log` without a symbol version, so it gets glibc's oldest one, whose wrapper returns a NaN with
the sign bit clear for a negative argument (`math.log(-1)` is 0x7ff8000000000000) where EPA's `log@GLIBC_2.29` sets it
(0xfff8000000000000); `R.log` returns the latter for x < 0.

What to take from it: "the language calls the C library" has to be checked function by function and for the
arguments the program uses, as lessons/36 found for Perl's `**`: an interpreter can special-case an argument
(`y == 2`) or route a function through a different one (`atan2`).
