In Free Pascal an untyped real constant is Extended, so `x * 0.1` is computed on the x87 in 80 bits: every float literal has to be a typed Double constant.

Free Pascal on x86-64 does its Double and Single arithmetic with SSE2, one rounding per operation, as gcc does.
A literal changes that. Compiled with `fpc -O2`, the one-line function `Result := x * 0.1` became

    fldl   (%rsp)            ; x, widened to 80 bits
    fldt   _$T4$_Ld1         ; 0.1 as an 80-bit Extended constant
    fmulp  %st,%st(1)        ; an 80-bit product
    fstpl  (%rsp)            ; rounded to double

which rounds twice and multiplies by a different 0.1 (the 80-bit one, not the double one C uses). `x < 0.1`
compiles to an x87 compare against the 80-bit constant, which is a different test from C's. The same holds
for constant folding: `1.0/3.0` is folded in Extended and then rounded. Only literals exactly representable in a
smaller type escape (0.5 becomes a Single constant).

So `tools/c2x/emit_pascal.py` never puts a real literal in an expression. Each distinct value becomes a typed
constant (`const F0p1: Double = 0.1;`), which Free Pascal treats as a variable in memory: it is never folded,
and arithmetic with it stays in SSE2. Even the typed constant's value goes through Extended on its way in
(decimal, rounded to 64 bits, then to 53), so the translator writes the decimal only where it can show, with
exact fractions, that the 80-bit step cannot land on the wrong side of a rounding midpoint; otherwise it stores
the bit pattern (`F..._bits: Int64 = $...;` with the Double declared `absolute` over it). Tables in global
initialisers get the same treatment (culvert.c's `Params`, roadway.c's `Kt_Gravel`). For the same reason the
runtime's strtod does not use Free Pascal's `Val`, which also reads through Extended; it rounds by exact
big-integer comparison.

The rule is easy to break by hand. After the port had passed the gate, a census of x87 instructions per
function in the engine's binary (`objdump -d`, counting `fcom`, `fmul`, `fadd`, ... by enclosing symbol) found
them in node_setParams, link_setParams and dozens of other functions. They were the runtime's own `D2I` and
`D2L`, inlined everywhere: `if not ((x > -2147483649.0) and (x < 2147483648.0))` compared each double with
80-bit constants. The answers happened to be the same (both constants are integers, and for `D2L` the 80-bit
-9223372036854775809.0 and the double it rounds to, -2^63, lead to the same result), but the code was not C's.
With typed constants the census finds no x87 arithmetic or comparison anywhere in the engine or the runtime;
what remains is `fldl`/`fstpt`, the exact widening of a Double that `array of const` performs when fprintf's
arguments are packed. The final gate (pas_3) ran that build.

A second Free Pascal trap, caught before it ran: the RTL's system calls have an overload with an untyped `var`
buffer next to the `PChar` one. `FpPRead(fd, f^.rbuf, n, pos)` with `rbuf` a pointer variable compiles, binds to
the `var` overload, and reads the file into the pointer variable itself and whatever follows it. Pass
`PAnsiChar(f^.rbuf)`. The same call with an expression (`b + done`) fails to compile ("Variable identifier
expected"), which is how the problem showed up.

What to carry forward: in a language whose real constants are wider than double, look at the assembly of one
multiplication by a literal before translating anything, and count the wide-format instructions per function in
the finished binary, hand-written runtime included.
