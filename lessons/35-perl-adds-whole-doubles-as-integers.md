Perl adds, subtracts and multiplies whole-number doubles as 64-bit integers: exact, fast, and blind to C's -0.0.

Perl keeps a number as an integer (IV) whenever it can, a feature called IV preservation. `pp_add`,
`pp_subtract` and `pp_multiply` first ask whether both operands are integers; a double holding a whole number
below 2**53 counts (Perl caches the integer beside the double the first time a comparison or an arithmetic op
looks at it), and then the operation is done in 64-bit integer arithmetic. For whole numbers below 2**53 that is
exactly the double C computes, with one exception: an integer has no sign of zero.

    my ($z, $m) = (0.0, -3.0);   $z * $m      Perl +0.0   C -0.0
    my ($n, $p) = (-0.0, -0.0);  $n + $p      Perl +0.0   C -0.0
                                 $n - 0.0     Perl +0.0   C -0.0
    my $q = $z - 0.0;            -$q          Perl +0.0   C -0.0

C prints -0.0 as "-0.00", so the sign reaches EPA's reports. The Perl back end (tools/c2x/emit_perl.py, `zfix`)
writes a double `+`, `-` or `*` whose operands could both be whole as `((A * B) || rt_zm(A, B))`: `||` keeps any
nonzero result (and a NaN, which is true in Perl), and a zero result is recomputed by the runtime from the operands'
sign bits with C's rules (`rt_zm`, `rt_za`, `rt_zs`, `rt_zn` in perl/swmm5/crt.pl). An operand with a call or a side
effect is evaluated once into a temporary. The fix is left out where C's answer cannot be -0.0 or Perl cannot take
the integer path: a literal that is not whole (0.5, 32.2) as either operand; a sum with a literal or a converted C
integer as an operand; a difference whose left operand is one of those, or whose right one is a nonzero literal.

The integer path is also exact where C rounds. A chain of operations on whole numbers that passes 2**53 keeps
every bit in Perl and rounds at each step in C:

    my ($x, $y) = (2.0**53, 1.0);   ($x + $y) + $y   Perl 9007199254740994   C 9007199254740992

One rounding at the end gives C's answer, so a single operation is safe; a chain is not. No fix is applied for
this: it takes whole-number doubles beyond 9e15 passed from one integer operation to the next, which is not ruled
out but is far from SWMM's quantities; on the gate models it would show as a difference.

How it was checked: `perl/test/libmcheck.pl` evaluates each operation in the exact form the engine uses, twice:
once on plain doubles, and once after a comparison has made Perl cache each operand as an integer (the state the
engine's variables are in). `perl/test/mkexact.c` supplies a million whole-number operand pairs for `*`, `+` and
`-`, zeros of both signs among them: 0 differ (`perl/results/libm_tests.txt`). Without the fix, every zero product
of two whole numbers with one negative operand (-0.0 included) would come out +0.0 in that mode.

What to carry forward: an interpreter that keeps integers and doubles in one scalar type may switch between them
behind your back. Test each arithmetic operation with operands in every internal state the engine can leave them
in, not only as freshly made doubles.
