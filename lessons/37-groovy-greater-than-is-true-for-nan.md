Groovy's static compiler makes `a > b` and `a >= b` true when either double is NaN; C and Java make them false.

The Groovy port is the Java port's translation run through Groovy 3.0.24 with `@CompileStatic` on every class, so it
was expected to behave as Java does. In the first development runs, EPA/swmm5_shapes.inp's `.out` matched EPA's but
its report did not. Where EPA's routing summary says

    Convergence obtained at all time steps.

the Groovy port's listed five nodes as not converging:

    Node 10208 (-nan%)
    Node 16109 (-nan%)
    ...

(These nodes' depths are NaN in EPA's own run too; its Node Depth Summary prints `-nan` for them, an EPA defect that
every port reproduces.)

The cause is in how the two compilers turn a comparison of doubles into bytecode. The JVM has two instructions that
compare doubles, `dcmpl` and `dcmpg`; they differ only in what they push when either operand is NaN (-1 and +1).
javac picks, for each operator, the one that makes the comparison false for NaN: `dcmpl` for `>` and `>=`, `dcmpg`
for `<` and `<=`. Groovy's static compiler uses `dcmpg` for all four (`groovy/results/nan_compare.txt`):

    static boolean gt(double a, double b) { return a > b }      // @CompileStatic, Groovy 3.0.24
       0: dload_0
       1: dload_2
       2: dcmpg              <- NaN pushes +1
       3: ifle          10   <- +1 is not <= 0, so the branch to "false" is not taken
       6: iconst_1

    NaN > 1.0: true   NaN >= 1.0: true   NaN < 1.0: false   NaN <= 1.0: false   1.0 > NaN: true   1.0 >= NaN: true

EPA's code that met it, in `stats_updateMaxStats` (stats.c), keeps the most critical statistics in a short sorted list:

    if ( fabs(maxStats1.value) > fabs(maxStats[k].value) )
    {
        maxStats2 = maxStats[k];
        maxStats[k] = maxStats1;
        maxStats1 = maxStats2;
    }

It is called for the non-convergence list (`MaxNonConverged`, five entries, which start with no node and value 0)
with each node's `NodeStats[j].nonConvergedCount / stepCount`, which is NaN for these nodes on this model. The
generated Groovy was the same test, `if ((Math.abs(maxStats1.value) > Math.abs(maxStats[k].value)))`. In C a node
whose statistic is NaN never enters the list, because the test is false, so the list stays empty and the report says
convergence was obtained; in Groovy the test was true, the NaN nodes filled the list, and the report printed them.

The fix is in the translator, not the generated code: `tools/c2x/emit_groovy.py` writes every `>` and `>=` between
floating-point values as a call, `R.dgt(a, b)` and `R.dge(a, b)`, which are `b < a` and `b <= a` (Groovy compiles `<`
and `<=` correctly). The new Groovy back end of `tools/libm/gim2x.py` swaps the operands of the same comparisons in
glibc's translated routines, and the hand-written runtime was searched for the operators by hand. After that the
model, and then all 480, matched EPA.

What to take from it: a language that compiles to the same virtual machine as a language you trust can still differ
in the instructions it picks. NaN is where comparison instructions differ, and SWMM's statistics meet NaN on real
models, so test NaN comparisons (all four operators, NaN on either side) in any new back end before the first gate.
