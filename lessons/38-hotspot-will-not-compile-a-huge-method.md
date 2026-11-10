HotSpot never JIT-compiles a method of more than 8,000 bytes of bytecode: a translated libm routine can stay interpreted forever.

The Groovy port's math is glibc 2.39's routines translated from GIMPLE by `tools/libm/gim2x.py`, as in the Java and
Kotlin ports. On Hydrology/SCANLON.inp the Groovy engine ran for more than 380 seconds without finishing, where the
Kotlin port takes 21 s, though the math checks had passed and every routine was correct. SCANLON calls pow millions
of times, and the size of the Groovy pow was the difference.

HotSpot has a flag, `DontCompileHugeMethods`, on by default, with `HugeMethodLimit` = 8000: a method whose bytecode is
longer than 8,000 bytes is never compiled by C1 or C2, however often it runs. Groovy's bytecode for the same routine
is much larger than javac's (array reads go through Groovy's helper calls, and the GIMPLE's block dispatch is a tree of
`if`s where Java has a `switch`), and four translations crossed the line (`javap -c`, last bytecode offset):

    Groovy:  Glibm.pow 9,161   ieee754_acos 9,732   tan 8,580   ieee754_asin 8,244   (sin 7,029, cos 7,190)
    Java:    Glibm.pow 5,558   ieee754_acos 6,159   tan 5,456   ieee754_asin 5,216
    (no generated engine method in the Groovy port is over 7,000)

On that model every one of the pow calls ran in the bytecode interpreter. The measurement
(`groovy/results/hugemethod.txt`, a copy of the deck in a scratch folder, 2 cores shared with another run):

    java -XX:+DontCompileHugeMethods (the default)   more than 380.9 s, stopped
    java -XX:-DontCompileHugeMethods                 32.6 s; .out identical to EPA's, .rpt identical except the clock lines

`groovy/runswmm` passes `-XX:-DontCompileHugeMethods`. Splitting the routines into smaller methods would also work,
but it would make the translator write something other than the GIMPLE's own control flow, and the flag changes no
result: compiled and interpreted code compute the same IEEE operations.

What to take from it: when a JVM port is many times slower than another JVM port of the same code, look at method
sizes before looking at algorithms. Generated code makes long methods easily, and the JIT's limit is silent: nothing
is logged unless you ask for it (`-XX:+PrintCompilation` shows the method never being compiled).
