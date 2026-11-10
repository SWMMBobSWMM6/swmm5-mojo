F# reads an upper-case name in a parameter list as a pattern: a byref parameter called `Qw` cannot be assigned.

The first F# build of the generated engine stopped on inlet.c's `findOnSagGrateFlows(int i, double d, double *Qw,
double *Qo)`, whose body assigns `*Qw = ...`. The translation was

    static member findOnSagGrateFlows (i: int, d: float, Qw: byref<float>, Qo: byref<float>) : unit =
        ...
            Qw <- ((3.0 * P) * Libm.pow(di, 1.5))

and fsc 12.8 (F# 8.0) answered `error FS0027: This value is not mutable`. The same member with the parameters
renamed `qw` and `qo` compiles and writes through the reference as expected (a ten-line test). F# treats an
identifier that begins with a capital letter in a pattern position, which a method's parameter list is, as a
possible union case or literal; when none exists it binds a value, but not the byref's write-through form. Upper-
case local variables (`let mutable P = 0.0`) are not affected. The translator now gives every parameter whose name
starts with a capital letter a `p_` prefix (`p_Qw`), which also silences warning FS0049 on the non-byref ones.

What to carry forward: a language's naming rules can carry meaning (Ruby's capital means a constant, lessons/27;
F#'s capital in a pattern means a case), and C names follow none of them. Map C names into a part of the target's
name space that has no such meaning, and test the mapping on a parameter that is assigned through.
