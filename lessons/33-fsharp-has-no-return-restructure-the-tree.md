F# has no return, break, continue or goto: restructure C's control flow as a tree first, and set a flag only where a jump would skip code.

The F# back end (tools/c2x/emit_fsharp.py) could not translate statement by statement as every earlier back end did,
because every C jump has to become structure. It builds each function body as a small tree (blocks, ifs, loops,
switches, jumps), restructures the tree, and only then writes F#:

1. Code after a statement that cannot complete normally is dropped, as C compilers drop it.
2. `if (c) <jump>; rest` becomes `if c then <jump> else rest`. This one rule turns most of EPA's early returns
   (`if (ErrorCode) return ErrorCode;`, the input parsers' `if (n < 3) return error_setInpError(...)`) and most
   `continue`s into plain structure; chains of them become `if ... elif ... else`.
3. Any other jump sets a flag (`__ret`, or `__brkN`, `__cntN`, `__swN` for its loop or switch) and the statements
   after it are wrapped in `if not (flags) then`. A jump needs no flag when nothing runs between it and its target:
   a return in tail position only stores `__rv`; the last break of a switch section is dropped.
4. A loop tests its flags before C's condition, `while not (__brk3 || __ret) && cond do`, so the condition is not
   evaluated after a break (C does not evaluate it); a for loop's increment runs after a continue but not after a
   break or a return; a do-while evaluates its condition at the end of the body.

Two details mattered. Deciding whether a jump needs a flag has to be done on the restructured tree, not on the C:
a return that rule 2 moves into tail position at one level may still leave a loop or a guarded block at an outer
one, so tail position is decided per target after the moves. And a switch whose sections all return and which has
a default cannot complete normally; until the translator knew that, three nested switches in climate.c and one in
controls.c looked as if they fell through into the next case, and the next case's code was duplicated after them
(unreachable, but there). In the final engine (951 functions), 1,785 of 2,336 returns, all 476 switch breaks and 85
of 86 continues became structure; 551 returns, the 50 breaks out of loops and 1 continue set a flag
(fsharp/results/emit_stats.txt), and no exception is used for control flow. The F# engine compiled after
four fixes to the translator and gave the same .out and .rpt as EPA on the first four models it ran.

What to carry forward: when the target language lacks a control construct, translate into an intermediate tree and
transform it, rather than emitting text and patching it; and keep the transformation's correctness argument
(which jumps are in tail position, what a loop tests and when) in the translator's header, where the next reader
will look.
