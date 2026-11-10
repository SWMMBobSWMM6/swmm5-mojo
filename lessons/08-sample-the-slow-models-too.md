The slow-model sample found a Python bug the 451 fast models never reached; run a sample of everything you skip.

The Python engine passed all 451 fast models, then crashed on Hydrology/Horton_Continuous_Model.inp in the
slow sample:

    File "py/swmm5/engine.py", line 21917, in parseStdLine
      n = rt.sscanf(line, L350, token, year, month, day, hour, minute, value)
    File "py/swmm5/crt.py", line 631, in sscanf
      a[1].v = v if lmod > 0 else _i32(v)
    TypeError: 'Box' object is not subscriptable

The C it came from (rain.c:1070) passes pointers that are already pointers, not `&x`:

    int parseStdLine(char *line, int *year, int *month, int *day, int *hour, int *minute, float *value)
    ...
    n = sscanf(line, "%s %d %d %d %d %d %f", token, year, month, day, hour, minute, value);

The Python back end wrapped `&x` arguments as `('i', box)` for the runtime's sscanf, but passed a bare
`int *` parameter as the box alone. The fix went into `tools/c2x/emit_py.py` (`vararg`): any pointer to a
number gets the same `(tag, box)` pair. Regenerating changed exactly four calls (climate.c readUserFileLine
and readGhcndFileLine, rain.c readNwsOnlineValue and parseStdLine), every one a call that would always have
crashed, which is why no passing model could have reached them. The whole Python gate was rerun anyway.

The C# back end had met the same construct first: its first gate run (gate/csharp_run1.txt) failed
Horton_Continuous_Model.inp at the same report line, and the fix went into emit_cs.py as a special case for
pointer parameters passed to sscanf (`R.Slot` plus a copy-back, because C# lambdas cannot capture ref
parameters). The Python back end, written afterwards, did not inherit it. This is the second time a fix made
in one back end had to be rediscovered in the next (defect 1 in lessons/02 was the first); a construct that
needs special handling belongs in a list the front end hands to every back end. Two habits it argues for: sample the models you skip for
time, and when a back end special-cases a construct, grep the C for every other spelling of it.
