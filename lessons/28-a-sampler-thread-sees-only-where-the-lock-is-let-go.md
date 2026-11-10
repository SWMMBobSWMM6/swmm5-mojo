A profiler thread inside an interpreter with a global lock samples only the places where the program lets go of the lock: it put 28% of a Ruby run in `write`.

No profiler gem was available for the Ruby port, so the first profile came from a thread that woke every 2 ms and
read the main thread's backtrace. It said 28.4% of the time of Hydraulics/InfoSewer_ICM.inp went to `write`
(the `.out` file's results, through `c_fwrite_arr`). The number was an artefact. MRI runs one Ruby thread at a
time under its global VM lock; a thread that wakes up must wait for the lock, and the main thread hands it over
only at a blocking call (a `write` that reaches the kernel) or when its 100 ms time slice runs out. So the sampler
looked almost only at the moments the engine was writing.

A second profiler sends the process a signal every 3 ms from a forked child; Ruby runs the signal handler on the
main thread at its next safe point (a method call, a loop's back edge), and the handler records
`caller_locations`. Its profile of the same run put `write` below 1% and the time where it belongs: 91% under
`dynwave_execute`, 60% in `dwflow_findConduitFlow` and what it calls. It is still biased toward safe points, so
it over-counts calls into C methods such as `Integer#to_f` and `Float#/`; a stopwatch on those (3 million calls)
showed them at 10 to 15 ns each, against about 100 ns for `Box.new`, which the profile had ranked lower.

What it led to: the boxes. C locals whose address is passed to another function (`findSurfArea(j, ..., &h1, &h2,
&y1, &y2)`) live in Box objects, and the first engine allocated four of them on every call of
`dwflow_findConduitFlow` and more in `findSurfArea`. `emit_ruby.py` now finds the functions that can be active
twice at once (cycles in the call graph, counting a call through a function pointer as a call to every function
whose address is taken: 21 functions, and of the 113 with boxed locals only `getTree`, the recursive-descent
parser in mathexpr.c) and gives every other function's boxes a single allocation at load time. On InfoSewer_ICM.inp the objects allocated fell from 36.5 to
19.3 million, garbage collections from 4,714 to 1,312, and CPU time from 57.8 s to 51.6 s (one run each; with a
second change made at the same time, a divisor that is not a plain variable kept in a temporary instead of passed to
a helper method, interleaved A/B runs on four models gave 0 to 10%). A real but modest gain: the interpreter's own
work, spread over every line, is the cost, and no single fix removes it.

What to carry forward: know how your profiler gets its samples before believing it. In a language with a global
lock, sample from outside the lock (signals, or the operating system's profiler), confirm a surprising hot spot
with a stopwatch on that one operation, and treat the cost of a call into the runtime as something to measure, not
something to read off a profile.
