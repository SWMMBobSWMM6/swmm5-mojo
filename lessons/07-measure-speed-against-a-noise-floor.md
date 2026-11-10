A speed ratio means nothing until you know how far EPA disagrees with itself; run EPA twice in the same shuffle.

The benchmark (gate/bench.py) runs every engine on 12 models, 3 repetitions, in a fresh random order each
repetition, and runs EPA twice. EPA against EPA landed between 0.98 and 1.06 times per model (medians over
repetitions); single pairs ranged from 0.88 to 1.81 (the 1.81 on a run of two hundredths of a second, the
0.88 on one of 0.18 s), which is why each ratio is a median of repetitions. So:

- C++ at 0.94 times EPA is "a few percent faster, just outside the band", not "faster" in general.
- Fortran at 1.26 times (1.13 to 1.40 on every model) is a real cost. A gprof profile of one long model put
  the time in the same engineering routines EPA uses, plus small runtime overheads everywhere (the checked
  double-to-integer conversion ran 13 million times in that run). No single fix was found; it was not
  pursued.
- C# start-up (.NET plus just-in-time compilation) dominates tiny models: 27.7 times EPA on a model EPA runs
  in a hundredth of a second, 2.9 times on the largest. Quote the median and the range, never one number.
- Measure CPU time (user plus system) of the engine process, not wall time, and record start-up separately
  with a `--version` run.

Two process-handling traps from the same work:
- `pgrep -f pattern` and `pkill -f pattern` match the shell that is running the command, because its own
  command line contains the pattern. A wait loop never ends and a kill takes down your own shell. Find the
  PID with `ps -eo pid,args` and an exact match, or record `$!` when you start the job.
- A job started with `nohup ... &` from a tool call can be stopped when the turn ends. Long jobs need the
  harness's background mode, and a runtime limit that fits inside it.
