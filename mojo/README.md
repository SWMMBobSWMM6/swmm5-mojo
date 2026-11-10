# swmm5-mojo

EPA SWMM 5.2.4 in Mojo, written by a translator that reads EPA's C, and judged against EPA itself: the binary
`.out` file byte for byte, and the `.rpt` report line for line except the three lines that print the wall clock.

**Result: 480 of 480 gate models identical to EPA 5.2.4**, in the first full gate (run mojo_1, 9 November 2026) and
again in an independent rerun from a clean checkout, with the engine regenerated and rebuilt there (mojo_v): every
`.out` byte-identical, every `.rpt` identical except the three clock lines, exit code 0 on every model, as EPA's. The
compiled engine runs at about EPA's speed (see Speed).

It is not a new engine and not a wrapper: there is no C in it and it calls no other port. Every number it writes is
EPA 5.2.4's, including the results of EPA's own defects wherever EPA's behaviour is defined
(`lessons/02-epa-defects-found.md`). Mojo is one of the eight languages of the second wave of Bob Dickinson's Code
Rosetta Stone app.

## The parity contract

The same as the earlier ports' (see `go/` or the swmm5-go repository): EPA SWMM 5.2.4 built from the USEPA v5.2.4
tag with gcc 13.3 `-O2` on x86-64 Linux with glibc 2.39 (`ref/Makefile`), on a processor with FMA and AVX2; each
model run in its own folder; pass = `.out` byte-identical (when EPA writes one) and `.rpt` identical after removing
`Analysis begun on`, `Analysis ended on` and `Total elapsed time`, the exit code the same (EPA's command line always
exits 0). When an input error stops EPA before it writes results, the engine must not write a results file either.
Corpus: the 480 gate models of `gate/models_all.tsv` from SWMMBobSWMM6/1729-SWMM5-Models-2030.

## Build and run

Requires the **Mojo 1.2.0** compiler, `Mojo 1.2.0 (2016d0cd)`, from PyPI:
`pip install mojo-compiler==1.2.0 mojo-compiler-mojo-libs==1.2.0` (an 82 MB and a 3.5 MB wheel, 272 MB installed:
the compiler and the standard library; the `mojo` package adds the debugger and formatter, which the build does not
need). It was installed with `pip install --target` into a folder in memory and run as `PYTHONPATH=<that folder>
<that folder>/bin/mojo`. The engine links against glibc only.

```sh
mojo/build.sh                                        # about a minute; MOJO=<path to mojo> if it is not on PATH
mojo/bin/runswmm model.inp model.rpt model.out
```

The build is `mojo build --fp-mode contract=off --target-cpu x86-64 -I mojo -o mojo/bin/runswmm
mojo/swmm5/main.mojo`:

- `--fp-mode contract=off`: **Mojo fuses `a*b + c` into one fused multiply-add by default** (`contract=fast`, "like
  Clang's -ffp-contract=fast", across statements). C as EPA's gcc build compiles it rounds the product and the sum
  separately; with the default a result can change in the last bit. `objdump -d` of the built engine shows no FMA
  instruction (`vfmadd`, `vfmsub`, `vfnmadd`, `vfnmsub`): 0.
- `--target-cpu x86-64`: the baseline x86-64 that EPA's gcc build targets (Mojo's default is the host CPU); no AVX
  instruction appears, and `floor` becomes a call to glibc's `floor`.

The compiler prints about 2,500 warnings (locals zero-initialised that the C code assigns again, code after a
`return`, doc-string style); `build.sh` writes them to `bin/build.log`.

To regenerate the engine: `python3 tools/c2x/emit_mojo.py mojo/swmm5/engine.mojo` from the repository root (needs
`pip install libclang==18.1.1` and the clang 18 headers at `/usr/lib/llvm-18/lib/clang/18/include`; about 20 s).

## How it was made

`tools/c2x/front.py` parses EPA's 54 C files with libclang; `tools/c2x/emit_mojo.py` (1,706 lines) writes the engine
as one module, `mojo/swmm5/engine.mojo` (38,032 lines, generated). Mojo has raw pointers, fixed-width integers
that wrap, IEEE floats and value structs, so the translation keeps C's data and its pointers, as the Zig port does:
the Mojo back end subclasses the Zig back end (`emit_zig.py`) for its naming, its classification of C types, its
folding of constant expressions and its facts about control flow (which statements can complete), and writes Mojo's
statements, which are Python's. Everything else is written out in the emitter's header; the main points:

- **Types.** `int`, `unsigned`, `long`, `unsigned long`, `short`, `char` are `Int32`, `UInt32`, `Int64`, `UInt64`,
  `Int16`, `Int8` (Mojo's `+ - *` wrap on overflow, as x86 does); `double` and `float` are `Float64` and `Float32`;
  a pointer is `P[T]`, an alias for `Pointer[T, MutUntrackedOrigin]`, and NULL is `rt.null[T]()`; a struct is a Mojo
  struct, copied with `.copy()` where C copies it; the one union (`TInfil`) is a struct of raw words read as each of
  its members.
- **Arrays.** An array object is its storage, and as a value the pointer to its first element; multi-dimensional
  arrays are flattened (`Params[code][C]` is `Params.unsafe_offset(Int(code) * 5)[unsafe_offset=C]`). An array that
  is a field of a struct is a block of raw words inside the struct, so copying the struct copies the array.
- **No global variables.** Mojo 1.2 rejects them ("global variables are not supported"). All 626 of EPA's globals
  and its static locals are fields of one `Globals` struct, allocated and given their C initial values at start-up
  (`new_globals`), and every translated function takes a pointer to it as its first parameter, `G`. The runtime's
  own state (standard output, `strtok`'s position) hangs off `G` too.
- **Function pointers.** Mojo 1.2 cannot keep a function value in a struct field, so a C function pointer is a
  number: each function whose address is taken gets one, and a call through a pointer goes to a generated
  dispatcher for its signature: six signatures, 20 functions.
- **Locals whose address is taken** (and every local array and struct) live on the engine's own stack, a block of
  heap memory in the runtime (`rt.salloc`; the function gives the space back before it returns). They were Mojo stack
  slots (`stack_allocation`) at first, which broke: Mojo marks a call `tail` (to LLVM: the callee touches none of the
  caller's stack) even when the slot's address, as an untracked pointer, is one of its arguments, so LLVM read the slot
  after the call as if nothing had written it. The first model failed on its time strings (`datetime_strToTime`
  passes `&endptr` to `strtod`); see `lessons/42-mojo-tail-calls-hide-writes-to-the-stack.md`.
- **Integers.** C's `/` and `%` on signed integers truncate, Mojo's `//` and `%` floor: `rt.idiv32`, `rt.irem32`
  and the 64-bit ones. A shift by a computed count masks the count as x86 does (`rt.shl32` ...). `(int)` of a
  double is `rt.d2i32`, x86-64's `cvttsd2si` (NaN or out of range gives INT_MIN); Mojo's own conversion is LLVM's
  `fptosi`, whose result for those arguments is undefined.
- **C expressions with side effects used as values.** `x = e`, `x++` and `x += e` used inside an expression become
  `rt.set(x, e)`, `rt.postinc(x)` and so on; Mojo passes the place by reference (a `mut` argument), so it is
  evaluated once. The comma operator never appears as a value in EPA's code.
- **Statements.** `switch` becomes an `if`/`elif` chain, or, where a case falls through or a `break` leaves a case
  early, a one-pass `while True:` loop with a fall-through flag; `for` becomes `while` with the increment repeated
  before every `continue`; `do`/`while` is `while True: ...; if not cond: break`. Every local is declared at the top
  of its function and zero-initialised (Mojo scopes a `var` to its block).
- **Literals.** A `double` constant is `Float64(<shortest decimal>)`: Mojo rounds a literal once to the nearest
  double (checked on 3,011 values, subnormals and halfway cases included, against Python's `float`); a `float`
  constant is written from its bits, because Mojo's `Float32(1e-45)` gave 0 where C gives the smallest subnormal.
  Mojo writes `"\xb3"` in a string literal as the character U+00B3 in UTF-8 (two bytes), so the four report headers
  with a byte above 127 (`1000 ft\xb3`) are built from their bytes at start-up.

When the port disagreed with EPA, the fix went into the translator or the runtime, never into the generated file.

## The runtime and the math library

The runtime, `mojo/swmm5/rt.mojo` (2,231 lines), follows the Zig port's runtime in design and is written in Mojo:

- **printf/snprintf**: every conversion written here; `%f`, `%e` and `%g` expand the double exactly with big
  integers (its binary value times a power of five) and round the decimal digits half to even, as glibc does.
- **strtod/atof/sscanf**: glibc's syntax (decimal, hexadecimal, `inf`, `nan(...)` with its payload); the value of a
  decimal number by Clinger's fast path where it is exact (at most 15 digits and a power of ten up to 10^22), and
  otherwise by exact big-integer division to 55 bits plus a sticky bit, then rounding half to even (subnormals and
  overflow included); sscanf's `%f` into a C `float` rounds once from the decimal, as glibc's `strtof` does.
- Checked against glibc 2.39 by `mojo/test/run_crtcheck.sh` (the 1,394,252 cases from `tools/crt/test/mkfmt.c` the
  other runtimes replay): **1 differs**, `%#g` of 999999.5 (glibc `1.e+06`, the port `1.00000e+06`), the case every
  runtime reports; SWMM never uses `%#g`. And 200,000 cases of sscanf's `%f` into a float (`mojo/test/mkstrtof.c`):
  **0 differ**. Output: `mojo/results/crtcheck_result.txt`.
- **Math.** `exp`, `log`, `log10`, `pow`, `sin`, `cos`, `tan`, `asin`, `acos` and `atan` are glibc's own, reached
  through `external_call` from wrappers marked `@no_inline`, so LLVM cannot fold a call with constant arguments (it
  did fold `pow(1.1, 2.5)` at compile time in a test) or rewrite one. The built engine imports `exp@GLIBC_2.29`,
  `log@GLIBC_2.29`, `pow@GLIBC_2.29` and the others at GLIBC_2.2.5: the versions EPA imports (`nm -D` against
  `ref/runswmm`). `fabs` clears the sign bit; `sqrt` and `floor` are Mojo's (an instruction, and with the baseline
  target a call to glibc's `floor`); the engine calls no `ceil`, which the check below covers anyway. Checked bit for bit, NaN signs and payloads included, by
  `mojo/test/run_libm_tests.sh`, as the engine computes each one: 10,000,416 random arguments over SWMM's ranges plus
  special values (`tools/libm/test/mkvectors.c`), 3,300,000 edge cases (`mkedge.c`) and 8,000,360 cases
  (`mojo/test/mkexact.c`) for `sqrt`, `floor`, `ceil`, `fabs`, negation, `(float)`, `(int)` and `(long)`:
  **0 differ** (`mojo/results/libm_tests.txt`).
- **stdio** over `open`, `pread`, `pwrite`, `write`, `lseek` and `close`, with C's file position, end-of-file flag
  and buffering; memory from glibc's `calloc` with a size header (every block zero-filled, for `realloc`); time,
  `mkstemp` and `realpath` written here. Those system calls and the allocator are the only other things taken from
  glibc.

## How it was checked

| Run | Models | Engine | Result |
|---|---|---|---|
| (development) | 40 decks drawn at random from the fast models, copied to a scratch folder | working tree | 40 identical, after the stack fix (the first build failed the first model it ran: see Locals above) |
| mojo_1 | all 480, one at a time | working tree, commit 325f04d's files, `mojo/build.sh` | **480 identical**, 186 s of engine time |
| **mojo_v** | **all 480, one at a time** | **a clean checkout of commit 325f04d (`git archive` into a scratch folder), `tools/c2x/emit_mojo.py` run again there (its `engine.mojo` byte-identical to the committed one) and the engine built there with `build.sh`** | **480 identical**, 181 s |
| mojo_main | 48: 45 drawn at random from the 480, plus the three decks that SAVE and USE `cho.txt` | a clean `git clone` of commit b988548, `engine.mojo` regenerated there (byte-identical), the compiler installed again from PyPI and the engine built there | 48 identical |

The two runs are the first full gate and the independent rerun the brief asks for; records (JSON and logs) in
`mojo/results/`, queue and run times in `mojo/gate/`. Before either, the runtime and math checks above.

The main session then checked the result itself: a clean `git clone` of commit b988548, `tools/c2x/emit_mojo.py` run
again there (`engine.mojo` byte-identical to the committed one), Mojo 1.2.0 installed again from PyPI
(`mojo-compiler==1.2.0`, `mojo-compiler-mojo-libs==1.2.0`, with `pip install --target` into a folder in memory) and
the engine built in that clone with `mojo/build.sh` (53 s; no fused multiply-add instruction in the binary), then
gate run mojo_main from that clone on 48 models: 45 drawn at random (seed 20261109) from the 480, plus
`Hydrology/save_rtk_long.inp`, `one_sub_one_rdii_node.inp` and `Use_SeasonalRDIIn.inp`, the decks that SAVE and USE
`cho.txt`. All 48 identical, exit code 0 on each, 16.4 s of engine time (the longest
Hydrology/sewer_rdii_problem.inp, 8.2 s); ids in `mojo/gate/ids_main_check.txt`, record in
`mojo/results/mojo_main.json`. `cho.txt` was unchanged afterwards.

All runs: `python3 gate/gate.py NAME "$PWD/mojo/runswmm_saves.sh" --ids IDS -j 1 --timeout 1800 --prune`, inside
`flock` on the shared corpus lock, with the output folder in `/dev/shm` (`lessons/22`), through
`mojo/gate/run_chunk.sh`. `runswmm_saves.sh` (the Ruby port's wrapper with the engine changed) backs up every file a
deck SAVEs (listed by the swmm6-rust repository's `gate/savefiles.py`, called read-only), including the backslash
spelling of `[LID_USAGE]` report files (`lessons/29`), and restores them after the run.
`Hydrology/cho.txt` was 1,114,474 bytes, md5 5b0ca1fe78588202fa779dbfa417b089, before and after.

## Speed

The gate's clock: 186 s of engine time for all 480 models in mojo_1 (181 s in mojo_v), median 0.05 s; the longest
were EPA/72_H&H_Elements(2).inp, 27.6 s, and Hydrology/SCANLON.inp, 20.6 s. Against EPA's own times from the
reference run (made earlier, on a differently loaded machine, so a rough guide only), the median ratio is 0.73 (103
models where EPA took 0.1 s or more; range 0.33 to 5.81); against the Zig port's gate times (zig_5), 1.43 (79 models
of 0.1 s or more there; range 0.70 to 2.13). Start-up (`mojo/bin/runswmm --version`) takes under 0.01 s. No
interleaved benchmark was run (lessons/07), so these are the gate's numbers, not a measurement of speed.

## What this does not show

- That SWMM is right: identical to EPA means EPA's answers, good or bad.
- Other platforms: the port calls the system libm, so on another machine it should follow EPA built there; only
  x86-64 Linux with glibc 2.39 was run, with Mojo 1.2.0.
- A checked run: Mojo's `Pointer` is unchecked, like C's; an overrun that changes no output would not show.
- Later Mojo releases: the language changes fast. In 1.2.0 `UnsafePointer` is already a deprecated alias of
  `Pointer`, positional indexing and `+` on pointers are deprecated (the engine uses `unsafe_offset`), and `alloc`
  without a `Layout` is deprecated. The parts most likely to need changes with a newer compiler: the pointer type
  and its null (`Pointer` is documented as non-nullable; the engine makes NULL from address 0 and tests it with
  `Int(p) == 0`), `rt.salloc`'s reason for being (the `tail` marking), the `Globals` struct (if Mojo gains global
  variables), the numbered function pointers (if a struct can hold a function), and `external_call`.
- Paths no gate model exercises: streets and inlets (one deck, which stops on input errors), climate files,
  USE HOTSTART, USE INFLOWS, USE RUNOFF; the stepping API is translated but only the command line was gated.
- Speed beyond the gate's own clock: no interleaved benchmark against EPA was run (lessons/07).
- No person has reviewed the generated code line by line; the evidence is the gate and the runtime checks.

## Licence and credit

EPA SWMM is a work of the U.S. Environmental Protection Agency and is in the public domain; its engine is Lewis
Rossman's design, and this port keeps every algorithm as he wrote it. The port contains no glibc code: it calls the
system's libm and a few system calls (glibc, LGPL-2.1-or-later, `ref/LGPL-2.1.txt`; see the swmm5-go repository's
`LICENSES`) as a shared library at run time, as EPA's own build does. Mojo's compiler is Modular's (its licence is
Modular's community licence; the standard library is Apache-2.0 with LLVM exceptions). No licence has been chosen
yet for the translator and the runtime.

## AI use

The translator back end (`tools/c2x/emit_mojo.py`), the runtime (`mojo/swmm5/rt.mojo`), the command line
(`mojo/swmm5/main.mojo`), the generated engine, the build script, gate wrapper and chunk runner, the runtime and math
checks, lessons 42 and 43 and this README were written by Claude (Anthropic's AI model, Claude Opus 5.5) in a Claude Code
session on 9 November 2026, for Robert (Bob) Dickinson, who asked for Mojo in his Code Rosetta Stone app ("even [if]
you cannot run the code like mojo i would still like to see the code in a repo for some other day") and set the
byte-for-byte standard. The compiler could be installed and run here, so the port was built and gated like the
others. The runtime's design follows the Zig port's (also Claude's work). Claude ran every gate and check reported
here. The checks are mechanical; no person has yet reviewed the code.
