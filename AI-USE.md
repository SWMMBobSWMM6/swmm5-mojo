# AI use

This repository was made with Claude, Anthropic's AI model (Claude Opus 5.5), in Claude Code sessions in
November 2026, under the direction of Robert (Bob) Dickinson. He found that his Code Rosetta Stone app held no
genuinely translated, working SWMM5 engines beyond the ones made in these sessions and chose the languages: first
Zig, Free Pascal, Kotlin and Scala (replaced by Ruby when this sandbox could not fetch or run a Scala compiler),
then JavaScript, F#, PHP, Perl, Groovy, Lua, Hy and Mojo. He asked that each be checked byte for byte against EPA
SWMM 5.2.4 as the earlier six ports were, created this repository and supplied the model corpus. Responsibility
for publishing the work is his.

**What Claude did.** It wrote the Mojo back end of the translator (`tools/c2x/emit_mojo.py`; the libclang
front end `tools/c2x/front.py` was written earlier for the first six ports), the hand-written runtime that gives the
C library's behaviour (printf, sscanf, strtod, file I/O and the rest), the build and gate scripts, ran
every test, diagnosed and fixed every mismatch, and wrote the README and the lessons. Claude subagents did the
translation and ran the full gate; the main session then checked the result itself (its engine regenerated from a clean checkout and compared byte for byte with the committed one, the compiler installed again from PyPI and the engine built there, then gate run `mojo_main` from that checkout on 45 models drawn at random from the 480 plus the three decks that SAVE and USE `cho.txt`) before publishing.

**How the results were checked.** Mechanically: byte comparison of every `.out` and `.rpt` with EPA 5.2.4 built from
its tag on the 480 gate models, and the runtime compared with glibc directly (lesson 25 is why: a gate can pass
with a runtime that is wrong on inputs the corpus never gives it). No person has yet reviewed the generated code or
the runtime line by line, or rerun the gate on another machine.

`gate/savefiles.py`, which lists the files a deck SAVEs so the gate can restore them, comes from the swmm6-rust
repository (also written by Claude for Bob).
