A list of files to protect must name them the way the engine under test names them: the shared SAVE-file lister follows OpenSWMM 6's path rule, and EPA 5.2.4 writes four LID report files it never lists.

Every port's gate runs through a wrapper that asks the swmm6-rust repository's `gate/savefiles.py` which files a
deck writes, backs them up, and restores them after the run. For `[LID_USAGE]` report files the lister turns `\`
into `/`, as OpenSWMM 6's PathResolver does, and prints, for LID/w_wo_GR_2Subcatchments.inp,

    .../LID/C:/Users/dickinre/Desktop/groof.txt

EPA 5.2.4 does no such thing. It opens the name as written, and on Linux `C:\Users\dickinre\Desktop\groof.txt` is
one relative file name, backslashes included, created in the deck's folder. The wrapper backed up a path that never
exists and left the real file unprotected, so every gate run of every port that used the wrapper (Zig, Pascal,
Kotlin, and the Ruby port's runs before rb_5) rewrote four untracked report files in `LID/`: `groof.txt`, `bob.txt`,
`lid_output.txt` and `drain_out.txt` under their backslash names, written by w_wo_GR_2Subcatchments.inp,
w_wo_IT_2Subcatchments.inp, w_wo_BC_2Subcatchments_Mod_GA_OpenAI.inp and Broomfield LID Underdrain Example US
units.inp. `git status` in the corpus shows them, next to
the SAVE files of `[FILES]` sections, which the lister does spell correctly.

Nothing was damaged: EPA's own build, run on copies of the four decks in a scratch folder, writes files
byte-identical to the four in `LID/`. That check doubles as one the gate does not make, because the gate compares
only `.rpt` and `.out`: the last run to write them was the Ruby port's (rb_4), so its LID report files are EPA's too.
`ruby/runswmm_saves.sh` now backs up and restores both spellings.

A second wrapper trap from the same work: `gate.py` enforces its timeout by killing its own child, which is the
wrapper, not the engine. A slow engine killed that way keeps running as an orphan, still writing into the result
folder and holding a core, and the wrapper never restores anything. The Ruby wrapper now `exec`s the engine when a
deck has nothing to back up (none of the slow models does), so the timeout kills the engine itself.

What to carry forward: when a test harness protects files on behalf of a program, derive the file names from the
program's own rules (here EPA's: the string as written, relative to the working folder), not from another
implementation's, and check after a run that the working tree has no file the harness did not expect.
