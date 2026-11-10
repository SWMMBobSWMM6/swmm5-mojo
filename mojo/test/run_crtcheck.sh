#!/bin/sh
# run_crtcheck.sh - check the Mojo runtime's printf, strtod and sscanf against the system glibc: tools/crt/test/mkfmt.c
# writes about 1.4 million reference cases from glibc, test/crtcheck.mojo replays them through swmm5/rt.mojo and
# counts the differences; then 200,000 cases of sscanf's %f into a float (test/mkstrtof.c, test/strtofcheck.mojo).
# Both programs are built with the engine's flags. The cases go to a temporary folder in TMPDIR and are deleted.
# Needs `mojo` (Mojo 1.2.0) on PATH or MOJO set to it. Written by Claude (Anthropic) for Robert Dickinson; see ../README.md.
set -e
cd "$(dirname "$0")/.."
MOJO=${MOJO:-mojo}
T=$(mktemp -d "${TMPDIR:-/tmp}/mojocrt.XXXXXX")
gcc -O2 -o "$T/mkfmt" ../tools/crt/test/mkfmt.c -lm
gcc -O2 -o "$T/mkstrtof" test/mkstrtof.c
$MOJO build --fp-mode contract=off --target-cpu x86-64 -I . -o "$T/crtcheck" test/crtcheck.mojo > "$T/b1.log" 2>&1 || { cat "$T/b1.log"; exit 1; }
$MOJO build --fp-mode contract=off --target-cpu x86-64 -I . -o "$T/strtofcheck" test/strtofcheck.mojo > "$T/b2.log" 2>&1 || { cat "$T/b2.log"; exit 1; }
"$T/mkfmt" > "$T/fmt.txt"
"$T/crtcheck" "$T/fmt.txt"
"$T/mkstrtof" 200000 > "$T/strtof.txt"
"$T/strtofcheck" "$T/strtof.txt"
rm -rf "$T"
