#!/bin/bash
# run_libm_tests.sh [N] - check the Mojo port's math against the system libm (the library EPA calls), bit for bit:
# N random arguments per function over SWMM's ranges plus special values (tools/libm/test/mkvectors.c), an
# edge-case set (tools/libm/test/mkedge.c), and the exact functions and C conversions (test/mkexact.c: sqrt,
# floor, ceil, fabs, negation, the (float), (int) and (long) casts), all replayed by test/libmcheck.mojo, built
# with the engine's flags. The vectors go to MOJO_LIBM_WORK (default: a temporary folder in TMPDIR) and are deleted.
# Needs `mojo` (Mojo 1.2.0) on PATH or MOJO set to it. Written by Claude (Anthropic) for Robert Dickinson; see ../README.md.
set -e
HERE=$(cd "$(dirname "$0")" && pwd); P=$(cd "$HERE/.." && pwd); ROOT=$(cd "$P/.." && pwd)
MOJO=${MOJO:-mojo}
N=${1:-1000000}; W=$(mktemp -d "${MOJO_LIBM_WORK:-${TMPDIR:-/tmp}}/mojolibm.XXXXXX")
gcc -O2 -o "$W/mkvectors" "$ROOT/tools/libm/test/mkvectors.c" -lm
gcc -O2 -o "$W/mkedge" "$ROOT/tools/libm/test/mkedge.c" -lm
gcc -O2 -fno-builtin -o "$W/mkexact" "$HERE/mkexact.c" -lm
"$W/mkvectors" "$N" "$W/vectors.bin" 2> /dev/null > /dev/null
"$W/mkedge" 100000 "$W/edge.bin" 2> /dev/null > /dev/null
"$W/mkexact" "$N" "$W/exact.bin" 2> /dev/null > /dev/null
(cd "$P" && $MOJO build --fp-mode contract=off --target-cpu x86-64 -I . -o "$W/libmcheck" test/libmcheck.mojo 2>&1 | grep -v Crashpad || true)
echo "== $($MOJO --version 2>&1 | grep -v Crashpad): vectors.bin (N = $N per function)"
"$W/libmcheck" "$W/vectors.bin"
echo "== edge.bin"
"$W/libmcheck" "$W/edge.bin"
echo "== exact.bin (N = $N per function)"
"$W/libmcheck" "$W/exact.bin"
rm -rf "$W"
