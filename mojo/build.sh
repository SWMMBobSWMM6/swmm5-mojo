#!/bin/sh
# build.sh - build the Mojo port of EPA SWMM 5.2.4:  bin/runswmm <input> <report> [output]
# Needs the Mojo 1.2.0 compiler: `pip install mojo-compiler==1.2.0 mojo-compiler-mojo-libs==1.2.0` gives `mojo`
# (set MOJO to it if it is not on PATH).
#   --fp-mode contract=off   Mojo's default (contract=fast) fuses a*b+c into one fused multiply-add across
#                            statements; C, as EPA's gcc build compiles it, rounds the product and the sum
#                            separately, so the default would change results in the last bit
#   --target-cpu x86-64      the baseline x86-64 EPA's gcc build targets (no FMA or AVX instruction can appear;
#                            floor becomes a call to glibc's floor)
# The compiler's warnings (about 2,500: zero-initialised locals the C code assigns again, code after a return,
# doc-string style) go to bin/build.log. To regenerate swmm5/engine.mojo from EPA's C first:
#   python3 tools/c2x/emit_mojo.py mojo/swmm5/engine.mojo        (from the repository root)
# Written by Claude (Anthropic) for Robert Dickinson; see README.md.
set -e
cd "$(dirname "$0")"
MOJO=${MOJO:-mojo}
mkdir -p bin
if ! $MOJO build --fp-mode contract=off --target-cpu x86-64 -I . -o bin/runswmm swmm5/main.mojo > bin/build.log 2>&1; then
  grep -v -e Crashpad -e 'warning:' bin/build.log | grep -A3 'error' | head -60
  exit 1
fi
echo "built bin/runswmm with $($MOJO --version 2>/dev/null | grep -v Crashpad) ($(grep -c 'warning:' bin/build.log) compiler warnings in bin/build.log)"
