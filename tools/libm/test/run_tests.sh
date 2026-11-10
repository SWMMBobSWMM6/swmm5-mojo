#!/bin/bash
# run_tests.sh [N]
# Check the TypeScript and Java ports of glibc's math routines bit for bit against the system libm (the
# library EPA's runswmm calls): N random arguments per function over the ranges SWMM uses plus the
# arguments sampled by the census of the 480 gate models (gate/libm_census, if present), and an edge-case
# set (huge trig arguments, negative bases, overflow/underflow, subnormals, domain errors). Also a
# differential test of TypeScript pow's fast path against pow_exact. Needs gcc, node + npx tsc, javac, go.
# Written by Claude (Anthropic); see AI-USE.md.
set -e
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../../.." && pwd)
N=${1:-400000}; W=$ROOT/build/libm_test; mkdir -p "$W/ts" "$W/java/swmm5"
gcc -O2 -o "$W/mkvectors" "$HERE/mkvectors.c" -lm
gcc -O2 -o "$W/mkedge" "$HERE/mkedge.c" -lm
CENSUS=${LIBM_CENSUS_DIR:-}   # optional: the per-model samples written by run_census.sh (163 MB, not kept)
"$W/mkvectors" "$N" "$W/vectors.bin" $CENSUS
"$W/mkedge" 100000 "$W/edge.bin"
cp "$ROOT/ts/src/glibm.ts" "$ROOT/ts/src/glibm_rt.ts" "$HERE/check.ts" "$HERE/powdiff.ts" "$W/ts/"
cat > "$W/ts/tsconfig.json" <<'J'
{ "compilerOptions": { "target": "ES2022", "module": "commonjs", "outDir": "dist", "strict": false, "skipLibCheck": true, "types": ["node"] } }
J
[ -e "$W/ts/node_modules" ] || ln -s "$ROOT/ts/node_modules" "$W/ts/node_modules"
echo "== TypeScript"
(cd "$W/ts" && npx tsc -p . && node dist/check.js "$W/vectors.bin" && node dist/check.js "$W/edge.bin" && node dist/powdiff.js 20)
cp "$ROOT/java/src/swmm5/Glibm.java" "$ROOT/java/src/swmm5/GlibmRt.java" "$HERE/Check.java" "$W/java/swmm5/"
echo "== Java"
(cd "$W/java" && javac -d classes swmm5/*.java && java -cp classes swmm5.Check "$W/vectors.bin" && java -cp classes swmm5.Check "$W/edge.bin") 2>&1 | grep -v '^Picked up'
echo "== Go"
(cd "$ROOT/go" && go run "$HERE/check.go" "$W/vectors.bin" && go run "$HERE/check.go" "$W/edge.bin")

