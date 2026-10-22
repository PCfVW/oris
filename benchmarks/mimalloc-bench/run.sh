#!/usr/bin/env bash
# SPDX-License-Identifier: MIT OR Apache-2.0
#
# Runs mimalloc-bench (set up by setup.sh) on glibc, mimalloc, jemalloc, snmalloc and both
# Oris shims, and stores the raw results and a summary under
# benchmarks/results/<version>/mimalloc-bench/.
#
#   benchmarks/mimalloc-bench/run.sh [<platform-label>] [-r=<repeats>]
#
# The tests are mimalloc-bench's self-contained programs (built by `build-bench-env.sh
# bench`). The ones that need a large external project (lean, redis, rocksdb, ghostscript,
# lua, linux, z3, spec) and rbstress (ruby) are left to the full run v1.0.0 plans.
set -euo pipefail

readonly MB_DIR="${MB_DIR:-$HOME/mimalloc-bench}"
readonly here="$(cd "$(dirname "$0")" && pwd)"
readonly bench="$(cd "$here/.." && pwd)"
platform="${1:-linux-wsl2-x86_64}"
repeats="${2:--r=3}"
readonly version="v0.3.0"
readonly out="$bench/results/$version/mimalloc-bench"
readonly allocators="sys mi je sn onik onit"
readonly tests="cfrac espresso barnes larson-sized mstress rptest alloc-test sh6bench sh8bench \
xmalloc-test cscratch cthrash glibc-simple glibc-thread malloc-large mleak"

mkdir -p "$out"
"$bench/scripts/env.sh" "$platform" > "$out/env.json"
cd "$MB_DIR/out/bench"
# shellcheck disable=SC2086
../../bench.sh $allocators $tests "$repeats" 2>&1 | tee "$out/bench-log.txt"
cp benchres.csv "$out/benchres.csv"
python3 "$here/summarize.py" "$out"
