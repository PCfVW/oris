#!/usr/bin/env bash
# SPDX-License-Identifier: MIT OR Apache-2.0
#
# Runs the trace-replay benchmarks (benchmarks/methodology.md) on Linux or macOS and writes
# raw JSON lines to benchmarks/results/<version>/<platform>/. run.ps1 is the Windows twin.
#
#   scripts/run.sh <platform-label> [--smoke] [--skip-build]
#
# --smoke: one trace, one repetition — checks the pipeline, measures nothing.
# Afterwards: (cd scripts/aggregate && cargo run --release) writes SUMMARY.md.
set -euo pipefail

platform="${1:?usage: run.sh <platform-label> [--smoke] [--skip-build]}"
shift
smoke=false
build=true
for arg in "$@"; do
  case "$arg" in
    --smoke) smoke=true ;;
    --skip-build) build=false ;;
    *) echo "unknown argument $arg" >&2; exit 2 ;;
  esac
done

bench="$(cd "$(dirname "$0")/.." && pwd)"
version="v0.3.0"
out="$bench/results/$version/$platform"
target="${CARGO_TARGET_DIR:-$bench/scripts/target-$platform}"

if $build; then
  (cd "$bench/scripts/tracegen" && CARGO_TARGET_DIR="$target/tracegen" cargo run --release -q -- generate --tier bench)
  (cd "$bench/scripts/tracegen" && CARGO_TARGET_DIR="$target/tracegen" cargo run --release -q -- verify)
  (cd "$bench/scripts/bench-rust" && CARGO_TARGET_DIR="$target/bench-rust" cargo build --release -q)
  (cd "$bench/scripts/bench-zig" && zig build -Doptimize=ReleaseFast --prefix "$target/bench-zig")
fi
rust_bin="$target/bench-rust/release/bench-rust"
zig_bin="$target/bench-zig/bin/bench-zig"

mkdir -p "$out"
"$bench/scripts/env.sh" "$platform" > "$out/env.json"

reps=10
traces=("$bench"/traces/*.trace)
if $smoke; then
  reps=1
  traces=("$bench/traces/synthetic-mixed-1m.trace")
fi

run_cell() { # harness binary allocator trace pass
  local harness="$1" bin="$2" allocator="$3" trace="$4" pass="$5"
  local name
  name="$(basename "$trace" .trace)"
  "$bin" --allocator "$allocator" --trace "$trace" --pass "$pass" --repetitions "$reps" \
    --env-file "$out/env.json" > "$out/$harness-$allocator-$name-$pass.jsonl"
}

for trace in "${traces[@]}"; do
  echo "== $(basename "$trace")"
  for allocator in $("$rust_bin" --list); do
    for pass in wall latency memory; do run_cell rust "$rust_bin" "$allocator" "$trace" "$pass"; done
    echo "   rust/$allocator"
  done
  for allocator in orisnitsa smp c; do
    for pass in wall latency memory; do run_cell zig "$zig_bin" "$allocator" "$trace" "$pass"; done
    echo "   zig/$allocator"
  done
done
echo "results in $out"
