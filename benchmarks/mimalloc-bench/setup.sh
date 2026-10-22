#!/usr/bin/env bash
# SPDX-License-Identifier: MIT OR Apache-2.0
#
# Sets up mimalloc-bench (https://github.com/daanx/mimalloc-bench) with Oris in it, on Linux:
#
#   1. clones mimalloc-bench at the pinned commit below (into $MB_DIR, default ~/mimalloc-bench);
#   2. applies bench.sh.patch, which registers two allocators: `onik` (orisnik) and `onit`
#      (orisnitsa);
#   3. builds the two LD_PRELOAD shims (preload-rust/, preload-zig/) and installs them into
#      mimalloc-bench's extern/oris/;
#   4. builds the comparison allocators and the benchmark programs with mimalloc-bench's own
#      build-bench-env.sh.
#
#   benchmarks/mimalloc-bench/setup.sh
#
# Needs: cargo, zig 0.16.0, git, and the packages step 4 uses. mimalloc-bench can install
# those itself (`build-bench-env.sh packages`, which runs apt with sudo); for the subset
# built here it is enough to have
#
#   sudo apt install -y build-essential cmake autoconf automake libtool ninja-build \
#                       clang lld unzip dos2unix time
set -euo pipefail

readonly MB_COMMIT=391382606681408e34d96ec54e9e6c79805aa3ac   # 2026-10-17
readonly MB_DIR="${MB_DIR:-$HOME/mimalloc-bench}"
readonly here="$(cd "$(dirname "$0")" && pwd)"
# The comparison allocators: mimalloc, jemalloc, snmalloc. `sys` (glibc) needs no build.
readonly ALLOCATORS="mi je sn"

if [ ! -d "$MB_DIR/.git" ]; then
  git clone https://github.com/daanx/mimalloc-bench.git "$MB_DIR"
fi
cd "$MB_DIR"
git checkout -q "$MB_COMMIT"
if git apply --check "$here/bench.sh.patch" 2>/dev/null; then
  git apply "$here/bench.sh.patch"
elif ! git apply --reverse --check "$here/bench.sh.patch" 2>/dev/null; then
  echo "bench.sh.patch neither applies nor is already applied" >&2
  exit 1
fi

(cd "$here/preload-rust" && cargo build --release)
(cd "$here/preload-zig" && zig build -Doptimize=ReleaseFast)
mkdir -p "$MB_DIR/extern/oris"
cp "$here/preload-rust/target/release/liborispreload_rust.so" "$MB_DIR/extern/oris/"
cp "$here/preload-zig/zig-out/lib/liborispreload-zig.so" "$MB_DIR/extern/oris/"

./build-bench-env.sh $ALLOCATORS bench
echo "mimalloc-bench is ready in $MB_DIR; run benchmarks/mimalloc-bench/run.sh"
