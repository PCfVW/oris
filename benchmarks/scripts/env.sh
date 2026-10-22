#!/usr/bin/env bash
# SPDX-License-Identifier: MIT OR Apache-2.0
#
# Prints this machine's benchmark environment as one line of JSON (embedded in every result
# record, so each file is self-describing — benchmarks/methodology.md). Linux and macOS;
# env.ps1 is the Windows twin.
#
#   scripts/env.sh <platform-label>     e.g. linux-wsl2-x86_64
set -euo pipefail
platform="${1:?usage: env.sh <platform-label>}"
root="$(cd "$(dirname "$0")/../.." && pwd)"

json() { python3 -c 'import json,sys; print(json.dumps(sys.argv[1]))' "$1"; }

if [ "$(uname -s)" = "Linux" ]; then
  cpu="$(grep -m1 'model name' /proc/cpuinfo | cut -d: -f2- | sed 's/^ *//')"
  ram_kb="$(grep MemTotal /proc/meminfo | awk '{print $2}')"
  ram_gb=$(( (ram_kb + 524288) / 1048576 ))
  os="$(. /etc/os-release && echo "$PRETTY_NAME")"
  governor="$(cat /sys/devices/system/cpu/cpu0/cpufreq/scaling_governor 2>/dev/null || echo unknown)"
else
  cpu="$(sysctl -n machdep.cpu.brand_string)"
  ram_gb=$(( $(sysctl -n hw.memsize) / 1073741824 ))
  os="macOS $(sw_vers -productVersion)"
  governor="n/a"
fi
cores="$(getconf _NPROCESSORS_ONLN)"
kernel="$(uname -r)"
rustc="$(rustc --version 2>/dev/null || echo none)"
zig="$(zig version 2>/dev/null || echo none)"
cc="$( (cc --version 2>/dev/null || echo none) | head -1)"
commit="$(git -C "$root" rev-parse --short HEAD)"
dirty="$(git -C "$root" status --porcelain | grep -qv '^??' && echo true || echo false)"
date="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

printf '{"platform":%s,"os":%s,"kernel":%s,"cpu":%s,"logical_cores":%s,"ram_gb":%s,"cpu_governor":%s,"rustc":%s,"zig":%s,"cc":%s,"commit":%s,"dirty":%s,"date":%s,"host":"redacted"}\n' \
  "$(json "$platform")" "$(json "$os")" "$(json "$kernel")" "$(json "$cpu")" "$cores" "$ram_gb" \
  "$(json "$governor")" "$(json "$rustc")" "$(json "$zig")" "$(json "$cc")" "$(json "$commit")" "$dirty" "$(json "$date")"
