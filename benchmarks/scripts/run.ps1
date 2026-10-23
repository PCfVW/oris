# SPDX-License-Identifier: MIT OR Apache-2.0
#
# Runs the trace-replay benchmarks (benchmarks/methodology.md) on Windows and writes raw JSON
# lines to benchmarks/results/<version>/<platform>/. run.sh is the Linux/macOS twin.
#
#   pwsh benchmarks/scripts/run.ps1 -Platform windows-x86_64 [-Smoke] [-SkipBuild]
#
# -Smoke: one trace, one repetition — checks the pipeline, measures nothing.
# bench-rust is built without snmalloc (snmalloc-sys does not build here with MSVC) and
# without jemalloc (not supported on MSVC). Needs cl.exe on PATH (a Developer PowerShell)
# for mimalloc's C sources.
# Afterwards: (cd scripts/aggregate; cargo run --release) writes SUMMARY.md.

param(
    [Parameter(Mandatory)][string]$Platform,
    [switch]$Smoke,
    [switch]$SkipBuild
)

$ErrorActionPreference = 'Stop'
$bench = Split-Path $PSScriptRoot -Parent
$version = 'v0.3.0'
$out = Join-Path $bench "results\$version\$Platform"
$target = if ($env:CARGO_TARGET_DIR) { $env:CARGO_TARGET_DIR } else { Join-Path $bench "scripts\target-$Platform" }

function Invoke-Checked([scriptblock]$Block) {
    & $Block
    if ($LASTEXITCODE -ne 0) { throw "failed: $Block" }
}

$savedTargetDir = $env:CARGO_TARGET_DIR
if (-not $SkipBuild) {
    Push-Location (Join-Path $bench 'scripts\tracegen')
    try {
        $env:CARGO_TARGET_DIR = "$target\tracegen"
        # verify first: it regenerates every trace in memory and checks it against the committed
        # checksums, which `generate` would otherwise rewrite before they could be compared.
        Invoke-Checked { cargo run --release -q -- verify }
        Invoke-Checked { cargo run --release -q -- generate --tier bench }
    } finally { Pop-Location }
    Push-Location (Join-Path $bench 'scripts\bench-rust')
    try {
        $env:CARGO_TARGET_DIR = "$target\bench-rust"
        Invoke-Checked { cargo build --release -q --no-default-features --features mimalloc }
    } finally { Pop-Location }
    Push-Location (Join-Path $bench 'scripts\bench-zig')
    try { Invoke-Checked { zig build -Doptimize=ReleaseFast --prefix "$target\bench-zig" } } finally { Pop-Location }
    $env:CARGO_TARGET_DIR = $savedTargetDir
}
$rustBin = "$target\bench-rust\release\bench-rust.exe"
$zigBin = "$target\bench-zig\bin\bench-zig.exe"

New-Item -ItemType Directory -Force $out | Out-Null
$envFile = Join-Path $out 'env.json'
& (Join-Path $PSScriptRoot 'env.ps1') -Platform $Platform | Set-Content -Encoding utf8NoBOM -NoNewline $envFile

$reps = 10
$traces = Get-ChildItem (Join-Path $bench 'traces\*.trace')
if ($Smoke) {
    $reps = 1
    $traces = Get-ChildItem (Join-Path $bench 'traces\synthetic-mixed-1m.trace')
}

function Invoke-Cell($Harness, $Bin, $Allocator, $Trace, $Pass) {
    $file = Join-Path $out "$Harness-$Allocator-$($Trace.BaseName)-$Pass.jsonl"
    $lines = & $Bin --allocator $Allocator --trace $Trace.FullName --pass $Pass --repetitions $reps --env-file $envFile
    if ($LASTEXITCODE -ne 0) { throw "$Harness/$Allocator/$($Trace.BaseName)/$Pass failed" }
    $lines | Set-Content -Encoding utf8NoBOM $file
}

foreach ($trace in $traces) {
    Write-Host "== $($trace.Name)"
    foreach ($allocator in (& $rustBin --list).Split(' ')) {
        foreach ($pass in 'wall', 'latency', 'memory') { Invoke-Cell rust $rustBin $allocator $trace $pass }
        Write-Host "   rust/$allocator"
    }
    foreach ($allocator in 'orisnitsa', 'smp', 'c') {
        foreach ($pass in 'wall', 'latency', 'memory') { Invoke-Cell zig $zigBin $allocator $trace $pass }
        Write-Host "   zig/$allocator"
    }
}
Write-Host "results in $out"
