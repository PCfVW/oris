# SPDX-License-Identifier: MIT OR Apache-2.0
#
# Prints this machine's benchmark environment as one line of JSON (embedded in every result
# record, so each file is self-describing — benchmarks/methodology.md). Windows; env.sh is
# the Linux/macOS twin.
#
#   pwsh benchmarks/scripts/env.ps1 -Platform windows-x86_64

param([Parameter(Mandatory)][string]$Platform)

$ErrorActionPreference = 'Stop'
$root = Split-Path (Split-Path $PSScriptRoot -Parent) -Parent
$cpu = Get-CimInstance Win32_Processor | Select-Object -First 1
$sys = Get-CimInstance Win32_ComputerSystem
$os = Get-CimInstance Win32_OperatingSystem
$plan = (powercfg /getactivescheme) -replace '^.*\((.*)\).*$', '$1'
$rustc = try { (rustc --version) } catch { 'none' }
$zig = try { (zig version) } catch { 'none' }
$dirty = [bool](git -C $root status --porcelain | Where-Object { $_ -notmatch '^\?\?' })

[ordered]@{
    platform      = $Platform
    os            = "$($os.Caption) $($os.Version)"
    kernel        = $os.BuildNumber
    cpu           = $cpu.Name.Trim()
    logical_cores = [int]$sys.NumberOfLogicalProcessors
    ram_gb        = [math]::Round($sys.TotalPhysicalMemory / 1GB)
    cpu_governor  = "power plan: $plan"
    rustc         = $rustc
    zig           = $zig
    cc            = 'msvc (cl) for bench-rust and mimalloc; zig c_allocator: the C runtime Zig links (mingw-w64 UCRT)'
    commit        = (git -C $root rev-parse --short HEAD)
    dirty         = $dirty
    date          = (Get-Date).ToUniversalTime().ToString('yyyy-MM-ddTHH:mm:ssZ')
    host          = 'redacted'
} | ConvertTo-Json -Compress
