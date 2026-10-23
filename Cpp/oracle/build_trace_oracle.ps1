# SPDX-License-Identifier: MIT OR Apache-2.0
#
# Builds trace_replay.exe: the 2007 HPHA allocator, patched with letopis.patch in a scratch
# copy, linked with trace_replay.cpp. The reference files ../hpha.h and ../hpha.cpp are never
# modified (see ../NOTICE.md).
#
#   pwsh Cpp/oracle/build_trace_oracle.ps1 [-OutDir <dir>]
#
# Needs MSVC's cl.exe with its environment (a Developer PowerShell, or vcvars64.bat run first;
# CI uses ilammy/msvc-dev-cmd) and git (for `git apply`). Prints the path of the executable.
#
# The build is the non-debug allocator by construction: no /D_DEBUG and no debug CRT
# (/MTd, /MDd), either of which would turn on hpha.h's DEBUG_ALLOCATOR and its 16-byte guard
# reservation — shifting every size class away from what both ports' records describe. HPHA's
# asserts stay on (no /DNDEBUG): a trace that trips one is a finding, not noise.

param(
    [string]$OutDir = (Join-Path ([System.IO.Path]::GetTempPath()) 'oris-trace-oracle')
)

$ErrorActionPreference = 'Stop'
$oracle = $PSScriptRoot
$cpp = Split-Path $oracle -Parent

# A fresh scratch directory *outside* any git work tree, so `git apply` acts as plain
# `patch` there (inside a repository it would resolve paths against the repository root).
if (Test-Path $OutDir) { Remove-Item -Recurse -Force $OutDir }
New-Item -ItemType Directory -Force $OutDir | Out-Null

# The patch is written against the committed (LF) blobs; a Windows checkout may hold CRLF
# copies (Cpp/** is -text), so normalize while copying.
foreach ($name in 'hpha.h', 'hpha.cpp') {
    $text = [System.IO.File]::ReadAllText((Join-Path $cpp $name)) -replace "`r`n", "`n"
    [System.IO.File]::WriteAllText((Join-Path $OutDir $name), $text)
}

Push-Location $OutDir
try {
    git apply --check (Join-Path $oracle 'letopis.patch')
    if ($LASTEXITCODE -ne 0) { throw 'letopis.patch no longer applies to ../hpha.h/../hpha.cpp' }
    git apply (Join-Path $oracle 'letopis.patch')
    if ($LASTEXITCODE -ne 0) { throw 'git apply failed' }

    $exe = Join-Path $OutDir 'trace_replay.exe'
    cl /nologo /EHsc /O2 /DWIN32 /D_CRT_SECURE_NO_WARNINGS /W3 "/I$OutDir" "/I$oracle" `
        (Join-Path $oracle 'trace_replay.cpp') (Join-Path $OutDir 'hpha.cpp') `
        "/Fe:$exe" "/Fo:$OutDir\" | Out-Host
    if ($LASTEXITCODE -ne 0) { throw 'cl failed' }
    Write-Output $exe
}
finally {
    Pop-Location
}
