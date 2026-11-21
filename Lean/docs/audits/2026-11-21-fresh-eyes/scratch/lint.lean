-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Tools.Audit
#eval do
  let r ← Oris.AuditTool.lintFile "scratch/evil.lean"
  IO.println s!"{r.size} findings: {r}"
