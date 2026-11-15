# NOTICE — vendored red-black tree library

The Lean files in this directory (`Basic.lean`, `WF.lean`, `Depth.lean`, `Alter.lean`,
`Lemmas.lean`), the umbrella module `../RBTree.lean`, and `README.md` are copied **verbatim**
from the `RBTree` library of
[leanprover-community/batteries-recycling](https://github.com/leanprover-community/batteries-recycling),
which collects modules retired from [Batteries](https://github.com/leanprover-community/batteries)
(the red-black map left Batteries on 2026-10-05; Lean's own `Std.TreeMap`, its replacement, is a
size-balanced tree, not a red-black one).

## Source

| | |
|---|---|
| Repository | `leanprover-community/batteries-recycling` |
| Commit | `b655c13f6e99c9dd1216ffce7c53afbd520553d7` (2026-11-04) |
| Lean toolchain upstream | `leanprover/lean4:v4.36.0-rc2` |
| Copied on | 2026-11-14 |

## Original copyright and licence

Each file keeps its original header verbatim, for example:

```
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
```

`LICENSE` in this directory is upstream's Apache License 2.0, copied verbatim. Apache-2.0 is
compatible with Oris's `MIT OR Apache-2.0`.

## Changes from upstream

**None to the Lean sources.** The one deviation is in how the library is built: upstream's
`lakefile.toml` required Batteries from its `cell-network` branch; `../lakefile.toml` here pins
Batteries to the release tag `v4.36.0-rc2`, the tag matching the library's own toolchain. The
library builds unchanged against it, and the audit (`../Tools/Audit.lean`, `lake exe audit`)
checks every declaration defined in its modules, private and auxiliary ones included, whatever
their names (standard axioms only, no `sorry`).

Any future change to a file here must be recorded in this section, file by file, with its
reason, as `../../Cpp/ERRATA.md` does for the HPHA reference.

## Why vendored

The library is no longer actively maintained upstream, and every package in a Lean build must
share one Lean toolchain: depending on it directly would tie Oris's proofs to whatever toolchain
upstream last used. Vendoring lets Oris move toolchains on its own schedule while keeping the
provenance auditable.
