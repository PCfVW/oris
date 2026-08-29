# NOTICE — HPHA reference source

The files in this directory (`hpha.h`, `hpha.cpp`) are Dimitar Lazarov's original HPHA implementation, dated 2007. They are included here for reference: the Rust (`orisnik`) and Zig (`orisnitsa`) ports diff against this canonical source, and the cross-language invariant described in [`../ROADMAP.md`](../ROADMAP.md) is defined relative to it.

## Original copyright

```
Copyright (c) 2007, Dimitar Lazarov, Luxoflux
dimitar.lazarov@usa.net
```

The original header is preserved verbatim in both `hpha.h` and `hpha.cpp`.

## Publication

The HPHA design and this source were published as a chapter by Dimitar Lazarov in *Game Programming Gems 7* (Charles River Media / Course Technology, 2008), alongside the accompanying source code archive from which the files in this directory derive.

## Licensing basis

The HPHA design was published by Dimitar Lazarov in the *Game Programming Gems* series (see Publication above), and was subsequently re-implemented as `HphaSchemaBase` (and related files) in the [Open 3D Engine](https://github.com/o3de/o3de) (O3DE) project — a Linux Foundation project — where it is distributed under:

```
SPDX-License-Identifier: Apache-2.0 OR MIT
```

The relevant O3DE files:

- [`Code/Framework/AzCore/AzCore/Memory/HphaAllocator.h`](https://github.com/o3de/o3de/blob/development/Code/Framework/AzCore/AzCore/Memory/HphaAllocator.h)
- [`Code/Framework/AzCore/AzCore/Memory/HphaAllocator.cpp`](https://github.com/o3de/o3de/blob/development/Code/Framework/AzCore/AzCore/Memory/HphaAllocator.cpp)

The O3DE header explicitly credits Lazarov: *"Heap allocator schema, based on Dimitar Lazarov 'High Performance Heap Allocator'."*

This Oris project adopts the same dual licensing — **MIT OR Apache-2.0** — for the inclusion of the C++ reference source in this directory, consistent with the public license trail above and with the maintainer's correspondence with the original author dating to 2009.

## Modifications

**One line, in `hpha.h`.** Otherwise the files are byte-identical to the maintainer's archived originals, modulo file timestamps — verified by diff against the archived source package:

| File | Difference from the archived original |
|---|---|
| `hpha.cpp` | none — byte-identical |
| `hpha.h` | line 31: `#define MULTITHREADED` → `//#define MULTITHREADED` |

The `MULTITHREADED` change is a build-configuration choice, not an edit to the algorithm: both Oris ports implement HPHA's single-threaded mode, and `ROADMAP.md` defers `MULTITHREADED` to v2.x. Leaving it enabled would make this reference compile against a mutex-guarded variant that no port mirrors, so the ports would be diffing against the wrong configuration. The original copyright headers are preserved verbatim in both files, as required.

Any future modification is recorded in this table.

## Which revision this is, and why it matters

These files are the **2007 source**. A later revision by the author exists, dated 2012-04-21, which is *not* what this directory carries.

The difference is behavioural, not cosmetic, and it falls inside the v0.2.0 debug-allocator milestone: the 2012 revision fixes a case where a failed `realloc` destroys the allocation record of a still-live block. It is recorded as **E9** in [`ERRATA.md`](ERRATA.md), which also carries the recommendation for what v0.2.0 should port.

The default reference for both ports is the source in this directory. Anything ported from the 2012 revision instead must say so explicitly, per-entry, in `ERRATA.md`.

## Known defects in this reference

The ports do not reproduce this source uncritically. [`ERRATA.md`](ERRATA.md) is the register of defects found in it, split by what each port does about them — fixed, deliberately preserved, unreachable, or already fixed upstream. Each entry records whether the difference is visible to the cross-port trace gate described in [`../ROADMAP.md`](../ROADMAP.md).
