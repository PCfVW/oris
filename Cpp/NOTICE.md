# NOTICE — HPHA reference source

The files in this directory (`hpha.h`, `hpha.cpp`) are Dimitar Lazarov's original HPHA implementation, dated 2007. They are included here for reference: the Rust (`orisnik`) and Zig (`orisnitsa`) ports diff against this canonical source, and the cross-language invariant described in [`../ROADMAP.md`](../ROADMAP.md) is defined relative to it.

## Original copyright

```
Copyright (c) 2007, Dimitar Lazarov, Luxoflux
dimitar.lazarov@usa.net
```

The original header is preserved verbatim in both `hpha.h` and `hpha.cpp`.

## Licensing basis

The HPHA design was published by Dimitar Lazarov in the *Game Programming Gems* series, and was subsequently re-implemented as `HphaSchemaBase` (and related files) in the [Open 3D Engine](https://github.com/o3de/o3de) (O3DE) project — a Linux Foundation project — where it is distributed under:

```
SPDX-License-Identifier: Apache-2.0 OR MIT
```

The relevant O3DE files:

- [`Code/Framework/AzCore/AzCore/Memory/HphaAllocator.h`](https://github.com/o3de/o3de/blob/development/Code/Framework/AzCore/AzCore/Memory/HphaAllocator.h)
- [`Code/Framework/AzCore/AzCore/Memory/HphaAllocator.cpp`](https://github.com/o3de/o3de/blob/development/Code/Framework/AzCore/AzCore/Memory/HphaAllocator.cpp)

The O3DE header explicitly credits Lazarov: *"Heap allocator schema, based on Dimitar Lazarov 'High Performance Heap Allocator'."*

This Oris project adopts the same dual licensing — **MIT OR Apache-2.0** — for the inclusion of the C++ reference source in this directory, consistent with the public license trail above and with the maintainer's correspondence with the original author dating to 2009.

## Modifications

None. The files are byte-identical to the maintainer's archived 2007 originals, modulo file timestamps. Any future modifications will be recorded in this file.
