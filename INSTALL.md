# Installing / building Oris

Oris is a two-port monorepo; each port builds independently with its own toolchain.

**64-bit platforms only** — both ports enforce this at compile time (a
`const`/`comptime` assert on `usize`/`@bitSizeOf(usize) == 64`; see `Rust/src/block.rs`'s and
`Zig/src/block.zig`'s module docs for why).

## Rust — `orisnik`

- **Toolchain:** Rust **1.85+** (edition 2024). The MSRV is 1.85 — the release that
  stabilized the strict-provenance APIs the allocator relies on.
- **Nightly** is needed only for two *optional* extras: running **Miri** (the
  soundness gate) and the unstable `allocator_api` `Allocator` trait surface. The
  default build, the C-shaped `oris_*` API, and the `#[global_allocator]` surface
  are all stable.
- **`--features debug-allocator`** enables `spomen`, the port of HPHA's
  `DEBUG_ALLOCATOR` mode (guard bytes, allocation-record tracking, leak detection,
  `check()`/`report()`), implemented on `main` for the unreleased v0.2.0 (`ROADMAP.md`; not in
  0.1.x) — stable, no nightly needed. Guard bytes, payload poisoning, allocation records (with callstack capture) and
  the hooks that use them are implemented: a guard overrun, a double free, a foreign
  pointer or a wrong sized-free size now **panics** with a diagnostic naming the block and
  where it was allocated. `Orisnik::check()` audits every live block on request
  (`Result<(), OrisError>`), `report()` prints the live blocks to stderr, and dropping an
  instance that still has live allocations is a **leak**: it is reported, the idle memory is
  released, and it panics. Installed as a `#[global_allocator]`, build with
  `panic = "abort"`, and note that such an instance records no callstacks (see `Rust/CONVENTIONS.md`). Build and test it
  with
  `cargo test --features debug-allocator` (Miri:
  `MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-tree-borrows" cargo +nightly miri test
  --features debug-allocator`). See the [user guide](docs/debug-allocator.md), and try
  `cargo run --example catch_an_overrun --features debug-allocator`.

```sh
cd Rust
cargo build
cargo test
cargo clippy --all-targets -- -D warnings
cargo fmt --check

# Optional — the allocator soundness gate (nightly):
cargo +nightly miri test   # MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-tree-borrows"
```

Once published, depend on it from crates.io:

```toml
[dependencies]
orisnik = "0.1"
```

## Zig — `orisnitsa`

- **Toolchain:** Zig **0.16.0**, pinned in `Zig/build.zig.zon`. The
  `std.mem.Allocator` vtable shape is version-sensitive while Zig is pre-1.0, so the
  pin is load-bearing.
- **`OrisnitsaWith(.{ .debug = true })`** is the Zig analog of `orisnik`'s
  `debug-allocator` feature — `spomen`, implemented on `main` for the unreleased v0.2.0
  (`ROADMAP.md`). No
  `zig build` flag needed; the default `orisnitsa.Orisnitsa` export stays the
  non-debug `Orisnitsa(.{})`. Same status as the Rust side above: guard bytes and
  payload poisoning, allocation records, the hooks that use them, `check()`/`report()` and
  leak detection are all implemented (detected corruption and leaks panic). Every
  `Orisnitsa` **must** be `deinit()`ed: that returns its idle memory to the OS, and a debug
  instance also frees its record pages and fails on leaked blocks. Exercise
  it with `zig build test` (the debug instantiation is covered by the test suite). See the
  [user guide](docs/debug-allocator.md), try `zig build example`, and generate the API
  reference with `zig build docs` (into `zig-out/docs/`).

```sh
cd Zig
zig build test                          # Debug — runtime safety checks ON
zig build test -Doptimize=ReleaseSafe   # optimized, safety checks ON
zig fmt --check build.zig build.zig.zon src
```

Once released, fetch the tagged GitHub Release asset (the URL and hash are printed in
each release's notes):

```sh
zig fetch --save=orisnitsa https://github.com/PCfVW/oris/releases/download/vX.Y.Z/orisnitsa-vX.Y.Z.tar.gz
```

## Linking from C/C++ (`oris.h`)

Both ports also build a real linkable C library, not just the `oris_*` symbols compiled into
their own test binaries:

- `orisnik`: `cargo build --release` emits `liborisnik.so`/`.dylib`/`orisnik.dll` (`cdylib`) and
  `liborisnik.a`/`orisnik.lib` (`staticlib`) under `Rust/target/release/`.
- `orisnitsa`: `zig build` emits `liborisnitsa.so`/`.dylib`/`.a` (or `orisnitsa.dll`/`.lib` on
  Windows) under `Zig/zig-out/`.

[`include/oris.h`](include/oris.h) declares the shared `oris_*` prototypes behind an opaque
`OrisAllocator*` handle — identical whichever port's library is linked. Building from this
repo, use the canonical copy at the repo root; each port's own published package (crates.io,
the Zig release tarball) also carries its own byte-identical vendored copy
(`Rust/include/oris.h`, `Zig/include/oris.h` — kept in sync by `c-abi-ci.yml`'s drift check)
since a package can't reference a file outside its own root:

```c
#include "oris.h"

OrisAllocator *h = oris_new();
void *p = oris_alloc(h, 64);
oris_free(h, p);
oris_destroy(h);
```

## Both ports ship in lockstep

The same version number on `orisnik` (crates.io) and `orisnitsa` (GitHub Release)
carries the same feature set and the same internal state transitions — see
[`ROADMAP.md`](ROADMAP.md).
