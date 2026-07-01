# Installing / building Oris

Oris is a two-port monorepo; each port builds independently with its own toolchain.

## Rust — `orisnik`

- **Toolchain:** Rust **1.85+** (edition 2024). The MSRV is 1.85 — the release that
  stabilized the strict-provenance APIs the allocator relies on.
- **Nightly** is needed only for two *optional* extras: running **Miri** (the
  soundness gate) and the unstable `allocator_api` `Allocator` trait surface. The
  default build, the C-shaped `oris_*` API, and the `#[global_allocator]` surface
  are all stable.

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

## Both ports ship in lockstep

The same version number on `orisnik` (crates.io) and `orisnitsa` (GitHub Release)
carries the same feature set and the same internal state transitions — see
[`ROADMAP.md`](ROADMAP.md).
