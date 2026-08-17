# Releasing Oris

Both ports ship in lockstep (see [`ROADMAP.md`](ROADMAP.md#versioning-policy)): one
`vX.Y.Z` git tag drives both [`rust-publish.yml`](.github/workflows/rust-publish.yml)
(crates.io) and [`zig-release.yml`](.github/workflows/zig-release.yml) (a GitHub
Release asset). This is the checklist for cutting one.

Both publish workflows now verify, on the tagged commit itself, that their manifest's
version matches the tag — a mismatch fails the job immediately rather than publishing
a silently-inconsistent release. That check is a safety net, not a substitute for
doing step 1 correctly.

## 1. Bump versions

Three places, kept in sync by hand:

- `Rust/Cargo.toml` — `version = "X.Y.Z"`
- `Zig/build.zig.zon` — `.version = "X.Y.Z"`
- `Rust/src/lib.rs` — `#![doc(html_root_url = "https://docs.rs/orisnik/X.Y.Z")]`

## 2. Update `CHANGELOG.md`

Move every bullet under `## [Unreleased]` into a new, dated `## [X.Y.Z] - YYYY-MM-DD`
section (the file has an HTML comment marking where). Leave `## [Unreleased]` in
place, empty, for the next cycle.

## 3. Update `SECURITY.md`

- The "Supported versions" table: move `main (pre-release)` → the new `X.Y.x` line as
  supported; the `< 0.1.0` row becomes historical.
- The blockquote note ("as of this writing... only the published package registries
  still hold name-reservation stubs") no longer applies once this release lands —
  reword or remove it.

## 4. Update the three README status paragraphs

- Root `README.md`'s Status section ("Not yet released...").
- `Rust/README.md` ("not yet published to crates.io... the 0.0.0 release currently
  live on crates.io only reserves the name").
- `Zig/README.md` ("not yet tagged as a release").

## 5. Run the full local gauntlet on the exact commit being tagged

- `cargo fmt --check && cargo clippy --all-targets -- -D warnings && cargo test`
- `cargo +nightly test --features nightly`
- `cargo +nightly miri test --features nightly` with
  `MIRIFLAGS="-Zmiri-strict-provenance -Zmiri-tree-borrows"`
- `zig fmt --check build.zig build.zig.zon src`
- `zig build test` and `zig build test -Doptimize=ReleaseSafe`, then
  `zig build -Doptimize=ReleaseFast`
- Confirm the last push of this commit to `main` shows green on **Rust CI**,
  **Zig CI**, and **C-ABI CI** (all three are required checks; the publish/release
  workflows themselves independently re-run the Rust gauntlet and the Zig
  Debug/ReleaseSafe/ReleaseFast + packaged-tarball build-test, but not the C-ABI
  smoke test, so check that one manually here).

## 6. Tag and push

```sh
git tag vX.Y.Z
git push origin vX.Y.Z
```

This fires both `rust-publish.yml` and `zig-release.yml`. Watch both runs; either
one's version-consistency check failing means step 1 was missed or is out of sync —
fix and re-tag rather than trying to patch a partially-published state.

## 7. Post-release verification

- `https://crates.io/crates/orisnik` shows the new version.
- `https://docs.rs/orisnik/X.Y.Z` built successfully.
- `https://github.com/PCfVW/oris/releases` has the new `orisnitsa-vX.Y.Z.tar.gz`
  asset, with the release notes' `zig fetch` hash matching what `zig-release.yml`
  computed.
- The root `README.md` badges (crates.io version, Zig release version) resolve to the
  new version.
- `zig fetch --save=orisnitsa <the release asset URL>` succeeds from a scratch
  project, matching the release notes' own instructions.
