# The C++ oracle harness

`oracle_trace.cpp` is the C++ side of the three-way RB-tree cross-validation this
project's `CHANGELOG.md` and `Rust/src/rbtree.rs`/`Zig/src/rbtree.zig` refer to: it
links against the real, unmodified `../hpha.h`/`../hpha.cpp` and drives HPHA's own
`intrusive_multi_rbtree<T>` through the identical 3000-step PRNG-seeded
insert/erase sequence, printing the identical in-order trace format, as:

- Rust: `Rust/src/rbtree.rs`'s `#[ignore]`d
  `rbtree::tests::print_oracle_cross_validation_trace`
- Zig: `Zig/src/rbtree.zig`'s skipped-by-default
  `"oracle cross-validation trace (manual tool, not an assertion)"`

All three must produce byte-identical stdout across the full run for the cross-port
invariant's RB-tree slice (`ROADMAP.md`) to hold. This is a **manual verification
tool**, not part of this repo's CI: HPHA is Windows-only by `../hpha.h`'s own hard
`#error` outside `WIN32`, so it can only build where the other two ports' CI can't
meaningfully run it either.

## Build (Windows, MSVC)

From a Developer Command Prompt (or after running `vcvars64.bat`), from this
directory:

```sh
cl /EHsc /DWIN32 /I.. oracle_trace.cpp ..\hpha.cpp /Fe:oracle_trace.exe
```

`/DWIN32` is required explicitly — `cl` does not define bare `WIN32` on its own, and
`hpha.h` hard-errors without it.

## Run and cross-validate

```sh
.\oracle_trace.exe > cpp_trace.txt
```

Compare against a fresh run of each port's own oracle test:

```sh
# Rust, from Rust/ — extract the printed lines between "running 1 test" and the
# trailing "test ... ok" / "test result" summary:
cargo test --lib --release -- --ignored --nocapture rbtree::tests::print_oracle_cross_validation_trace

# Zig, from Zig/ — temporarily flip `run_oracle_trace` to `true` in
# rbtree.zig's oracle test, then:
zig test src/root.zig --test-filter "oracle cross"
# flip it back to `false` before committing; strip the "N/N ...)..." progress-line
# prefix Zig's test runner prepends to the very first trace line.
```

`cpp_trace.txt`'s lines end `\r\n` (MSVC's default text-mode stdio); the Rust/Zig
captures are `\n`-only — `diff --strip-trailing-cr` (or equivalent) before comparing,
same convention difference, not a real divergence.

## Verified

Re-run during this repo's v0.1.0 pre-release audit follow-up (2026-08-17): all 3000
steps matched byte-for-byte across all three pairings (C++↔Rust, C++↔Zig,
Rust↔Zig) — confirming the `CHANGELOG.md` claim live, not just by inspection of a
prior, unreproduced run.
