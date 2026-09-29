# Changelog

All notable changes to Oris are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Both ports ship in lockstep: one version number covers `orisnik` (crates.io) and
`orisnitsa` (GitHub Release), carrying the same feature set and the same internal
state transitions (see [`ROADMAP.md`](ROADMAP.md)).

## [Unreleased]

### Added

- **Debug hooks wired into the allocator (v0.2.0, Phase 4).** With `debug-allocator` /
  `Orisnitsa(.{ .debug = true })` the record store from Phase 3 is now live: every
  allocation is recorded (address, requested size, source, guard seed, callstack) and every
  free, realloc, resize and purge goes through HPHA's own hooks — `debug_add`,
  `debug_remove`, `debug_replace`, `debug_update`, `debug_check`, `debug_purge` — at exactly
  the points and in exactly the order HPHA calls them. The hooks own the guard seed, the
  ramp write and the poisoning, so the three can no longer disagree; that code moved out of
  the Phase 2 size-class wrappers, which are back to plain inflate shims. `free` now
  verifies the block *before* reclaiming it: a record must exist (else: double free or a
  foreign pointer), a sized free's size must match, and the guard ramp must still equal the
  recorded seed (else: something wrote past the end of the block). Payloads are poisoned at
  the *recorded* size, which retires Phase 2's "poison the usable size" approximation.
  Detected corruption is fail-fast (`panic!` / `std.debug.panic`); detection itself is a
  plain value (`verify`), so it is testable in both ports. `requested()` reports HPHA's
  running total of requested bytes (each block plus its guard reservation); if the record
  store cannot get a page, `alloc` frees the block and returns `None`/`null` — a value, as
  in HPHA. A failed `realloc` leaves the original allocation *and* its record untouched
  (the `Cpp/ERRATA.md` E9 correction). Without the feature the hooks are no-ops (Rust:
  `#[inline]` stand-ins the compiler removes; Zig: never analysed).

  Two things in `orisnik` that `orisnitsa` does not need. (1) *Re-entrancy:* a `busy` flag
  makes nested allocator calls made while a hook runs skip the hooks. No hook allocates
  from its own instance today, so this is an enforced invariant, tested directly, that the
  coming `report()` (which formats strings while iterating the store) will rely on.
  (2) *`#[global_allocator]`:* std's backtrace lock is process-wide and non-reentrant, and
  std allocates while holding it, so an allocator that captures a backtrace inside `alloc`
  **deadlocks** against application code that is itself capturing one (a panic hook with
  `RUST_BACKTRACE=1`, an explicit `Backtrace::capture`) — found by
  `tests/debug_global_allocator.rs`, which force-captures a backtrace from user code with
  `Orisnik` as the process's allocator (it hung before this rule). An instance used through `GlobalAlloc` therefore records **no
  callstack**; every other record field, and so every detection above, still works. Such a
  program must be built with `panic = "abort"`. `orisnitsa` captures into a fixed buffer
  with no lock and no allocation, so it has neither concern.

  A defect in HPHA's own debug mode is fixed rather than reproduced (`Cpp/ERRATA.md` E10):
  `alloc(5)` records size 8 (it clamps first), but `free(p, 5)` compared the raw 5 against
  it and asserted on a perfectly legal call. Both ports compare the way the record holds the
  size: clamped for a bucket-path record, raw for a tree-path one (an aligned request past
  `MAX_SMALL_ALLOCATION` alignment goes to the tree, which never clamps — an unconditional
  clamp would have introduced a false report there; caught in review, pinned by a test in each
  port).

  `orisnitsa` specifics: a debug instance must be `deinit()`ed or its record pages leak;
  `RecordStore.replace(ptr, fresh)` and `update(..., callstack)` changed signature; and
  `os.test_vm.failMapAfter` budgets need one extra map under debug (the record page). Zig
  cannot catch a panic, so detection is tested through the pure `verify`, and dispatch wiring
  through debug-only hook-invocation counters (`stats`) that never let a corrupted free
  continue.

- **Allocation-record store and callstack capture (v0.2.0, Phase 3).** The data structures
  behind HPHA's `debug_record_map`, for `debug-allocator` (Rust: feature-gated) and
  `Orisnitsa(.{ .debug = true })` (Zig: the record modules are non-generic and always
  compiled, but reachable from neither config yet). Not wired into the allocator's
  dispatch — that is Phase 4 — so nothing observable changes. A `Record` remembers one live allocation — address,
  the size the caller requested, which sub-allocator served it (`Source`), the seed of
  its guard ramp, and where it was allocated from. Records live densely in a
  page-chained `RecordBook` (HPHA's `virtual_book`: push/pop at the back only) and are
  indexed by address in the existing intrusive red-black tree via a `RecordStore`
  (`add`/`find`/`remove`/`replace`/`update`); removing from the middle swaps the last
  record into the hole and re-links it, as HPHA does. The store is pure bookkeeping — it
  never dereferences the caller's allocation, so poisoning and the guard-ramp assert
  stay with the dispatch layer. A new strict guard check (`check_guard_seeded`/
  `checkGuardSeeded`) compares the trailing ramp against the *recorded* seed, closing
  the self-consistency-only gap the earlier `check_guard` documented. Callstacks:
  `orisnik` captures a real `std::backtrace::Backtrace` (`force_capture`, so it works
  regardless of the embedder's `RUST_BACKTRACE`), and `orisnitsa` a fixed 8-frame
  address buffer via `std.debug.captureCurrentStackTrace` (HPHA's own depth); HPHA's
  version is a stub. The two ports' records differ in size (`orisnitsa` inlines the 8
  addresses; `orisnik` holds a `Backtrace`), so the record book's page capacity differs —
  debug-only diagnostic storage, outside the state-transition invariant. `Backtrace`
  capture allocates, so Phase 4 must break the re-entrancy when `Orisnik` is its own
  global allocator (noted in `spomen/record.rs`); the store already captures before it
  mutates any state. Symbol resolution is deferred to `report()`. Miri supports both the capture and symbol
  resolution (the latter only when run with `-Zmiri-isolation-error=warn`, because std
  asks for the current directory first): one test drives real, heap-owning backtraces
  through swap-remove, replace, update and drop under Miri, and the name-checking test
  runs there as an opt-in; other tests use the cheap no-op capture under Miri, since
  each real capture costs ~1.5 s. Deliberate departure
  from the plan's sketch: HPHA's dense `virtual_book` is ported faithfully rather than a
  free-slot `RecordPage`. Found by Miri while building it: `Drop::drop(&mut self)`
  must not unlink intrusive-list nodes (a foreign write to a protected tag under Tree
  Borrows); `RecordBook::drop` releases its pages without unlinking, and
  `list.rs`'s module doc now records the rule for the `Drop for Orisnik` still to come.
- **Payload poisoning (v0.2.0, Phase 2 — completes this phase).** Behind
  `debug-allocator`/`config.debug`: fresh allocations and freed blocks both get
  filled with a repeating `{0xFF, 0xC0, 0xC0, 0xFF}` pattern (a quiet-NaN bit
  pattern in either endianness), ported from HPHA's `initial_fill`
  (`Cpp/hpha.cpp:762-767`) exactly — catching reads of uninitialized memory and
  use-after-free reads with a recognizable pattern instead of plausible-looking
  leftover data. Wired into the same tree/bucket `alloc`/`alloc_aligned` choke
  points guard bytes already use (fill after the guard write — the two spans are
  disjoint, so order has no functional effect, only fidelity value) and into
  `free`/`free_with_size`/`free_with_size_aligned` (fill *before* the underlying
  reclaim, matching HPHA's `debug_remove`-before-`bucket_free`/`tree_free` order).
  `realloc`/`resize` are deliberately untouched — HPHA's own `update`/`replace`
  never poison either. `calloc` needed no changes: it already composes for free
  (`alloc`'s poison, then `calloc`'s own zero-fill, in that order).

  `free`'s pointer-only overload has no caller-supplied size, so it poisons the
  block's own current, deflated usable size (a safe, documented substitute for
  HPHA's exact allocation-record-tracked original size, pending that record store
  in a later phase); `free_with_size`/`free_with_size_aligned` already have the
  caller's original size in hand and use it directly, matching HPHA exactly. One
  test deliberately reads a block's payload immediately after `free()` (before
  `purge()`) to confirm the poison — empirically checked under Miri
  (`-Zmiri-strict-provenance -Zmiri-tree-borrows`) rather than assumed sound, and
  it passes clean.

  No behavior change with the feature/config off. Full suites verified in both
  ports (cargo test/clippy -D warnings with/without the feature and combined with
  nightly; zig build test in Debug and ReleaseSafe; zig fmt), plus Miri on the
  Rust side.
- **Bucket-path memory guard bytes (v0.2.0, Phase 2).** Completes the guard-byte
  reservation started by the tree-path commit above. Unlike the tree path, the
  bucket path has no per-block header to inflate — `bucket::is_small_allocation`
  itself becomes guard-aware (`size + MEMORY_GUARD_SIZE <= MAX_SMALL_ALLOCATION`,
  ported from HPHA's own `is_small_allocation` exactly, with a saturating add so a
  pathologically huge `size` can't wrap into falsely reporting "small"), shifting
  the bucket/tree dispatch boundary down by 16 bytes under the feature/config —
  exactly mirroring HPHA. New `bucket_alloc`/`bucket_alloc_aligned`/
  `bucket_realloc`/`bucket_resize` choke points parallel the tree-path ones
  (`bucket_alloc_aligned` folds the guard in *before* rounding to alignment, not
  after — order matters, not just that both happen, per HPHA's own
  `round_up(size + MEMORY_GUARD_SIZE, alignment)`).

  The single most important fix in this commit: `free_with_size`/
  `free_with_size_aligned` independently recompute a pointer's bucket index from
  its caller-supplied original size, and that recomputation must apply the
  *identical* guard inflation the original `alloc` used — without it, a live
  pointer frees into the *wrong* bucket's free list (verified empirically, not
  just reasoned about: reverting just this one inflate call and re-running the
  new regression test reproduces a `bucket_index` mismatch, off by exactly 2 size
  classes, in both ports — `Cpp/hpha.h`'s own `free(void*, size_t[, size_t])`
  inflates before recomputing for exactly this reason).

  Both ports' `VintageRand`-derived cross-port golden-number test (bucket/tree
  split counts over the shared stress-workload stream) now asserts distinct,
  empirically-measured pairs for the feature/config on vs. off, since the shifted
  dispatch boundary moves a handful of borderline sizes — the two ports' measured
  numbers agree exactly, confirming the guard-byte dispatch logic didn't diverge
  between them.

  No behavior change with the feature/config off. Full suites verified in both
  ports (cargo test/clippy -D warnings with/without the feature and combined with
  nightly; zig build test in Debug and ReleaseSafe; zig fmt), plus Miri with
  -Zmiri-strict-provenance -Zmiri-tree-borrows on the Rust side.
- **Tree-path memory guard bytes (v0.2.0, Phase 2).** Behind `debug-allocator`/
  `config.debug`: every tree-path allocation now reserves and writes a trailing
  16-byte guard ramp (`seed, seed+1, ..., seed+15`, wrapping) immediately after the
  caller's own requested bytes, ported from HPHA's `write_guard`
  (`Cpp/hpha.cpp:745-751`) exactly, including its size (`MEMORY_GUARD_SIZE`) and
  placement. `orisnik::alloc`/`alloc_aligned`/`realloc`/`realloc_aligned`/`resize`
  (and `orisnitsa`'s equivalents) all route through new private wrapper methods
  (`tree_alloc`/`tree_alloc_aligned`/`tree_realloc`/`tree_realloc_aligned`/
  `tree_resize`) that inflate the real block size by the guard reservation and
  write/rewrite the ramp on success — invisibly to every caller (`size`/`querySize`
  report exactly the original request either way). `spomen::guard`/`spomen_guard`
  add a directly-tested, self-consistency-only `check_guard`/`checkGuard`
  primitive (not yet wired into `free`/`realloc`'s dispatch — that needs the
  allocation-record store, a later phase, to supply the true original size a
  live pointer's *usable* size can exceed).

  The existing test-only `VintageRand` (the Microsoft CRT `rand()` port) is
  promoted to production (`Rust/src/rand.rs`, `Zig/src/rand.zig`) and now also
  seeds the guard ramp, so both ports write byte-identical ramps for an identical
  allocation sequence — not merely per-port-plausible content.

  One real bug was caught by testing through the actual dispatch (not just the
  low-level ramp primitive) and fixed before landing: the first `resize`
  implementation only rewrote the guard when the block grew *past* the caller's
  requested size, which misses the case where growth lands *exactly* on it (the
  guard's position still moves). The fix — always rewrite, at the block's actual
  reported new size — mirrors HPHA's own `resize` body exactly (`hpha.h`
  reassigns `size` to `tree_resize`'s real return value before calling
  `debug_update`, unconditionally, whether or not growth occurred).

  No behavior change with the feature/config off — both full suites (`cargo
  test`/`clippy -D warnings` with and without `debug-allocator`, incl. `nightly`
  combined; `zig build test` in Debug and ReleaseSafe) pass unchanged, plus Miri
  (`-Zmiri-strict-provenance -Zmiri-tree-borrows`) on the Rust side. The bucket
  path and the rest of `spomen` (allocation records, callstack capture,
  `check()`/`report()`) follow in later phases.
- **The `debug-allocator` / `spomen` toggle scaffolding (v0.2.0, Phase 1).**
  Behavior-inert groundwork for porting HPHA's `DEBUG_ALLOCATOR` mode: `orisnik`
  gains a `debug-allocator` Cargo feature (same shape as the existing `nightly`)
  and an always-compiled `guard` module holding just `MEMORY_GUARD_SIZE` (16 when
  the feature is on, 0 otherwise — not yet consumed anywhere); `orisnitsa`'s
  `Orisnitsa`/`Buckets`/`Tree` become generic type constructors over a new
  `spomen.Config`, matching Zig's own `std.heap.DebugAllocator(comptime config:
  Config)` shape, so the eventual debug instrumentation gets a compiler-guaranteed
  zero-cost-when-disabled property rather than an optimizer hope. Both ports'
  default (non-debug) behavior and every existing test are unchanged; each port
  gains one new test exercising the debug-enabled side of the toggle end to end.
  See `ROADMAP.md`'s v0.2.0 milestone.
- **`Cpp/oracle/main_c_abi.cpp`** — Lazarov's own `main.cpp` benchmark (from the
  maintainer's archived HPHA copy, not in this repo), mechanically ported onto the
  `oris_*` C ABI: 512 Ki live allocations at its `r^8`-skewed size distribution,
  freed in its randomized order, run once manually against both ports' real
  libraries (audit's "Option A"). Both survive intact — exit 0,
  `allocated after purge: 0`, including the `realloc(ptr, 0, 0)` call F5 blocked
  before v0.1.1. See [`Cpp/oracle/README.md`](Cpp/oracle/README.md) for build/run
  instructions; MSVC/Windows-only and not wired into CI, matching
  `oracle_trace.cpp`'s existing precedent.

### Fixed

- **Bucket→tree `realloc` clobbered the new block's guard ramp (v0.2.0 Phase 2, both
  ports; found by the Phase 2 consistency review, not by a test).** When a
  guard-enabled `realloc`/`realloc_aligned` promotes a bucket allocation onto the tree
  path, the port copied the old slot's *whole* inflated `elem_size`, including its
  trailing guard ramp. HPHA's own `memcpy` copies `elem_size - MEMORY_GUARD_SIZE`
  (`Cpp/hpha.h:1322`, `:1367`); the port had reasoned that copying the extra bytes was
  "harmless" because the new block is larger, overlooking that the new block's *own*
  ramp — already written by `tree_alloc` at `[size, size + MEMORY_GUARD_SIZE)` — lands
  inside that range whenever `elem_size > size` (a 256-byte slot promoted to a
  250-byte request), so the old ramp's tail overwrote it. Latent, because nothing
  checks guards from dispatch yet; it would have become a false corruption report the
  moment `free`/`realloc` verification is wired in. Both crossovers now copy only the
  payload (`deflate(elem_size)`, further capped at `size` on the aligned path). Two new
  regression tests per port (plain and aligned) failed before the fix, in both
  languages, and pass after it.

### Changed

- **Zig `// SAFETY:` coverage and Rust rustdoc links (pre-existing gaps closed).** The
  pre-v0.2.0 Zig code (`tree`, `block`, `bucket`, `align`, `os`, `rbtree`, `orisnitsa`,
  `allocator`, `list`) justified raw-pointer operations without the literal
  `// SAFETY:` tag `Zig/CONVENTIONS.md` requires; every such site now carries one
  (comment-only change, no behavior difference). In Rust, four broken intra-doc links
  reported by `cargo doc --document-private-items` (`tree.rs`, `rbtree.rs`,
  `orisnik.rs`) are fixed.
- **Phase 2 consistency pass (documentation, annotations, tests).** Applied both
  `CONVENTIONS.md` files to the Phase 2 code and removed prose the phase had made
  stale: `// SAFETY:` tags on the Zig guard/poison call sites (the older Zig code was
  brought into line in the separate entry below), a mis-used
  `// PROVENANCE:` and a malformed `// CAST:` in Rust, an unannotated test index,
  explanations of why the bucket wrappers' `inflate(..).unwrap_or(..)` fallback is
  unreachable, `INSTALL.md`'s "currently inert" claim, "later phase" wording in
  `spomen.zig`/`guard.zig`/`orisnitsa.zig`, missing field/`init` docs on
  `VintageRand` (Zig), and `CONVENTIONS.md` coverage of the `guard`/`spomen` module
  split, `rand`, and the `if (config.debug) T else void` conditional-field idiom.
- **`Cpp/ERRATA.md`'s E9 corrected — not a real defect.** While planning v0.2.0's debug
  allocator, direct re-reading of `hpha.cpp:908-910` (`allocator::debug_replace`'s own
  `if (!newPtr) return;` guard, one call frame above the snippet E9 quotes) and of
  `bucket_realloc`/`tree_realloc`'s every branch (`hpha.cpp:256-267`, `:522-587`) showed
  a failed `realloc` never frees or moves the original block and never reaches
  `debug_record_map::replace`'s unconditional overwrite with a NULL pointer — so the
  "lost record for a still-live block" E9 described does not occur in the 2007 source.
  Porting the 2012 `replace_begin`/`replace_end` split is therefore not required for
  v0.2.0's correctness (though it remains a reasonable shape on its own merits). See
  `Cpp/ERRATA.md`'s E9 entry and `Cpp/NOTICE.md` for the full correction.
  Documentation-only.
- **F8's remaining note closed.** `Cpp/oracle/README.md`'s build instructions (for
  both `oracle_trace.cpp` and the new `main_c_abi.cpp`) now state explicitly that
  the build must not define `_DEBUG` — `Cpp/hpha.h`'s `MEMORY_GUARD_SIZE` shifts
  from 0 to 16 the moment it is, which would silently move every size class and
  split relative to the non-debug allocator being compared against. Documentation
  only.
- **F4 closed, no further action.** The pre-v0.2.0 audit's two proposed follow-ups to
  v0.1.1's debug-only move-detection tripwire — a `Pin`-based API, and a
  marker/eager-self-link redesign — were both evaluated and rejected: the former cannot
  help the `static`/`GlobalAlloc` surface (already immovable by construction) or the
  plain owned-value surface the finding actually reproduces against without breaking
  `Orisnik::new()`'s `const fn` shape, and the latter is precluded by the same
  const-fn-constructor constraint that motivates the lazy-sentinel-init design in the
  first place. Promoting the tripwire to an always-on check was also rejected — it sits
  on the hot path `Rust/CONVENTIONS.md`'s "never `assert!` where `debug_assert!`
  suffices" rule forbids. See
  [`docs/audits/2026-08-29-pre-v0.2.0-audit.md`](docs/audits/2026-08-29-pre-v0.2.0-audit.md#f4)'s
  resolution note; both ports' `# Address stability` doc sections now record the
  conclusion directly. Documentation-only — no behavior changes in either port.

## [0.1.1] - 2026-08-29

A fidelity-and-soundness patch. Every change below either restores agreement with
`Cpp/hpha.h`/`hpha.cpp` or removes undefined behaviour, so all of it ships as a patch
under the *Fidelity fixes are patches* rule now recorded in
[`ROADMAP.md`](ROADMAP.md#fidelity-fixes-are-patches). No input that previously
behaved correctly changes. Both ports carry every fix, as the cross-port invariant
requires; findings are numbered as in
[`docs/audits/2026-08-29-pre-v0.2.0-audit.md`](docs/audits/2026-08-29-pre-v0.2.0-audit.md).

### Fixed

- **F1 — unchecked size arithmetic silently under-allocated on very large requests.**
  Every tree-path request passed through `round_up(size, 16)`, a bare mask with no
  overflow check, so `alloc(usize::MAX)` wrapped to a *zero-byte* block in a release
  build and panicked in `align.rs`/`std.mem.alignForward` in a checked one. Both ports
  now decline any request above a new `tree::MAX_ALLOCATION` / `tree.MAX_ALLOCATION`
  (roughly `usize::MAX - 64 KiB`, derived from the headroom each rounding step on the
  path to a mapped arena needs) before that arithmetic runs. HPHA performs the same
  arithmetic unchecked; the bound is above any allocation a real machine could serve,
  so it only refuses requests upstream would have corrupted the heap over.
- **F1, `calloc` half — an overflowing `count * size` was fatal, not merely wrong.**
  `calloc` passed HPHA's unchecked product to both the allocation *and* the zero-fill,
  so `calloc(2, usize::MAX)` acquired a few bytes and then memset exabytes over them —
  a segfault in release, reproduced during the audit. Now `checked_mul` /
  `@mulWithOverflow`, returning null on overflow.
- **F3 — `purge()` under-reclaimed bucket pages relative to HPHA.** Both ports broke
  out of the page-list walk at the first *partially-used* page; HPHA's `bucket_purge`
  breaks only at the first *full* one and keeps walking. Because a bucket's page list
  is re-sorted only on the full↔not-full transition, an empty page can sit behind a
  partially-used one, and those pages were never returned to the OS. The walk now
  mirrors HPHA exactly, latching each node's successor before unlinking it.
- **F5 — a zero `alignment` aborted where HPHA accepts it.** HPHA's own precondition is
  `assert((alignment & (alignment-1)) == 0)`, which *passes* for zero, so upstream
  routes `alloc(size, 0)` and `realloc(ptr, size, 0)` to the unaligned path — and
  Lazarov's own `main.cpp` benchmark calls `realloc(ptr, 0, 0)`. v0.1.0 checked
  `is_power_of_two`/`isPowerOfTwo` instead, which rejects zero and aborted every
  debug/`ReleaseSafe` build on that call. Both ports now port the original expression
  verbatim, as `is_hpha_alignment` / `isHphaAlignment`. `free_with_size_aligned` /
  `freeWithSizeAligned` maps a zero alignment to `DEFAULT_ALIGNMENT` so it names the
  same bucket the allocation came from — pinned by a test over the whole
  `1..=MAX_SMALL_ALLOCATION` range.
- **F6 — a zero-length `realloc`/`remap` freed the block and then reported failure.**
  `GlobalAlloc::realloc(ptr, layout, 0)` and the `std.mem.Allocator` vtable's
  `remap(_, 0)`/`resize(_, 0)` forwarded to a `realloc` that frees, then surfaced the
  resulting null — which both interfaces define as "failed, your pointer is still
  live", inviting a double free from a caller that respects the contract. All three
  now decline without touching the block. (Both interfaces forbid a zero length, so
  this is a caller bug either way; the guard makes it a harmless one.)
- **F10 — a zero `orig_size` underflowed the size-class index.** `free_with_size(ptr, 0)`
  and both zero-size forms of `free_with_size_aligned` reached
  `bucket_spacing_function(0)` — `((0 + 7) >> 3) - 1` — which underflows to
  `usize::MAX` and indexes a 32-element array. No allocation can have an original size
  of 0 (`alloc(0)` returns null), so this is a caller bug; but the consequence was not
  uniform. `orisnik` was contained to a bounds-check panic by Rust's always-on slice
  check, while **`orisnitsa`'s `ReleaseFast` build has no bounds check and wrote out of
  bounds silently** — in the build users ship. All three entry points in both ports now
  recover through `free`'s pointer-based dispatch, which re-derives bucket-vs-tree
  ownership from the pointer and so releases the block correctly regardless of the bad
  size. Deliberately not an assert: the recovery is correct rather than a guess, and
  asserting would reproduce the F5 failure shape (aborts in checked builds, works in
  release). HPHA has the identical underflow and no bounds check at all.

### Changed

- **F4 — `Orisnik`/`Orisnitsa` document their address-stability contract, and debug
  builds enforce it.** Both types bind three pieces of state to the instance's own
  address on first use (two lazily self-linked sentinels plus every bucket page
  marker), so moving one after its first allocation silently breaks bucket/tree
  dispatch. That constraint was documented only inside the private `list`/`rbtree`
  modules; it is now an `# Address stability` section on each public type. Debug and
  `ReleaseSafe` builds latch the instance address on first use and trip a named
  assertion on the first operation after a move, instead of corrupting quietly;
  `ReleaseFast`/release pay one word of storage and no instructions. A `Pin`-based API
  that would enforce this at compile time is deferred to v0.2.0. HPHA's C++
  `allocator` carries the same implicit constraint (it defines no move constructor).
- `Buckets::ptr_in_bucket`'s debug cross-check now distinguishes its two possible
  causes: a false *positive* is the known HPHA-inherited marker collision, while a
  false *negative* means the owning allocator was moved (F4).
- `SECURITY.md`'s CWE-190/CWE-131 row described checked size arithmetic that did not
  exist in v0.1.0 (**F2**). F1 implements it; the row now matches the code, and the
  CWE-476 row records the one documented exception to "OOM is a value, never a panic".
- `ROADMAP.md` gains an explicit *Fidelity fixes are patches* rule under the versioning
  policy, with the two conditions a change must meet to qualify.
- **F7 — `Zig/CONVENTIONS.md` and `Zig/CLAUDE.md` named the wrong verification tool.**
  Both listed `std.testing.checkAllAllocationFailures` as covering allocation-failure
  paths. It cannot: that helper wraps a `FailingAllocator` around a *backing*
  `std.mem.Allocator` and passes it **to** the code under test, so it exercises
  allocator *consumers*. `Orisnitsa` consumes no allocator — it calls `os.map` directly
  — so there is nothing to wrap. It was correspondingly never used anywhere in `src/`.
  Both documents now describe the injection seam that actually fits, and say why.
- **F8 — `Cpp/NOTICE.md` claimed "Modifications: None".** The reference `hpha.h` in fact
  differs from the archived original on one line (`#define MULTITHREADED` commented out —
  a build-configuration choice matching both ports' single-threaded scope, not an
  algorithm edit). `hpha.cpp` is byte-identical. The NOTICE now records this in a table,
  declares which revision of the reference governs, and points at the new errata
  register.

### Added

- **[`Cpp/ERRATA.md`](Cpp/ERRATA.md)** — a register of defects found in the HPHA
  reference, split by what the ports actually do about each: fixed (E1–E5), deliberately
  preserved (E6–E7), unreachable through the ports' surface (E8), and already fixed by
  the author in a later revision (E9). Every entry carries a **Trace-visible** verdict —
  whether the v0.3.0 trace-corpus gate should expect the C++ oracle and the ports to
  disagree — so that gate has a list to work from instead of firing on each deviation.
  The register also records the evidence each fix met the *Fidelity fixes are patches*
  conditions.
- **E9, found while writing that register and open for v0.2.0:** the 2007 reference in
  `Cpp/` loses a live allocation's debug record when a `realloc` fails. Two of
  `realloc`'s three debug call sites pass a possibly-`NULL` `newPtr` into
  `debug_replace`, whose unconditional `*record = debug_record(newPtr, ...)` then
  overwrites the record of the still-live original block. The author fixed this himself
  in a 2012 revision (splitting `replace` into `replace_begin`/`replace_end`, guarded by
  `if (ptr)`), which is *not* the source this directory carries. Nothing to fix in
  v0.1.1 — no debug subsystem is ported yet — but v0.2.0 should port the 2012 form.
  > **Correction (added while planning v0.2.0, 2026-09-28):** this entry is wrong — see
  > `Cpp/ERRATA.md`'s E9 correction note and the `[Unreleased]` entry below.
- **F7 — an out-of-memory injection seam, and coverage for every OOM path.** `os::map`
  had no failure seam, so every `?` / `orelse return null` on a `system_alloc` result in
  `Buckets` and `Tree` was unexecuted by any test — the OOM early-outs existed only on
  paper. `os::test_vm::fail_map_after` / `os.test_vm.failMapAfter` supplies one, and both
  ports now cover: OOM on all four alloc paths plus `calloc`, recovery once the OS stops
  refusing, and — the one with teeth — that a `realloc` which cannot grow reports failure
  **and leaves the original allocation live and intact**.
- **F9 — the entire public surface now runs under Miri (`orisnik`).** Miri cannot
  interpret `VirtualAlloc`/`mmap`, so before v0.1.1 every test that actually allocated
  was `#[cfg_attr(miri, ignore)]`: 22 allocator-path tests, including all of `Orisnik`,
  the `oris_*` C-ABI, `GlobalAlloc` and the `Allocator` trait, sat outside the soundness
  gate. `os::test_vm` now serves `map`/`unmap` from a `PAGE_SIZE`-aligned heap
  allocation **under Miri only** — a native `cargo test` still exercises the real
  syscalls, so this adds coverage rather than replacing it. v0.1.0 skipped **26 of its
  83 tests** under Miri; v0.1.1 skips **5** — `os.rs`'s four real-syscall tests, which
  Miri genuinely cannot interpret, and the manual C++ oracle tool — with **93 passing**
  under `-Zmiri-strict-provenance -Zmiri-tree-borrows`.
  - Nine tests gained a `purge()` they had been missing: with the stand-in backing
    `map`, pages the allocator holds until asked (matching HPHA) show up to Miri as
    still-live memory. That is the documented embedder contract, so calling `purge()`
    is both what a well-behaved caller does and a stronger assertion. `capi.rs`'s test
    now demonstrates the `oris_purge`-before-`oris_destroy` pattern `oris_destroy`'s own
    doc prescribes.
- **F9 — a randomized stress workload in both ports**, modelled on the shape of
  Lazarov's own `main.cpp` benchmark: 20 000 allocations at its `r^8`-skewed size
  distribution, freed in its randomized `i + rand() % (N - i)` order, with and without
  alignment — plus the assertions `main.cpp` never had. Every block is stamped with a
  fingerprint derived from its index and verified on free, so a block handed out twice
  or overlapping another fails loudly; `purge()` must then reclaim everything. Path
  coverage (~71% bucket, ~29% tree) is asserted so the workload cannot silently
  degenerate into a single-path test. This is the coverage class the suites had none of:
  the only randomized test in either port previously exercised the `RB-tree`, not the
  allocator. `orisnik` scales the workload down under Miri rather than skipping it
  there — Miri's cost is near-linear in the block count (measured at 22.9 s / 45.7 s /
  83.7 s / 149.9 s for 100 / 250 / 500 / 1000, i.e. `t ~= 8.8 + 0.141*N` s), so the
  full run would cost ~47 min while `N = 150` costs ~30 s and still puts a randomized
  alloc/free interleaving across both size paths under the soundness gate.
  - The generator is the **Microsoft C runtime's `rand()` LCG**, from Eric Jacopin's
    "Vintage RNGs" chapter (*Game AI Pro 3*) — verified bit-identical to the real CRT
    over 200 000 draws across five seeds before being relied on, and pinned in both
    ports by a golden vector from that chapter's own `srand(0)` corpus plus the
    `srand(1234)` seed `main.cpp` uses. Both ports therefore drive **one identical
    stream**, and a future three-way C++/Rust/Zig comparison (`ROADMAP.md`'s v0.3.0
    trace corpus) can generate Lazarov's exact sequence independently in each language
    rather than shipping recorded traces. The size distribution uses an integer
    analogue of `powf(r, 8.0f)` — deliberately, since float `pow` is not
    bit-reproducible across language runtimes.
- Regression tests for every finding above, in both ports: oversized and
  overflowing-product requests, the F3 page-list state (an empty page behind a
  partially-used one), zero-alignment accept/alloc/free round trips, the
  bucket-index agreement the zero-alignment free relies on, the
  raw-vtable/`GlobalAlloc` zero-length realloc guard, and the zero-`orig_size`
  recovery across all three entry points on both the bucket and tree paths.
  94 Rust tests (from 79) and 96 Zig tests (from 81).

## [0.1.0] - 2026-08-17

### Added

- The Rust port (`orisnik`) of HPHA's non-debug, single-threaded allocator
  (`DEBUG_ALLOCATOR`/`MULTITHREADED` remain out of scope, see `ROADMAP.md`):
  - Cross-platform VM layer, alignment helpers, and a tagged-pointer helper
    (`os.rs`, `align.rs`, `tag.rs`).
  - An intrusive doubly-linked list and red-black tree, both faithful ports of
    HPHA's `intrusive_list`/`intrusive_multi_rbtree` (`list.rs`, `rbtree.rs`),
    cross-validated against the reference C++ via a standalone oracle harness.
  - The block header and the bucket (small-allocation) and tree (large-allocation,
    best-fit + coalescing) sub-allocators (`block.rs`, `bucket.rs`, `tree.rs`).
  - The top-level `Orisnik` dispatcher plus its three public surfaces: the
    `oris_*` C-ABI, `unsafe impl GlobalAlloc` (opt-in `#[global_allocator]`), and
    an optional `unsafe impl core::alloc::Allocator` behind the nightly-only
    `nightly` Cargo feature (`orisnik.rs`, `capi.rs`, `global_alloc.rs`,
    `allocator_trait.rs`).
  - 80+ tests (60+ Miri-covered under `-Zmiri-strict-provenance
    -Zmiri-tree-borrows`), including a debug-only exhaustive-scan verification of
    `ptr_in_bucket`'s marker-based dispatch (mirroring HPHA's own `#ifndef
    NDEBUG` check) added after integration testing reproduced the false-positive
    HPHA's own comment already anticipates.
- The Zig port (`orisnitsa`) of the same HPHA slice, module-for-module mirroring
  `orisnik`:
  - Cross-platform VM layer, alignment helpers, and a tagged-pointer helper
    (`os.zig`, `align.zig`, `tag.zig`).
  - An intrusive doubly-linked list and red-black tree, both faithful ports of
    HPHA's `intrusive_list`/`intrusive_multi_rbtree` (`list.zig`, `rbtree.zig`),
    cross-validated against `orisnik`'s own already-C++-oracle-validated trace via
    a matching 3000-step operation trace (byte-for-byte identical).
  - The block header and the bucket (small-allocation) and tree (large-allocation,
    best-fit + coalescing) sub-allocators (`block.zig`, `bucket.zig`, `tree.zig`),
    including `ptr_in_bucket`'s debug-only exhaustive-scan verification from the
    start (ported ahead of the false-positive `orisnik` only added after
    integration testing).
  - The top-level `Orisnitsa` dispatcher plus its three public surfaces:
    `Orisnitsa`'s own methods, a `std.mem.Allocator` vtable (`resize` never
    moves, `remap` may — matching the vtable's own contract), and the `oris_*`
    C-ABI (`orisnitsa.zig`, `allocator.zig`, `capi.zig`).
  - 80+ tests, verified in `Debug`/`ReleaseSafe` (`std.testing.allocator` leak
    detection, runtime safety checks on) and `ReleaseFast`, on all three CI OSes —
    Zig's analog of the Rust port's Miri gate.
- A shared C header, [`include/oris.h`](include/oris.h), declaring the `oris_*` prototypes
  behind an opaque `OrisAllocator*` handle, identical for both ports, plus the build
  changes that make the `oris_*` C-ABI actually linkable by a real C/C++ caller instead
  of only compiled into each port's own test binary:
  - `orisnik`: `crate-type = ["lib", "cdylib", "staticlib"]` in `Cargo.toml` — `cargo build
    --release` now also emits `liborisnik.so`/`.dylib`/`orisnik.dll` and
    `liborisnik.a`/`orisnik.lib`.
  - `orisnitsa`: `build.zig` now builds static and shared library artifacts
    (`liborisnitsa.so`/`.dylib`/`.a`, or `orisnitsa.dll`/`.lib` on Windows) from a module
    rooted directly at `capi.zig` — Zig only auto-exports `export fn`s that live in a
    module's own root file, so rooting the library artifacts at `root.zig` (as initially
    tried) silently produced a library with no `oris_*` symbols at all; verified with
    `dumpbin /exports` and a real C smoke test linked against both the static and shared
    artifacts before landing.
- Project scaffolding ahead of the v0.1.0 allocator implementation:
  - Initial Rust (`orisnik`, edition 2024 / MSRV 1.85) and Zig (`orisnitsa`,
    0.16.0) package skeletons — `Cargo.toml`/`build.zig.zon` manifests, a green
    `cargo test`/`zig build test` baseline — ahead of either allocator core.
  - `Grit-ORIS` coding conventions and AI-assist wiring (`CLAUDE.md`) for both ports.
  - CI for both ports (3-OS matrix; Rust adds a Miri soundness lane) with aggregator
    gate checks, crates.io **Trusted Publishing**, and a re-rooted Zig release asset
    with a recorded `zig fetch` hash.
  - `INSTALL.md`, `SECURITY.md`, README badges, Dependabot, and the Rust lint floor.
- Release engineering ahead of the tag:
  - `RELEASING.md`, the release-ceremony checklist, plus tag↔manifest version
    consistency gates in both `rust-publish.yml` and `zig-release.yml`.
  - A cross-platform C-ABI smoke-test workflow (`c-abi-ci.yml`) that builds both
    ports' real linkable libraries and links a real C caller against each via
    `zig cc`; `oris.h` vendored into both packages with a CI drift check.
  - CI coverage for the `nightly` `Allocator`-trait feature (test + clippy),
    previously verified only locally; both release workflows' own gauntlets
    extended to match (Miri re-run on the exact tagged commit, `ReleaseFast`
    tests, a packaged-tarball build-test for the Zig release asset).
  - `Orisnik`'s single-threaded/UB-if-multithreaded contract published on its
    public type doc (previously only in a private module's comment).
  - The C++ oracle harness (`Cpp/oracle/`) behind the three-way RB-tree
    cross-validation, reconstructed and re-verified live: all 3000 steps match
    byte-for-byte across every C++/Rust/Zig pairing.

[Unreleased]: https://github.com/PCfVW/oris/compare/v0.1.1...HEAD
[0.1.1]: https://github.com/PCfVW/oris/compare/v0.1.0...v0.1.1
[0.1.0]: https://github.com/PCfVW/oris/releases/tag/v0.1.0
