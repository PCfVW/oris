# orisnik Coding Conventions (Grit + Grit-ORIS Extensions)

This document describes the [Amphigraphic coding](https://github.com/PCfVW/Amphigraphic-Strict)
conventions used in `orisnik`, the Rust port of Dimitar Lazarov's **HPHA**. It is a
superset of the [Grit — Strict Rust for AI-Assisted Development](https://github.com/PCfVW/Amphigraphic-Strict/tree/master/Grit)
base, with allocator-specific extensions (`Grit-ORIS`).

It is aligned with [`anamnesis/CONVENTIONS.md`](https://github.com/PCfVW/anamnesis/blob/main/CONVENTIONS.md),
[`candle-mi/CONVENTIONS.md`](https://github.com/PCfVW/candle-mi/blob/main/CONVENTIONS.md), and
[`hypomnesis/CONVENTIONS.md`](https://github.com/PCfVW/hypomnesis/blob/main/CONVENTIONS.md) on the
trigger-checklist, doc-comment, signature, and control-flow rules.

**One section is inverted relative to its siblings.** Those crates parse files or measure
the system; `unsafe` is incidental to them and quarantined behind feature gates. orisnik
*is* an allocator: raw pointer arithmetic, intrusive metadata, pointer tagging, and manual
provenance are the work, not an exception to it. The [When Writing `unsafe`](#when-writing-unsafe)
section therefore does not try to minimize `unsafe` — it disciplines it. Everything is held
together by **provenance correctness**, **aliasing correctness**, and a **Miri gate** that
plays the role `cargo-show-asm` plays for the numeric crates.

The companion Zig port `orisnitsa` carries a parallel
[`Zig/CONVENTIONS.md`](../Zig/CONVENTIONS.md). The two share the
[Cross-Port Invariant](#the-cross-port-invariant) discipline, which is what makes maintaining
two ports worthwhile (see [`ROADMAP.md`](../ROADMAP.md)).

## Trigger Checklist

**Before writing any line of code, check which triggers apply.**

| You are about to... | Check these rules |
|---|---|
| Write a `///` or `//!` comment | [Backtick hygiene](#backtick-hygiene), [field-level docs](#field-level-docs), [intra-doc link safety](#intra-doc-link-safety) |
| Write a `pub fn` or `pub const fn` | [`const fn`](#const-fn), [`#[must_use]`](#must_use-policy), [pass by value](#pass-by-value-vs-reference) |
| Write a `pub unsafe fn` | [`# Safety` section](#safety-doc-section), [`// SAFETY:` at every call site](#safety-annotation) |
| Write a `pub fn` returning `Result<T>` | [`# Errors` section](#errors-doc-section) |
| Write a function that can return a null / dangling block | [Allocation outcomes, not `Result`](#allocation-outcomes-not-result) |
| Write a `pub struct` that is a block header or tree/list node | [`#[repr(C)]` layout lock](#repr-and-layout-lock), [`// EXHAUSTIVE:`](#exhaustive-annotation) |
| Write a `pub enum` | [`#[non_exhaustive]`](#non_exhaustive-policy) or [`// EXHAUSTIVE:`](#exhaustive-annotation) |
| Store bits in the low bits of a pointer | [`// TAG:`](#tag-annotation), [strict provenance](#strict-provenance) |
| Do pointer arithmetic / round to an alignment | [`// ALIGN:`](#align-annotation), [strict provenance](#strict-provenance) |
| Convert a pointer to/from an integer address | [`// PROVENANCE:`](#provenance-annotation), [strict provenance](#strict-provenance) |
| Write an `as` cast between numeric types | [`// CAST:`](#cast-annotation) |
| Write `slice[i]` or `slice[a..b]` | [`// INDEX:`](#index-annotation) |
| Write `.as_str()`, `.to_owned()` | [`// BORROW:`](#borrow-annotation) |
| Write an `unsafe` block | [`// SAFETY:`](#safety-annotation), [provenance & aliasing](#provenance-and-aliasing-the-core-discipline) |
| Dereference or build a `*mut T` / `NonNull<T>` | [`NonNull` over raw pointers](#nonnull-over-raw-pointers) |
| Write `Box<dyn T>` or `&dyn T` | [`// TRAIT_OBJECT:`](#trait_object-annotation) |
| Write a `match` or `if let` | [`if let` vs `match`](#if-let-vs-match), [`// EXPLICIT:`](#explicit-annotation) if no-op arm |
| Touch size-class math, tree rotation, or coalescing | [The Cross-Port Invariant](#the-cross-port-invariant) |
| Assert an internal allocator invariant | [`debug_assert!` invariants](#debug_assert-invariants) |
| Implement `GlobalAlloc` or `Allocator` | [Idiomatic surfaces](#idiomatic-surfaces) |
| Add `#[allow(clippy::...)]` for a newer lint | [MSRV lint guard](#msrv-lint-guard) |

---

## Annotation Grammar

The `// CAST:`, `// INDEX:`, `// PROVENANCE:`, `// TAG:`, `// ALIGN:`, `// BORROW:`,
`// TRAIT_OBJECT:`, `// SAFETY:`, `// EXPLICIT:`, and `// EXHAUSTIVE:` comments pair with
`#[allow(clippy::…)]` attributes that suppress the crate's [lint floor](#lint-floor). The
comment explains *why*; the attribute is what makes the code build under `#![deny(warnings)]`.

### Comment ↔ attribute pairing

| Annotation | Companion attribute(s) |
|---|---|
| `// CAST:` | `#[allow(clippy::as_conversions)]` plus, as the cast requires, `cast_possible_truncation`, `cast_possible_wrap`, `cast_ptr_alignment` |
| `// INDEX:` | `#[allow(clippy::indexing_slicing)]` |
| `// PROVENANCE:` | `#[allow(clippy::as_conversions)]` only when an FFI boundary forces a raw `as` (prefer the strict-provenance API, which needs no allow) |
| `// TAG:` / `// ALIGN:` | none when written with `map_addr` / `align_offset`; documentation-only |
| `// EXHAUSTIVE:` | `#[allow(clippy::exhaustive_enums)]` or `#[allow(clippy::exhaustive_structs)]` or `#[allow(clippy::wildcard_enum_match_arm)]` |
| `// SAFETY:` | `#[allow(unsafe_code)]` is **not** used — see the [`unsafe` policy](#when-writing-unsafe); the crate is `#![deny(unsafe_op_in_unsafe_fn)]`, not `#![deny(unsafe_code)]` |
| `// BORROW:`, `// TRAIT_OBJECT:`, `// EXPLICIT:` | none — documentation-only |

### Lint Floor

`Cargo.toml`'s `[lints.clippy]` block denies the underlying lints crate-wide:

| Lint | Level | How to satisfy |
|---|---|---|
| `unwrap_used`, `expect_used`, `panic` | `deny` (in `lib`) | never in allocator hot paths; allocation failure returns null, never panics |
| `indexing_slicing` | `deny` | `// INDEX:` + `#[allow(clippy::indexing_slicing)]` |
| `as_conversions` | `warn` | prefer strict-provenance APIs and `From`/`TryFrom`; `// CAST:` + allow only when unavoidable |
| `ptr_as_ptr`, `cast_ptr_alignment` | `warn` | `.cast::<T>()` for repointing; `// ALIGN:` to justify an alignment-increasing cast |
| `wildcard_enum_match_arm` | `deny` | `// EXHAUSTIVE:` + `#[allow(...)]` |
| `must_use_candidate` | `warn` | annotate with `#[must_use]` |
| `missing_errors_doc` | `warn` | write `# Errors` |
| `missing_safety_doc` | `warn` | write `# Safety` on every `pub unsafe fn` |
| `undocumented_unsafe_blocks` | `warn` | `// SAFETY:` on every `unsafe { … }` |
| `multiple_unsafe_ops_per_block` | `warn` | one logical `unsafe` operation per block, each with its own justification |
| `pedantic` (priority -1) | `warn` | per-lint allow with explanatory comment |

`#![deny(warnings)]` promotes every `warn` to a hard error. Keep this table in sync with
`Cargo.toml`. Note `undocumented_unsafe_blocks` and `missing_safety_doc`: in an allocator they
are the load-bearing lints, not afterthoughts.

---

## When Writing Doc Comments (`///`, `//!`)

### Backtick Hygiene

All identifiers, types, trait names, field names, crate names, and concepts-that-are-types
in doc comments must be wrapped in backticks so rustdoc renders them as inline code and
Clippy's `doc_markdown` lint passes.

Applies to: struct/enum/field names, method names (`fn alloc`), types (`NonNull<u8>`,
`Layout`, `Option<NonNull<u8>>`), crate/feature names (`core`, `alloc`, `debug-allocator`),
and the allocator's own terms of art — both the systems vocabulary (`mmap`, `VirtualAlloc`,
`RB-tree`, `best-fit`, `coalescing`, `purge`, `size class`) and the project's Bulgarian terms
of art used as identifiers (`orisnik`, `oris_alloc`, `razorisvam`, `spomen`, `stopanstvo`).

> ✅ `` /// Pops the best-fit free block from the `RB-tree` and splits it. ``
> ❌ `/// Pops the best-fit free block from the RB-tree and splits it.`

Cyrillic prose (Орисници, спомен) is welcome in `//!` module headers and free-text comments;
identifiers stay in diacritic-free Latin transliteration (per the brief's style note).

### Intra-Doc Link Safety

Rustdoc intra-doc links must resolve under all feature-flag combinations (enforced by
`#![deny(warnings)]` → `rustdoc::broken_intra_doc_links`). Feature-gated items (e.g. the
`spomen` debug-record types behind the `debug-allocator` feature) must use plain backtick text
from feature-independent modules, not link syntax:

> ✅ `` /// See `spomen::Record` (requires `debug-allocator` feature). ``
> ❌ `` /// See [`spomen::Record`](crate::spomen::Record). ``

### Field-Level Docs

Every field of every `pub` struct must carry a `///` doc comment. For the intrusive metadata
structs (block headers, tree/list nodes) the doc **must** state:

1. what the field represents,
2. its unit (bytes, size-class index) or valid range,
3. **whether the field is part of the inline metadata that physically precedes the payload**,
   and if so its byte offset and the alignment guarantee that places it there,
4. for tagged-pointer fields: which low bits carry flags and what they mean.

> Example:
> ```rust
> #[repr(C)]
> pub struct BlockHeader {
>     /// Block size in bytes, including this header. Always a multiple of
>     /// `ALIGN` (8). The low bit is unused here — tag bits live in `link`.
>     size: usize,
>     /// Tagged pointer to the previous physical block. Low bit = `IS_FREE`;
>     /// bit 1 = `IS_LAST`. Untag with `link.map_addr(|a| a & !TAG_MASK)`.
>     link: *mut BlockHeader,
> }
> ```

### `# Safety` Doc Section

Every `pub unsafe fn` must carry a `# Safety` section listing the preconditions the caller
must uphold — one bullet per invariant. This is the *contract*; the [`// SAFETY:`](#safety-annotation)
comment at a call site is the *discharge* of that contract.

    /// # Safety
    /// - `ptr` must have been returned by a prior `alloc`/`realloc` on **this**
    ///   allocator instance and not yet freed.
    /// - `layout` must be the same `Layout` used to allocate `ptr`.
    /// - No other reference to the block may be live across this call.

### `# Errors` Doc Section

Public fallible methods that genuinely return `Result<T>` (configuration, the debug
`check()`/`report()` paths) include an `# Errors` section. Each bullet: `Returns`
+ `` [`OrisError::Variant`] `` + `if`/`on`/`when`. The hot allocation path does **not** use
`Result` — see [Allocation outcomes, not `Result`](#allocation-outcomes-not-result).

### `# Invariants` Doc Section

Each allocator struct (`Bucket` and `Tree` — collectively the *orisnitsi*, the sub-allocator
sisters of the brief — and the top-level `Orisnik`) carries a `# Invariants` section on its type doc enumerating the structural invariants its `unsafe` code
relies on (e.g. "every free block is in exactly one tree; adjacent free blocks are always
coalesced; the bucket free-list head is null or points inside a live page"). The
[`debug_assert!` invariants](#debug_assert-invariants) check these at runtime under `debug`.

---

## When Writing Function Signatures

### `const fn`

Declare a function `const fn` when its body has no heap allocation, I/O, or `dyn` dispatch and
all callees are `const fn`. In an allocator this is not a minor nicety: **the size-class
table, the bucket boundaries, and the alignment masks must be computed in `const` context** so
they live in `.rodata` and the compiler can constant-fold size-class lookups on the hot path.

> ✅ `pub const fn size_class_of(bytes: usize) -> usize { (bytes + 7) >> 3 }`
> ✅ `const SIZE_CLASSES: [usize; 32] = build_size_classes();` where `build_size_classes` is `const fn`

When in doubt, annotate `const` and let the compiler reject it.

### `#[must_use]` Policy

All public functions that return a value and have no side effects are `#[must_use]`:
constructors, accessors, pure queries (`size`, `allocated`, `is_empty`). A discarded
allocation result is a leak — annotate every allocating method `#[must_use]` so callers cannot
silently drop the returned block.

### Pass by Value vs Reference

| Type | Rule |
|---|---|
| `Copy` type ≤ 2 words (`usize`, `NonNull<u8>`, `Layout`, size-class index) | Pass by value |
| `Copy` type > 2 words | Pass by reference |
| Non-`Copy`, not mutated | Pass by `&T` |
| Non-`Copy`, mutated | Pass by `&mut T` |
| Owned, consumed by callee | Pass by value |

`Layout` is `Copy` and two words — always pass it by value, never `&Layout`. The allocator
state is threaded by `&self` / `&mut self`; interior mutability (see
[`Layout`, `MaybeUninit`, `UnsafeCell`](#layout-maybeuninit-unsafecell)) governs which one.

---

## When Writing Public Structs and Enums

### Repr and Layout Lock

Block headers and intrusive node structs have a layout the algorithm depends on byte-for-byte
and that must match the Zig port field-for-field (see [the Cross-Port Invariant](#the-cross-port-invariant)).
They are therefore:

- `#[repr(C)]` (or `#[repr(transparent)]` for single-field newtypes) — **never** the default
  `repr(Rust)`, whose field order is unspecified.
- annotated `#[allow(clippy::exhaustive_structs)] // EXHAUSTIVE: <reason>` — these are *not*
  `#[non_exhaustive]`; their field set is part of the on-heap ABI and the cross-port contract,
  and is deliberately frozen.
- accompanied by a `const _: () = assert!(size_of::<BlockHeader>() == EXPECTED);` layout guard
  so an accidental field change is a compile error, not a silent corruption.

### `#[non_exhaustive]` Policy

Public *API* enums that may gain variants are `#[non_exhaustive]`: `OrisError`, and any
`Stats`/`QuerySource`-style enum. Internal dispatch enums matched exhaustively by this crate
get `#[allow(clippy::exhaustive_enums)] // EXHAUSTIVE: <reason>`. The on-heap metadata structs
above are the exception — frozen, not future-proofed.

---

## When Writing Expressions

These annotations are required **on or immediately before** the line where the pattern
occurs. Apply them as you write the line, not in a review pass.

### PROVENANCE Annotation

`// PROVENANCE: <what carries provenance, how it is preserved>` — required wherever a pointer
crosses to/from an integer address. Use the [strict-provenance](#strict-provenance) APIs
(`.addr()`, `.with_addr()`, `.map_addr()`, `ptr::without_provenance`,
`.expose_provenance()` / `ptr::with_exposed_provenance`), **never** `ptr as usize` /
`usize as *mut T`. The annotation names which original pointer the result's provenance derives
from.

> Example: `// PROVENANCE: derived from page_base; with_addr keeps the page's provenance for the whole block`
> Example: `// PROVENANCE: exposed at OS boundary — VirtualAlloc/mmap return is the provenance root for this region`

### TAG Annotation

`// TAG: <bits> = <meaning>` / `// UNTAG: <bits cleared>` — required on every pointer-bit pack
or unpack (HPHA's `ptr_bits`). Always implemented via `.map_addr(|a| …)` so provenance is
preserved; the comment documents the bit layout.

> Example: `// TAG: bit 0 = IS_FREE on the prev-block link`
> Example: `// UNTAG: clear bits [0..LOG2_ALIGN) to recover the aligned header address`

### ALIGN Annotation

`// ALIGN: <to what, why>` — required on every alignment round-up/round-down and on every
`as`-cast that *increases* a pointer's alignment requirement (`cast_ptr_alignment`). Prefer
`<*mut T>::align_offset`, `Layout::align`, and `align_up`/`align_down` helpers written over
`.map_addr`.

> Example: `// ALIGN: round payload up to ALIGN (8) so the next header is aligned`
> Example: `// ALIGN: cast page base to *mut BlockHeader; VirtualAlloc returns 64 KiB-aligned, ≥ align_of::<BlockHeader>()`

### CAST Annotation

`// CAST: <from> → <to>, <reason>` — required on every numeric `as` cast. Prefer `From`/`Into`
for lossless and `TryFrom`/`TryInto` with explicit handling for fallible. Use `as` only when
truncation/wrapping is the deliberate intent.

> Example: `// CAST: usize → u32, size-class index fits in u32 (≤ 31)`

### INDEX Annotation

`// INDEX: <reason>` — required on every direct slice index. Prefer `.get(i)`. In the
size-class dispatch tables the bound is provably valid (the index is the class number,
`< NUM_CLASSES`); annotate and index directly there rather than threading an `Option`.

> Example: `// INDEX: class < NUM_CLASSES, guaranteed by size_class_of's clamp`

### BORROW Annotation

`// BORROW: <what is converted>` — required on explicit `.as_str()`, `.as_bytes()`,
`.to_owned()`, and on `NonNull`↔`&mut [u8]` round-trips where the borrow's lifetime is
manually asserted (Grit Rule 2).

> Example: `// BORROW: slice::from_raw_parts_mut over the payload; exclusive for the lifetime of this &mut self`

### TRAIT_OBJECT Annotation

`// TRAIT_OBJECT: <reason>` — required on every `Box<dyn Trait>` / `&dyn Trait`. orisnik avoids
dynamic dispatch on the hot path entirely; the bucket vs tree decision is a branch on size,
not a vtable.

---

## When Writing `unsafe`

orisnik carries `#![deny(unsafe_op_in_unsafe_fn)]` at the crate root (`lib.rs`) — **not**
`#![deny(unsafe_code)]`. An allocator cannot quarantine `unsafe`
behind a feature gate the way `anamnesis`, `candle-mi`, and `hypomnesis` do; raw memory is its
domain. The discipline is therefore not *avoidance* but *containment and proof*.

### The three rules

1. **Concentrate, don't scatter.** All raw-pointer manipulation lives in the allocator core
   modules (`bucket`, `tree`, `block`, `os`). The public safe surface (`Orisnik::alloc`,
   the `GlobalAlloc`/`Allocator` impls) is a thin, fully-safe shell over them. A caller of the
   safe API writes zero `unsafe`.
2. **One operation per block.** `multiple_unsafe_ops_per_block` is on: each `unsafe { … }`
   performs one logical raw operation (one deref, one `from_raw_parts`, one tagged read) and
   carries its own `// SAFETY:`. Do not bundle a deref, a write, and a pointer offset into one
   block with one comment.
3. **Prove, don't assert.** Every `// SAFETY:` discharges a named precondition from a
   `# Safety` doc section or a struct `# Invariants` clause. "Should be fine" is not a safety
   comment.

### SAFETY Annotation

`// SAFETY: <invariants + how established here>` — required on every `unsafe` block and the
body of every `unsafe fn`. Document (1) the invariant the operation requires and (2) where, at
*this* call site, it is established.

> Example:
> ```rust
> // SAFETY: header was obtained by stepping back ALIGN bytes from a pointer this
> // allocator returned (caller contract of `free`); it is therefore a live, aligned
> // BlockHeader, and `&mut self` proves no concurrent access.
> let block = unsafe { &mut *header };
> ```

### Provenance and Aliasing: the core discipline

Two failure modes dominate allocator UB; both are invisible to ordinary testing and both are
caught by [Miri](#miri-the-verification-gate).

- **Provenance.** A pointer is not just an address. Tagging low bits, computing a header
  address from a payload address, and walking physical neighbors must all preserve the
  provenance of the original OS allocation. Round-tripping through `usize` with `as` strips
  provenance and is UB under Strict Provenance / the Rust memory model. See
  [strict provenance](#strict-provenance).
- **Aliasing.** Producing two live `&mut` to overlapping memory — or a `&mut` while a `*mut`
  to the same bytes is dereferenced — violates Stacked/Tree Borrows even if no write races.
  Prefer raw pointers (`*mut`/`NonNull`) for the duration of metadata surgery and materialize
  a `&mut [u8]` payload slice only at the boundary, for the shortest possible scope.

### Strict Provenance

Use the stable strict-provenance API (stable since Rust 1.84; orisnik's MSRV is 1.85) for
**all** address arithmetic on pointers:

| Need | Use | Never |
|---|---|---|
| Read a pointer's address | `p.addr()` | `p as usize` |
| Set the address, keep provenance | `p.with_addr(a)` | `a as *mut T` |
| Map the address (tag/align/offset) | `p.map_addr(\|a\| …)` | `((p as usize) op x) as *mut T` |
| A pointer with no provenance (sentinel) | `ptr::without_provenance_mut(a)` | `a as *mut T` |
| Cross an FFI/OS boundary (last resort) | `.expose_provenance()` / `ptr::with_exposed_provenance` + `// PROVENANCE:` | bare `as` |

`align_up`, `align_down`, and the `ptr_bits` tag/untag helpers are written **once** over
`map_addr` and reused; no open-coded `as` arithmetic anywhere else.

### `NonNull` over raw pointers

A block, page, or node pointer is never null in valid allocator state. Encode that in the type:
store and pass `NonNull<u8>` / `NonNull<BlockHeader>`, not `*mut`. The only `*mut`/null in the
codebase is at the API edge — the `GlobalAlloc` contract, where allocation failure *is* a null
return. Convert at that boundary (`NonNull::new(p)` → `Option`) and stay `NonNull` inside.

### `Layout`, `MaybeUninit`, `UnsafeCell`

- **`Layout`** is the unit of the public alloc API — size and alignment travel together,
  matching `core::alloc`. Never split them into two `usize` parameters in the public surface.
- **`MaybeUninit`** models freshly-obtained, uninitialized OS pages; do not form a `&[u8]`/`&mut [u8]`
  over memory before it is written. `calloc` zeroes; plain `alloc` returns `MaybeUninit` bytes.
- **Interior mutability.** When the allocator must mutate state through `&self` (the
  `GlobalAlloc` trait takes `&self`), the state lives in `UnsafeCell` (single-threaded v0.1) or,
  in the future multithreaded path, behind the mutex from HPHA's `MULTITHREADED` mode. The
  `UnsafeCell` access is the one place a `// SAFETY:` asserts single-threaded exclusivity.

### Miri: the verification gate

Miri is to orisnik what `cargo-show-asm` vectorization verification is to `anamnesis`: the
evidence that the `unsafe` is actually sound, not merely plausible. The rule mirrors the
`// VECTORIZED:` three-state policy:

- The test suite runs green under `cargo +nightly miri test` with both
  `-Zmiri-strict-provenance` **and** `-Zmiri-tree-borrows` before any `vX.Y.Z` tag — patch
  releases included, since a fidelity fix touches the same `unsafe` the gate exists for.
- A new or modified `unsafe` block is *pending* until it has been exercised by a Miri-covered
  test. A `pending` unsafe path older than one release is a release blocker, not a TODO.
- Provenance and aliasing bugs that escape Miri's per-run coverage are the reason the size-class
  and tree paths each carry a dedicated stress test that Miri runs.

**Reaching the OS boundary under Miri.** Miri cannot interpret `VirtualAlloc` or `mmap`, so
until v0.1.1 the *pending* rule above was quietly unsatisfiable for most of the crate: every
test that actually allocated was `#[cfg_attr(miri, ignore)]`, leaving 22 allocator-path tests —
all of `Orisnik`, the `oris_*` C-ABI, `GlobalAlloc` and the `Allocator` trait — outside the
gate they were supposed to be inside. `os::test_vm` (`os.rs`, `#[cfg(test)]`) closes that: under
Miri, and only under Miri, `os::map`/`os::unmap` are served by a `PAGE_SIZE`-aligned,
zero-filled heap allocation. A native `cargo test` still exercises the real syscalls, so this
adds coverage rather than substituting for it, and `os.rs`'s own tests stay Miri-ignored on
purpose — they are the ones testing the syscalls themselves.

Two consequences for new tests:

- **Do not add `#[cfg_attr(miri, ignore)]` to an allocator test.** It is no longer needed, and
  it silently removes the test from the gate. Reserve it for tests whose *runtime* under Miri is
  prohibitive, and then scale the workload instead where you can (see
  `randomized_alloc_free_stress_matches_the_hpha_benchmark_shape`, which runs a reduced `N`
  under Miri rather than skipping).
- **End an allocating test with `purge()`.** The allocator holds pages until asked, matching
  HPHA — which the stand-in correctly reports to Miri as still-live memory, i.e. a leak. Calling
  `purge()` is both what a well-behaved embedder does and a stronger assertion than omitting it.

`os::test_vm` also carries the out-of-memory injector (`fail_map_after`) that covers every
`None` return on the `system_alloc` path; those tests are Miri-covered too, since a refused map
never reaches the OS at all. The Zig port has the injector but not the stand-in — it has no
Miri, and its `Debug`/`ReleaseSafe` gate already runs against real mappings; see
[`Zig/CONVENTIONS.md`](../Zig/CONVENTIONS.md)'s *Verification gate*.

### MSRV Lint Guard

`lib.rs` carries `#![allow(unknown_lints)]` so a `#[allow(clippy::newer_lint)]` in a test
module does not break the MSRV CI build under `#![deny(warnings)]`. No action is needed when
adding a new `#[allow(clippy::...)]`; the guard covers it. The MSRV floor is **1.85** — one
notch above the 1.84 release that stabilized the strict-provenance APIs the crate relies on,
chosen so the crate can use **edition 2024** (`unsafe extern` blocks and
`#[unsafe(no_mangle)]` / `#[unsafe(export_name)]` attributes for the C-ABI `oris_*` symbols and
the `#[global_allocator]` shim). It is recorded in `Cargo.toml` `rust-version` + `edition` and
in `INSTALL.md`. Develop and run CI on current stable plus nightly (nightly for Miri and the
optional `allocator_api` surface); the MSRV deliberately trails the development toolchain, which
is exactly what the `#![allow(unknown_lints)]` guard above protects against.

---

## When Writing Control Flow

### `if let` vs `match`

| Situation | Preferred form |
|---|---|
| Testing a single variant, no binding | `matches!(expr, Pat)` |
| Testing a single variant, binding needed | `if let Pat(x) = expr { … }` |
| Two+ variants with different bodies | `match expr { … }` |
| Exhaustive dispatch over an enum | `match expr { … }` |

Never a `match` with one non-`_` arm and `_ => {}` where `if let`/`matches!` is clearer.

### EXPLICIT Annotation

`// EXPLICIT: <reason>` — required when a match arm is intentionally a no-op, or when an
imperative loop is used instead of an iterator chain for a stateful computation. Tree rotations,
free-list walks, and coalescing loops are inherently stateful pointer-chasing; they are
imperative by necessity and each carries an `// EXPLICIT:` naming the state being threaded.

> Example: `// EXPLICIT: coalesce-right loop mutates the neighbor link in place; an iterator would hide the splice`

### EXHAUSTIVE Annotation

`// EXHAUSTIVE: <reason>` — on `#[allow(clippy::exhaustive_enums)]`,
`#[allow(clippy::exhaustive_structs)]`, or `#[allow(clippy::wildcard_enum_match_arm)]`.

> Example: `// EXHAUSTIVE: BlockHeader layout is frozen on-heap ABI and part of the cross-port contract`

---

## When Returning Allocation Outcomes

### Allocation outcomes, not `Result`

The hot path does not allocate `Result`, does not format error strings, and does not panic.
Out-of-memory is a **value**, not an exception:

- The C-shaped `oris_alloc` returns `*mut u8` (null on failure), matching `malloc`.
- The idiomatic Rust surface returns `Option<NonNull<[u8]>>` (`None` on failure), matching
  `core::alloc::Allocator::allocate`'s `Result<_, AllocError>` shape (where `AllocError` is a
  zero-data marker).
- `OrisError` and `# Errors` apply **only** to the off-hot-path surfaces: configuration, and
  the `debug-allocator` feature's `check()` / `report()` diagnostics. Those follow the
  house error-wording rules below.

### Error Message Wording (diagnostic paths only)

- External/OS failures: `"failed to <verb>: {e}"`
  > Example: `OrisError::Os(format!("failed to map {bytes} bytes: {e}"))`
- Validation/diagnostic failures: `"<noun> <problem> (<context>)"`
  > Example: `OrisError::Corruption(format!("guard byte mismatch at block {addr:#x} (expected {GUARD:#x})"))`

Lowercase, no trailing period, include the offending value, wrap externals with `: {e}`.

---

## The Cross-Port Invariant

[`ROADMAP.md`](../ROADMAP.md) commits both ports to a property stronger than API parity:

> Given an identical allocation/deallocation sequence at the public API level, `orisnik` and
> `orisnitsa` produce **identical internal state transitions** — same bucket-page spawns, same
> tree-rotation count, same coalescing operations, same final RSS.

This constrains how Rust code is written, not just what it computes:

1. **Determinism.** No `HashMap` iteration order, no address-dependent branching, no
   `Instant`/`Random` in any path that affects state transitions. Tree tie-breaking, free-list
   insertion position, and split/coalesce decisions must be a pure function of the request
   sequence and sizes — identical to the Zig port's.
2. **Field-for-field metadata parity.** The `#[repr(C)]` block header and node layouts
   ([layout lock](#repr-and-layout-lock)) mirror `orisnitsa`'s `extern struct` / `packed
   struct` definitions. A field reorder on one side breaks the invariant and the CI parity gate.
3. **Identical size-class math.** `size_class_of`, the 32 boundaries at 8-byte spacing, and the
   256-byte bucket threshold are one algorithm expressed twice; keep the `const fn` and the
   Zig `comptime` versions provably equal (they share the trace corpus test).
4. **Identical rotation and coalescing order.** When porting HPHA's `intrusive_multi_rbtree`
   rotations and the physical-neighbor coalescing, preserve operation *order*, not just the
   final tree shape — the invariant counts transitions, not just end states.

From v0.3.0 a CI gate replays the shared trace corpus through both ports and asserts a
byte-identical transition record. Treat any change under this section as touching that gate.

---

## `debug_assert!` Invariants

HPHA's `DEBUG_ALLOCATOR` mode becomes, in Rust, a layered scheme:

- **`debug_assert!`** for cheap structural invariants checked on every operation in debug
  builds and compiled out in release: "freed block was marked allocated", "coalesced block size
  equals sum of parts", "size class of returned block ≥ requested size". These are the runtime
  enforcement of the type's [`# Invariants`](#invariants-doc-section) clause.
- **The `debug-allocator` Cargo feature** (the `spomen` module) for the heavyweight HPHA
  machinery — guard bytes, allocation-record tracking, callstack capture, leak detection on
  drop, `check()`/`report()`. `spomen` (*спомен*, "remembrance") is the named twin of the Zig
  port's subsystem, keeping the two debug surfaces parity-comparable. Gated so a release build
  links none of it (zero-cost-when-disabled, matching the Zig port's
  `comptime` bool). This is the Rust analog of `hypomnesis`'s feature-gated backends, applied to
  observability rather than FFI.

Never use `assert!` (always-on) on the hot path for an invariant that `debug_assert!` can carry
— it would tax every release-build allocation.

---

## Idiomatic Surfaces

Per the roadmap, orisnik exposes three layers over one core:

1. **`oris_*` C-shaped functions** (`oris_alloc`, `oris_free`, `oris_realloc`, `oris_calloc`,
   `oris_resize`, `oris_size`, `oris_purge`, `oris_allocated`) — the faithful HPHA surface,
   `*mut u8` / null, alignment-aware and alignment-naive variants.
2. **`unsafe impl GlobalAlloc`** — opt-in as a `#[global_allocator]`. `&self`, `Layout` in,
   `*mut u8` out. The interior-mutability and single-thread `// SAFETY:` contracts live here.
3. **`impl Allocator`** (the typed-instance surface, for `Box::new_in` / `Vec::new_in`) —
   `Result`-shaped, `NonNull<[u8]>`. This is the **only** layer that touches the unstable
   `allocator_api` feature (issue #32838, still unstable as of 1.96), and it needs only a thin
   slice of it: the `Allocator` trait — two required methods (`allocate`, `deallocate`), plus
   `allocate_zeroed` / `grow` / `shrink` overridden for `calloc` / `realloc` efficiency — and
   the `AllocError` marker. Make it an **optional extra, never a stable blocker**: either gate a
   native `core::alloc::Allocator` impl behind a `nightly` cargo feature, or implement
   `allocator-api2`'s stable mirror of the trait (one dependency, works on stable). The default
   build exposes `oris_*` + `GlobalAlloc` and needs none of this; document the nightly
   requirement (if the native path is chosen) in `INSTALL.md`.

All three are thin shells; the bucket/tree core is written once. Each `unsafe impl` documents,
in a `# Safety`-style module comment, exactly which trait preconditions the core upholds (chiefly:
returned blocks meet the requested `Layout`'s size and alignment, and `dealloc` is only sound for
blocks this instance produced).
