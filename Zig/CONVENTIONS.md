# orisnitsa Coding Conventions (Grit-ORIS, Zig dialect)

This document describes the coding conventions used in `orisnitsa`, the Zig port of Dimitar
Lazarov's **HPHA**. It is the Zig-language sibling of
[`Rust/CONVENTIONS.md`](../Rust/CONVENTIONS.md) and shares its lineage in the
[Amphigraphic coding](https://github.com/PCfVW/Amphigraphic-Strict) discipline (`Grit`).

The two ports are governed by one design and one [Cross-Port Invariant](#the-cross-port-invariant):
given an identical allocation/deallocation sequence, `orisnik` and `orisnitsa` produce
**identical internal state transitions** (see [`ROADMAP.md`](../ROADMAP.md)). This document
keeps the Zig side honest to that contract.

Zig has no Clippy and no rustdoc, so the Rust port's *lint-floor* and *intra-doc-link*
machinery have no direct analog. What carries over is the **annotation discipline** — the
`// SAFETY:`, `// PROVENANCE:`, `// TAG:`, `// ALIGN:`, `// CAST:`, `// INDEX:`, `// EXPLICIT:`
comments — because they document *why* each delicate operation is correct, and that reasoning
must match across the two ports line for line. Zig's compiler enforces much that Clippy
enforces in Rust (`@intCast` is checked in safe builds; unused values error; shadowing is an
error); the annotations cover the reasoning the compiler cannot.

Idiomatic Zig casing is used throughout: `TitleCase` for types, `camelCase` for functions,
`snake_case` for variables, fields, and constants. `zig fmt` is canonical; CI rejects
unformatted code. The project's Bulgarian terms of art (`orisnitsa`, `oris_alloc`,
`razorisvam`, `spomen`, `stopanstvo`) keep diacritic-free Latin transliteration in identifiers;
Cyrillic prose is welcome in `//!` and free-text comments.

## Trigger Checklist

**Before writing any line of code, check which triggers apply.**

| You are about to... | Check these rules |
|---|---|
| Write a `///` or `//!` doc comment | [Doc-comment hygiene](#doc-comment-hygiene), [field-level docs](#field-level-docs) |
| Write a `pub fn` | [`comptime` over runtime](#comptime-over-runtime), [return-value discipline](#allocation-outcomes-are-values) |
| Write a function whose result must be used | [return-value discipline](#allocation-outcomes-are-values) (Zig has no `#[must_use]`; use the type) |
| Write a function that can fail to allocate | [Allocation outcomes are values](#allocation-outcomes-are-values) |
| Write a `struct` that is a block header or tree/list node | [`extern`/`packed` layout lock](#extern-and-packed-layout-lock) |
| Store bits in the low bits of a pointer | [`// TAG:`](#tag-annotation), [pointer ↔ address](#pointer-and-address-conversion) |
| Do pointer arithmetic / round to an alignment | [`// ALIGN:`](#align-annotation), [`@alignCast`](#alignment-and-aligncast) |
| Convert a pointer to/from an integer address | [`// PROVENANCE:`](#provenance-annotation), [pointer ↔ address](#pointer-and-address-conversion) |
| Write a numeric cast (`@intCast`, `@truncate`, `@bitCast`) | [`// CAST:`](#cast-annotation) |
| Index a slice or many-item pointer | [`// INDEX:`](#index-annotation) |
| Write code that touches raw OS memory | [The unsafe-by-nature core](#the-unsafe-by-nature-core), [`// SAFETY:`](#safety-annotation) |
| Allocate where a later step can fail | [`errdefer` cleanup](#errdefer-cleanup) |
| Write a `switch` | [`switch` exhaustiveness](#switch-exhaustiveness), [`// EXPLICIT:`](#explicit-annotation) |
| Touch size-class math, tree rotation, or coalescing | [The Cross-Port Invariant](#the-cross-port-invariant) |
| Assert an internal allocator invariant | [`assert` vs safety checks](#assert-and-safety-checks) |
| Add a debug / instrumentation path | [`comptime` toggles](#comptime-toggles), [the `spomen` subsystem](#the-spomen-debug-subsystem) |
| Implement the allocator interface | [`std.mem.Allocator` vtable](#stdmemallocator-vtable) |

---

## When Writing Doc Comments (`///`, `//!`)

### Doc-Comment Hygiene

Use `///` for declarations and `//!` for the top of a file/module. Zig's doc comments render
in `zig doc`; keep identifiers, types, and terms of art consistent with the prose. Mirror the
Rust port's backtick-hygiene *intent* — name `RB-tree`, `best-fit`, `coalescing`, `size class`,
`purge`, `mmap`, `VirtualAlloc`, and the Bulgarian terms as terms of art, introduced once then
used precisely. Plain `//` line comments carry the annotation grammar (`// SAFETY:`, `// TAG:`,
…); doc comments describe the API.

### Field-Level Docs

Every field of every `pub` struct carries a `///` doc comment. For the intrusive metadata
structs (block headers, tree/list nodes) the doc **must** state:

1. what the field represents,
2. its unit (bytes, size-class index) or valid range,
3. whether it is part of the inline metadata physically preceding the payload, with its byte
   offset and alignment guarantee,
4. for tagged-pointer fields: which low bits carry flags and what they mean.

> Example:
> ```zig
> /// Inline block header. Physically precedes every payload; `@sizeOf` is locked
> /// by `comptime` assert and must equal `orisnik`'s `BlockHeader`.
> const BlockHeader = extern struct {
>     /// Block size in bytes, including this header. Multiple of `ALIGN` (8).
>     size: usize,
>     /// Tagged pointer to the previous physical block. Low bit = `IS_FREE`,
>     /// bit 1 = `IS_LAST`. Untag by clearing `TAG_MASK` before `@ptrFromInt`.
>     link: usize,
> };
> ```

---

## When Writing Function Signatures

### `comptime` over runtime

Zig's `comptime` is the analog of Rust's `const fn`, and it carries the same allocator-critical
weight: **the size-class table, bucket boundaries, and alignment masks are computed at
`comptime`** so they are baked into the binary and size-class lookups constant-fold on the hot
path.

> ✅ `const SIZE_CLASSES: [NUM_CLASSES]usize = comptime buildSizeClasses();`
> ✅ `fn sizeClassOf(bytes: usize) callconv(.@"inline") usize { return (bytes + 7) >> 3; }`

Prefer `comptime` parameters for anything fixed at build time (the size-class count, the page
size, whether the debug subsystem is on) so the compiler specializes the hot path. This is also
how the [debug subsystem](#comptime-toggles) achieves zero-cost-when-disabled.

### Pass by value vs pointer

| Type | Rule |
|---|---|
| Small value (`usize`, size-class index, `Layout`-equivalent struct ≤ 2 words) | Pass by value |
| Large struct, not mutated | Pass by `*const T` |
| Struct mutated in place | Pass by `*T` |
| The allocator state | Pass `*Self` (or via the `std.mem.Allocator` vtable) |

Mark non-aliasing pointer parameters `noalias` where the C source guarantees it (payload vs
metadata never overlap) — it documents the invariant and helps the optimizer, matching HPHA's
restrict-like assumptions.

---

## When Writing Structs

### `extern` and `packed` Layout Lock

Block headers and intrusive node structs have a layout the algorithm depends on byte-for-byte
and that must match the Rust port's `#[repr(C)]` definitions field-for-field (see
[the Cross-Port Invariant](#the-cross-port-invariant)). Therefore:

- Use `extern struct` for guaranteed C-compatible field order/offsets, or `packed struct` only
  where bit-level packing is genuinely required. **Never** the default Zig struct, whose field
  order the compiler may reorder.
- Lock the layout with `comptime` asserts at module scope:
  ```zig
  comptime {
      std.debug.assert(@sizeOf(BlockHeader) == EXPECTED_SIZE);
      std.debug.assert(@offsetOf(BlockHeader, "link") == EXPECTED_LINK_OFFSET);
      std.debug.assert(@alignOf(BlockHeader) == ALIGN);
  }
  ```
  An accidental field change is then a compile error, not silent heap corruption — and the
  asserts double as the human-readable spec the Rust `const _: () = assert!(…)` guards mirror.

---

## When Writing Expressions

These annotations are required **on or immediately before** the line where the pattern occurs.
Apply them as you write the line, not in a review pass. They are the same grammar as the Rust
port so the two codebases read as one reasoning, twice.

### PROVENANCE Annotation

`// PROVENANCE: <which allocation this pointer derives from>` — required wherever a pointer
crosses to/from an integer address (`@intFromPtr` / `@ptrFromInt`). Zig is less formally strict
about provenance than Rust, but the *reasoning* must be identical across ports: the comment
names which OS allocation the resulting pointer belongs to, so the Rust side's
`with_addr`/`map_addr` discipline has a one-to-one Zig counterpart at review time.

> Example: `// PROVENANCE: derived from page_base returned by os.map; address stays within [base, base+len)`

### TAG Annotation

`// TAG: <bits> = <meaning>` / `// UNTAG: <bits cleared>` — required on every pointer-bit pack
or unpack (HPHA's `ptr_bits`). Do the bit math on the `usize` address, then `@ptrFromInt` back;
keep the masking in one helper reused everywhere.

> Example: `// TAG: bit 0 = IS_FREE on the prev-block link`
> Example: `// UNTAG: addr & ~TAG_MASK recovers the aligned header before @ptrFromInt`

### ALIGN Annotation

`// ALIGN: <to what, why>` — required on every alignment round-up/round-down and on every
`@alignCast`. Use `std.mem.alignForward` / `alignBackward` / `isAligned` and a single
`align_up`/`align_down` helper; never open-code the mask twice.

> Example: `// ALIGN: alignForward(size, ALIGN) so the next header lands on an 8-byte boundary`
> Example: `// ALIGN: @alignCast to *BlockHeader; page base from os.map is 64 KiB-aligned ≥ @alignOf(BlockHeader)`

### CAST Annotation

`// CAST: <from> → <to>, <reason>` — required on every `@intCast`, `@truncate`, `@bitCast`, or
`@floatFromInt`-style cast. `@intCast` is checked in safe builds (panics on loss); `@truncate`
and `@bitCast` are deliberate — the comment states which and why.

> Example: `// CAST: usize → u5, size-class index fits in 5 bits (≤ 31), @intCast checked`
> Example: `// CAST: @bitCast pointer address ↔ usize for tag arithmetic`

### INDEX Annotation

`// INDEX: <reason>` — required on every slice index and many-item-pointer index where the
bound is not locally obvious. Safe builds bounds-check slice indexing and panic; the comment
records the proof so the same access can be trusted in `ReleaseFast` (where the check is off).

> Example: `// INDEX: class < NUM_CLASSES, guaranteed by sizeClassOf's clamp`

---

## When Writing Raw-Memory Code (`unsafe`-by-nature)

Zig has no `unsafe` keyword: the whole language is "unsafe" in Rust's sense, with runtime
safety checks that are *on* in `Debug`/`ReleaseSafe` and *off* in `ReleaseFast`/`ReleaseSmall`.
An allocator is exactly the code those checks cannot fully protect — it manufactures the memory
the checks assume. The discipline therefore mirrors the Rust port's `unsafe` policy.

### The unsafe-by-nature core

1. **Concentrate, don't scatter.** All raw pointer manipulation lives in the core modules
   (`bucket`, `tree`, `block`, `os`). The public surface (`Allocator` vtable, `oris_*` shims)
   is a thin shell; a caller never writes pointer arithmetic.
2. **One operation, one justification.** Each delicate operation (a `@ptrFromInt`, a
   `@ptrCast`+`@alignCast`, a tagged read) gets its own `// SAFETY:` comment. Do not bundle a
   cast, a deref, and an offset under one comment.
3. **Prove, don't assert.** Every `// SAFETY:` discharges a named precondition documented on
   the function or the struct's invariants. "Should be fine" is not a safety comment.

### SAFETY Annotation

`// SAFETY: <invariants + how established here>` — required on every block of raw-pointer
manipulation: pointer casts, `@ptrFromInt`/`@intFromPtr`, `@ptrCast`, forming a slice over raw
memory, and any `@setRuntimeSafety(false)` region.

> Example:
> ```zig
> // SAFETY: header lies ALIGN bytes before a pointer this allocator returned
> // (caller contract of free); it is a live, aligned BlockHeader, and the
> // single-threaded invariant guarantees no concurrent access.
> const block: *BlockHeader = @ptrFromInt(addr);
> ```

### Pointer and Address Conversion

Use `@intFromPtr` to read an address and `@ptrFromInt` to rebuild a pointer; never `@bitCast`
between pointer and integer for this purpose. Keep the tag/untag arithmetic in one helper
(`tagLink` / `untagLink`) so the bit layout lives in exactly one place and matches `orisnik`'s
`map_addr` helper.

### Alignment and `@alignCast`

`@ptrCast` changes the pointee type; `@alignCast` re-establishes an alignment the type system
lost. Every `@alignCast` carries an `// ALIGN:` naming the source of the alignment guarantee
(the OS page alignment, or a prior `alignForward`). In safe builds `@alignCast` is checked;
in `ReleaseFast` the `// ALIGN:` comment is the only remaining proof.

### `@setRuntimeSafety`

The bucket hot path may use `@setRuntimeSafety(false)` in a tightly scoped block to drop bounds
and overflow checks where the [`// INDEX:`](#index-annotation) / [`// CAST:`](#cast-annotation)
proofs already guarantee correctness — the analog of pre-validating once and iterating
branch-free. Each such block is small, carries a `// SAFETY:` explaining which checks are being
dropped and why they are provably unnecessary, and is covered by a `Debug`-build test where the
checks *are* on. Never disable safety to paper over a bound you have not proven.

### Verification gate

`Debug` and `ReleaseSafe` builds keep every runtime check on; the full test suite runs under
both before any `vX.Y.0` tag, plus `std.testing.allocator` (leak detection) wrapping the
allocator-under-test and `std.testing.checkAllAllocationFailures` to exercise every
allocation-failure path. This is the Zig analog of the Rust port's Miri gate: it is the
evidence the raw-memory code is sound, not merely plausible. A new raw-memory path is *pending*
until a safe-build test exercises it; a pending path older than one release is a release
blocker.

---

## When Allocating Where Later Steps Can Fail

### `errdefer` Cleanup

Any function that acquires a resource (an OS page, a spawned bucket page, a tree node) and then
performs a further fallible step must release it with `errdefer` on the error path. This is
Zig's structured answer to the leak-on-partial-init bug class — pair every acquisition with its
`errdefer` immediately, before the next fallible call.

> ✅
> ```zig
> const page = try os.map(PAGE_SIZE);
> errdefer os.unmap(page);
> try self.registerPage(page); // if this fails, the page is unmapped
> ```

---

## When Returning Allocation Outcomes

### Allocation outcomes are values

The hot path neither panics nor formats messages. Out-of-memory is a value:

- The C-shaped `oris_alloc` returns `?[*]u8` (null on failure), matching `malloc`.
- The `std.mem.Allocator` vtable's `alloc` returns `?[*]u8` per Zig's interface contract;
  higher-level helpers surface `error.OutOfMemory` only where Zig's `Allocator` API already
  does (`std.mem.Allocator.create`, `alloc`).
- Reserve Zig error sets (`error{...}`) for the off-hot-path surfaces: configuration and the
  `spomen` debug subsystem's `check()` / `report()`. Diagnostic message wording follows the
  Rust port: lowercase, no trailing period, include the offending value, `"failed to <verb>"`
  for OS failures and `"<noun> <problem> (<context>)"` for validation.

---

## When Writing Control Flow

### `switch` Exhaustiveness

Prefer `switch` over `if`/`else if` chains for enum dispatch; Zig requires `switch` over an
enum to be exhaustive (or carry an explicit `else`). Use an explicit `else => unreachable` only
where the invariant truly forbids the other cases, and annotate it `// EXPLICIT:`.

### EXPLICIT Annotation

`// EXPLICIT: <reason>` — required when a `switch` arm or `else` is intentionally a no-op or
`unreachable`, or when an imperative loop is used instead of a higher-level construct for a
stateful computation. Tree rotations, free-list walks, and coalescing are inherently stateful
pointer-chasing; each carries an `// EXPLICIT:` naming the state being threaded — matching the
Rust port's annotation on the same loop.

> Example: `// EXPLICIT: coalesce-right loop splices the neighbor link in place; state is the running merged size`

---

## The Cross-Port Invariant

[`ROADMAP.md`](../ROADMAP.md) commits both ports to a property stronger than API parity:

> Given an identical allocation/deallocation sequence at the public API level, `orisnik` and
> `orisnitsa` produce **identical internal state transitions** — same bucket-page spawns, same
> tree-rotation count, same coalescing operations, same final RSS.

This constrains how Zig code is written, not just what it computes:

1. **Determinism.** No iteration-order dependence, no address-dependent branching, no time or
   randomness in any path affecting state transitions. Tree tie-breaking, free-list insertion
   position, and split/coalesce decisions are a pure function of the request sequence and
   sizes — identical to the Rust port's.
2. **Field-for-field metadata parity.** The `extern`/`packed` header and node layouts
   ([layout lock](#extern-and-packed-layout-lock)) mirror `orisnik`'s `#[repr(C)]` structs,
   enforced on both sides by `comptime`/`const` size and offset asserts.
3. **Identical size-class math.** `sizeClassOf`, the 32 boundaries at 8-byte spacing, and the
   256-byte bucket threshold are one algorithm expressed twice; the `comptime` table and the
   Rust `const fn` are provably equal and share the trace-corpus test.
4. **Identical rotation and coalescing order.** Porting HPHA's `intrusive_multi_rbtree` and the
   physical-neighbor coalescing preserves operation *order*, not just final shape — the
   invariant counts transitions.

From v0.3.0 a CI gate replays the shared trace corpus through both ports and asserts a
byte-identical transition record. Treat any change under this section as touching that gate.

---

## `assert` and Safety Checks

HPHA's `DEBUG_ALLOCATOR` mode becomes, in Zig, a layered scheme:

- **`std.debug.assert`** for cheap structural invariants checked on every operation in `Debug`
  /`ReleaseSafe` and compiled out in `ReleaseFast`: "freed block was marked allocated",
  "coalesced size equals sum of parts", "returned class ≥ requested size". These are the
  runtime enforcement of each struct's documented invariants. (`std.debug.assert` is itself
  elided in `ReleaseFast`, so it is the correct tool for hot-path invariants — never a bare
  `if (!cond) unreachable` that you intend to keep in release.)
- **The Zig runtime safety checks** (bounds, overflow, alignment, `undefined` access) provide a
  second, free layer in `Debug`/`ReleaseSafe`; the `// INDEX:`/`// CAST:`/`// ALIGN:`
  annotations are the proofs that the same code is correct once `ReleaseFast` turns those off.

---

## `comptime` Toggles and the `spomen` Debug Subsystem

### `comptime` Toggles

The heavyweight HPHA debug machinery — guard bytes, allocation-record tracking, callstack
capture, leak detection on `deinit` — is gated behind a `comptime bool` config field (the Zig
analog of the Rust port's `debug-allocator` Cargo feature). When the bool is `false`, the
branches are `comptime`-eliminated and the release binary links none of it:
zero-cost-when-disabled, and parity-guaranteed with the Rust feature gate.

> ```zig
> pub const Config = struct {
>     /// Enables the `spomen` debug subsystem. comptime so all instrumentation
>     /// is eliminated when false. Parity: `orisnik`'s `debug-allocator` feature.
>     debug: bool = false,
> };
> ```

### The `spomen` Debug Subsystem

`spomen` (*спомен*, "remembrance") is the instrumentation cousin of the allocator family. It
owns guard-byte writing/checking, the allocation record store, leak reporting, and the
`check()` / `report()` diagnostics. It is the one place error sets and message formatting are
allowed; the core allocator stays value-returning and panic-free. Its record contents must match
the Rust port's `debug-allocator` records (modulo platform-specific callstack symbols), per the
cross-port parity goal in the roadmap.

---

## `std.mem.Allocator` vtable

Per the roadmap, `orisnitsa` exposes three layers over one core:

1. **`oris_*` C-shaped functions** (`oris_alloc`, `oris_free`, `oris_realloc`, `oris_calloc`,
   `oris_resize`, `oris_size`, `oris_purge`, `oris_allocated`) — the faithful HPHA surface,
   `?[*]u8` / null, alignment-aware and alignment-naive variants.
2. **`std.mem.Allocator` interface** — implement the vtable (`alloc`, `resize`, `free`, and
   `remap` on Zig versions that have it) so `orisnitsa` drops into any code that takes a
   `std.mem.Allocator`. The `Allocator.VTable` function pointers carry the `// SAFETY:`
   contracts: returned memory meets the requested length and alignment; `free`/`resize` are
   sound only for blocks this instance produced.
3. **An `Orisnitsa` owning type** (орисница — the allocator, feminine twin) that holds the
   governed address space (`stopanstvo`, стопанство — "the heap as a whole") and exposes
   `.allocator()` to hand out the vtable, plus `deinit()` for teardown and leak reporting under
   the [debug subsystem](#comptime-toggles). Its sub-allocators (`bucket`, `tree`) are
   collectively the *orisnitsi*.

Pin the targeted Zig version in `build.zig.zon` and `INSTALL.md` — target **Zig 0.16.0**
(current stable as of mid-2026; 0.15.x is one series behind, and 0.17.0 is imminent). The
`std.mem.Allocator` vtable signature has changed across Zig releases (notably the `alignment`
representation and the addition of `remap`, which shifted around the 0.15 → 0.16 boundary), and
the cross-port invariant is defined against a specific interface shape — so the pin is
load-bearing, not cosmetic, while Zig remains pre-1.0.
