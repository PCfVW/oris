# ERRATA — defects in the HPHA reference, and what each port does about them

The Oris ports are defined *relative to* the C++ in this directory (see
[`../ROADMAP.md`](../ROADMAP.md)'s cross-language invariant). That makes every place the
ports knowingly differ from it a fact worth recording once, in one place, rather than
leaving it distributed across code comments and release notes.

This file is that register. It covers four distinct situations, which are easy to
conflate and shouldn't be:

| | |
|---|---|
| **[A. Fixed](#a-defects-the-ports-fix)** | HPHA is wrong; the ports deliberately differ |
| **[B. Preserved](#b-defects-the-ports-preserve)** | HPHA is wrong; the ports reproduce it on purpose |
| **[C. Unreachable](#c-defects-unreachable-through-the-ports-surface)** | HPHA is wrong; no Oris configuration can reach it |
| **[D. Upstream's own](#d-upstreams-own-later-revisions)** | Lazarov fixed it himself, after the source in this directory |

Provenance and licensing live in [`NOTICE.md`](NOTICE.md); this file is only about
behaviour.

## Why this register exists

Two concrete reasons, beyond tidiness.

**The v0.3.0 trace-corpus gate needs it.** That gate replays one trace through the C++
oracle and both ports and asserts the transition records match. Every entry in section A
is a *potential* expected difference. Each entry below therefore carries a
**Trace-visible** verdict: whether the gate should expect the oracle and the ports to
disagree on a trace the C++ can execute without invoking undefined behaviour. Without
this list the gate either fires spuriously or gets weakened until it stops catching
anything.

**The versioning policy depends on it.** [`ROADMAP.md`](../ROADMAP.md#fidelity-fixes-are-patches)
lets a fidelity fix ship as a patch when two conditions hold — the reference decides, and
no previously-correct input changes. An entry here is where the evidence for those two
conditions is recorded, so a later reader can check the reasoning rather than trust it.

## Which reference governs

`hpha.h`/`hpha.cpp` in this directory are the 2007 source (see `NOTICE.md`). A later
revision by the author exists, dated 2012-04-21, and it is **not** what this directory
carries. Diffed in full, the two revisions differ in exactly two places: the
`MULTITHREADED` build toggle (a configuration choice, recorded in `NOTICE.md`) and the
`debug_replace` change recorded as **E9** below — which is the only *behavioural*
difference between them. Anything ported from that
later revision must say so explicitly, entry by entry; the default reference is the
source in this directory.

---

## A. Defects the ports fix

### E1 — unchecked size arithmetic on the tree path

**HPHA:** every `tree_alloc*`/`tree_realloc*`/`tree_resize` opens with
`if (size < sizeof(free_node)) size = sizeof(free_node); size = round_up(size, sizeof(block_header));`,
and `round_up` is a bare mask —
`template<class T> inline T round_up(T x, size_t a) {return (x + (a-1)) & -(int)a;}`
(`hpha.h:117`). `tree_grow` then adds `3 * sizeof(block_header)` and rounds up to
`PAGE_SIZE`. None of it is checked.

**Why it is wrong:** `alloc(SIZE_MAX)` wraps to a normalized size of **zero**. The
allocator maps an arena, splits a zero-payload block out of it, marks it used, and
returns a pointer to a caller expecting `SIZE_MAX` bytes. The first write corrupts the
heap.

**Ports:** both reject any request above `tree::MAX_ALLOCATION` / `tree.MAX_ALLOCATION`
(≈ `usize::MAX − 64 KiB`, derived term-by-term from the headroom each rounding step
needs) before the arithmetic runs. `orisnik` `tree.rs`, `orisnitsa` `tree.zig`.

**Trace-visible:** **No.** The bound is above any allocation a real machine can serve,
and every request above it was already undefined upstream.

**Fixed in:** v0.1.1 (audit finding F1).

### E2 — `calloc`'s unchecked `count * size`

**HPHA:** `void* calloc(size_t count, size_t size) { void* p = alloc(count * size); if (p) memset(p, 0, count * size); return p; }`
(`hpha.h`). The product is computed twice, unchecked, and used for two different
purposes.

**Why it is wrong:** the pairing is what makes it fatal rather than merely wrong. The
wrapped product under-allocates, while the same wrapped value drives the `memset` — so
`calloc(2, SIZE_MAX)` acquires a few bytes and then zeroes exabytes across them. This is
not theoretical: reproduced as an immediate segfault in `orisnik`'s release build during
the 2026-08-29 audit.

**Ports:** `checked_mul` (`orisnik`) / `@mulWithOverflow` (`orisnitsa`); null on overflow.

**Trace-visible:** **No.** Same reasoning as E1.

**Fixed in:** v0.1.1 (audit finding F1, `calloc` half).

### E3 — `free(ptr, origSize)` with `origSize == 0` underflows the size-class index

**HPHA:** `allocator::free(void* ptr, size_t origSize)` (`hpha.h`) tests
`is_small_allocation(origSize)` — true for 0 — then calls
`bucket_free_direct(ptr, bucket_spacing_function(origSize + MEMORY_GUARD_SIZE))`.
`bucket_spacing_function(0)` is `((0 + 7) >> 3) - 1`, which underflows to `SIZE_MAX`.
The same applies to `free(ptr, origSize, oldAlignment)`.

**Why it is wrong:** the underflowed value indexes `mBuckets`, a 32-element array, with
no bounds check. No allocation can legitimately have an original size of 0 — `alloc(0)`
returns `NULL` — so this is a caller error, but HPHA turns it into an out-of-bounds
access rather than reporting it.

**Ports:** all three entry points route a zero `orig_size` through `free`'s
pointer-based dispatch, which re-derives bucket-vs-tree ownership from the pointer and
releases the block correctly regardless. Deliberately not an assert — see
`free_zero_orig_size` / `freeZeroOrigSize` for why.

Worth recording that the consequence was *not* symmetric before the fix: `orisnik` was
contained to a bounds-check panic by Rust's always-on slice check, while `orisnitsa`'s
`ReleaseFast` build has no such check and wrote out of bounds silently — in the build
users ship. A defect inherited identically by both ports can still differ in severity
between them.

**Trace-visible:** **No.** Undefined upstream.

**Fixed in:** v0.1.1 (audit finding F10).

### E4 — `free(ptr, origSize, 0)` computes `round_up(origSize, 0)`

**HPHA:** `allocator::free(void*, size_t, size_t)` computes
`bucket_spacing_function(round_up(origSize + MEMORY_GUARD_SIZE, oldAlignment))`
unconditionally. With `oldAlignment == 0`, `round_up`'s `(x + (a-1)) & -(int)a` becomes
`(v + SIZE_MAX) & 0`, which is 0 — and 0 then underflows `bucket_spacing_function`
exactly as in E3.

**Why it is wrong:** zero is an alignment HPHA *accepts* on the allocation side — its
own precondition is `assert((alignment & (alignment-1)) == 0)`, which passes for zero, so
`alloc(size, 0)` routes to the unaligned path and succeeds. The matching
`free(ptr, size, 0)` is therefore a call a caller can reasonably make, straight into
undefined behaviour. (v0.1.0 had *also* got the allocation side wrong, in the opposite
direction: it checked `is_power_of_two`, which rejects zero, and so aborted where HPHA
succeeds. Both halves were corrected in v0.1.1 — see the ports' `is_hpha_alignment` /
`isHphaAlignment`, which port HPHA's expression verbatim.)

**Ports:** map `old_alignment == 0` to `DEFAULT_ALIGNMENT`, which names exactly the
bucket `alloc(size, 0)` allocated from. Both ports carry a test pinning the two
expressions together across the whole `1..=MAX_SMALL_ALLOCATION` range, so the mapping is
verified rather than argued.

**Trace-visible:** **No.** Undefined upstream.

**Fixed in:** v0.1.1 (audit finding F5, downstream half).

### E5 — bucket→tree aligned realloc copies `elem_size` bytes unconditionally

**HPHA:** in `realloc(void* ptr, size_t size, size_t alignment)`'s bucket branch
(`hpha.h`), when the request cannot stay in a bucket:
`memcpy(newPtr, ptr, ptr_get_page(ptr)->elem_size() - MEMORY_GUARD_SIZE);`

**Why it is wrong:** sound in the branch's *common* case, where `size` is too large for
any bucket and so exceeds `elem_size`. But the branch is also reachable with a small
`size` and merely `alignment > MAX_SMALL_ALLOCATION` — and then `elem_size` (up to 256)
can exceed `size`, while `tree_alloc_aligned` only guarantees room for `size`. The copy
overruns the new block.

**Ports:** copy `min(elem_size, size)`.

**Trace-visible:** **No** for state transitions — it changes only which stale bytes past
the caller's requested size get copied, never a split, coalesce, or page spawn. It *is* a
memory-content difference, so a trace format that hashes payload bytes (rather than
transitions) would see it.

**Fixed in:** v0.1.0.

---

## B. Defects the ports preserve

### E6 — `ptr_in_bucket` can report a false positive

**HPHA:** `ptr_in_bucket` recovers a candidate `page` by rounding the pointer down to
`PAGE_SIZE`, reads a bucket index and marker out of whatever bytes sit there, and trusts
the marker check. For a non-bucket pointer those bytes are not a `page` at all. HPHA's
own comment acknowledges this, and its `#ifndef NDEBUG` build adds an exhaustive scan of
the candidate bucket's page list to catch disagreement.

**Why it is preserved:** the marker check *is* the dispatch mechanism; replacing it would
change how every `free`/`realloc`/`size` call routes, which is exactly what the
cross-port invariant counts. Both ports reproduce it, including the debug-only exhaustive
cross-check.

One addition, in v0.1.1: the ports' cross-check now distinguishes the two directions. A
false positive is this inherited risk. A false *negative* is not inherited — it means the
owning allocator instance was moved after first use (see `Orisnik`'s
`# Address stability`), which is a different bug with a different fix.

**Trace-visible:** No — preserved exactly.

### E7 — `resize(ptr, 0)` asserts rather than answering

**HPHA:** `allocator::resize` opens with `assert(size > 0)`.

**Why it is preserved:** unlike E3 and E4, this one is *guarded* upstream rather than
silently undefined — the assert is the documented contract, not an oversight. Both ports
reproduce it as a `debug_assert!` / `std.debug.assert`, elided in release, where the call
then returns the block's current size unchanged (a harmless answer). The
`std.mem.Allocator` vtable additionally declines a zero `new_len` before it can reach
this, so the assert is unreachable from that surface.

**Trace-visible:** No — preserved exactly.

---

## C. Defects unreachable through the ports' surface

### E8 — 32-bit `block_header` is size-correct but alignment-wrong

**HPHA:** `block_header` (`hpha.h:1075`) is padded to `DEFAULT_ALIGNMENT`
(`sizeof(double)`, 8) past `sizeof(block_header*) + sizeof(size_t)`:
`unsigned char _padding[DEFAULT_ALIGNMENT <= sizeof(block_header*) + sizeof(size_t) ? 0 : ...]`
(`hpha.h:1083`). On a 32-bit build both fields are 4-byte
aligned, so the *size* comes out right while the *alignment* does not — a latent gap in
the 2007 source itself.

**Why it is unreachable:** both ports are 64-bit only, enforced at compile time
(`const _: () = assert!(usize::BITS == 64)` / the `comptime` equivalent), and say so in
`INSTALL.md` and both READMEs. A 32-bit target fails to build rather than
mis-aligning.

**Trace-visible:** N/A.

---

## D. Upstream's own later revisions

### E9 — `debug_replace` loses a live allocation's record when a realloc fails

**Status: not yet addressed. In scope for v0.2.0.**

This is the one entry where the source in this directory is *behind* the author's own
later work, and it lands directly in the v0.2.0 debug-allocator milestone.

**This directory (2007)** has a single `debug_record_map::replace`:

```cpp
this->erase(record);
*record = debug_record(newPtr, size, source);   // unconditional
this->insert(record);
```

**The 2012-04-21 revision** splits it into `replace_begin`/`replace_end` and guards the
overwrite:

```cpp
// replace_end
if (ptr)                                        // <-- only if the alloc succeeded
    *dr = debug_record(ptr, size, source);
this->insert(dr);
```

**Why the 2007 form is wrong:** two of `realloc`'s three debug call sites pass `newPtr`
straight into `debug_replace` with **no null check** —

```cpp
void* newPtr = bucket_realloc(ptr, size + MEMORY_GUARD_SIZE);
debug_replace(ptr, newPtr, size, DEBUG_SOURCE_BUCKETS);   // newPtr may be NULL
...
void* newPtr = tree_realloc(ptr, size + MEMORY_GUARD_SIZE);
debug_replace(ptr, newPtr, size, DEBUG_SOURCE_TREE);      // newPtr may be NULL
```

— and both `bucket_realloc` and `tree_realloc` return `NULL` on allocation failure. The
unconditional overwrite then stores a `NULL`-keyed record, destroying the record of the
**still-live original allocation**. The debug allocator's leak report and `check()` both
lose that block. (The third call site, the bucket→tree path, has its own
`if (!newPtr) return NULL;` earlier and is unaffected.)

The 2012 split also erases the record *before* the new allocation runs rather than after,
which is the structural reason the guard is expressible at all.

**Recommendation for v0.2.0:** port the **2012 `replace_begin`/`replace_end` form**, and
record that choice here and in `NOTICE.md`. Adopting the 2007 form would mean knowingly
porting a defect the author had already fixed — and the failure mode (a lost record for a
live block) is precisely the thing v0.2.0's leak detection exists to catch.

**Trace-visible:** N/A for v0.1.x — nothing in the debug subsystem is ported yet.

---

## Adding an entry

One entry per defect, in the section that matches what the ports actually do about it.
Each needs: what HPHA does (with the function named, so it survives line drift), why it
is wrong, what each port does instead, a **Trace-visible** verdict for the v0.3.0 gate,
and the release that changed it. Where the reasoning also lives in a code comment, name
the function that carries it — the code comment is the detailed argument, this file is
the index.

A change that makes a port *better* than HPHA by some standard other than correctness is
not an entry here: it is a feature, and takes a minor version bump under
[`ROADMAP.md`](../ROADMAP.md#fidelity-fixes-are-patches).
