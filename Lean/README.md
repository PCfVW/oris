# Lean proofs about `orisnik`

Machine-checked proofs, in [Lean 4](https://lean-lang.org/), about the algorithms `orisnik` (the
Rust port, `../Rust/`) runs: its size arithmetic, its red-black tree, and, to come, its tree-path
memory management. Every theorem is checked by Lean's kernel alone; a CI job also checks that
the models behave exactly like the running Rust code on a 20,000-operation trace.

## Build

Install [elan](https://github.com/leanprover/elan) (it fetches the pinned Lean toolchain by
itself), then from this directory, in bash (on Windows, Git Bash):

```
lake build --wfail
lake exe audit
lake env leanchecker --fresh Oris
```

The build compiles every theorem below without warnings (the first one also downloads and compiles
the Batteries modules the vendored library needs, about a minute). The audit (`Tools/Audit.lean`)
then checks, from outside the build, that every declaration of every proof module rests on the
three standard axioms alone, and lints the proof sources; the kernel replay re-checks every
declaration from scratch (about a minute). The cross-check against the Rust code (needs a Rust
toolchain; `pipefail` makes a failure anywhere in the pipe fail the command):

```
set -o pipefail
cargo test --manifest-path ../Rust/Cargo.toml --lib \
  rbtree::tests::print_lean_model_cross_check_trace -- --ignored --nocapture \
  | grep '^XC' | lake exe xcheck
```

CI runs all four (`../.github/workflows/lean-ci.yml`).

## Layout

| Path | Contents |
|---|---|
| `RBTree/`, `RBTree.lean` | A verified functional red-black tree library, vendored verbatim (`RBTree/NOTICE.md`) |
| `Oris/Arith.lean` | Size arithmetic: `round_up`, `normalize_size`, `MAX_ALLOCATION`, `Tree::grow`, `alloc_aligned`'s guard, the bucket size classes |
| `Oris/RB/Fixup.lean` | `rbtree.rs`'s `insert_fixup`, `insert_counted`, `erase_fixup` and `erase_counted` (its `Node` branch), on zippers |
| `Oris/RB/Heap.lean` | The same functions as pointer code on a model heap, one write per Rust write; the abstraction relation to zippers, and `rotate` proven to perform the zipper rotation (the other proofs are the next steps of `docs/heap-layer.md`) |
| `Oris.lean` | Imports every proof module (what `lake build` builds) |
| `Tools/Audit.lean` | `lake exe audit`: the axiom audit, the import and namespace checks, and the lint, run outside the build |
| `Tools/XCheck.lean` | `lake exe xcheck`: replays `rbtree.rs`'s cross-check trace through both models |
| `docs/heap-layer.md` | The design note for the pointer layer: the model, the theorems to come, the plan |
| `CONVENTIONS.md`, `CLAUDE.md` | How proofs here are written, and the pre-commit checks |

## What is proven

**Size arithmetic** (`Oris/Arith.lean`), on 64-bit words with Rust's exact operators:

- `round_up` computes the mathematical round-up whenever its addition does not overflow
  (`roundUp_spec`); it computes the same word as HPHA's `round_up` for every power-of-two
  alignment up to `2^30` (`hphaMask_eq`, `hphaRoundUp_eq`). Above that, HPHA's mask is undefined
  behaviour at `2^31` (`-INT_MIN`) and a defined but wrong 0 from `2^32` on.
- ERRATA E1, both sides: every request up to `MAX_ALLOCATION` normalizes without overflow to a
  block size that is a multiple of 16, at least the request and at least `MIN_BLOCK_SIZE`
  (`normalizeSize_spec`), and `Tree::grow` cannot overflow on it (`growSize_spec`; composed in
  `alloc_sizes_no_overflow`); HPHA's unchecked normalization of `SIZE_MAX`, computed with HPHA's
  own `round_up` and mask, really is zero (`hpha_normalize_SIZE_MAX`).
- `alloc_aligned`'s guard cannot underflow and leaves enough headroom (`alloc_aligned_guard`).
- The bucket size classes: every `bucket_spacing_function` input in `[1, 256]` maps to one of 32
  buckets whose element size is the smallest class that fits (`bucketSpacing_spec`), and on the
  plain allocation path a small request, clamped and guarded, lands in that bucket
  (`small_alloc_bucket`); the inverse is an inverse; the aligned shortcut agrees on every multiple
  of 8; `clamp_small_allocation` is `max(size, 8 - guard)` (HPHA's guard-aware clamp:
  `max(size, 8)` without the debug guard, the identity with it); and `is_small_allocation` cannot
  be fooled by
  wrap-around (`isSmall_iff`). The aligned bucket path, which rounds up to the alignment first,
  is not covered.

**The red-black tree insert** (`Oris/RB/Fixup.lean`):

- `insFix_toList`: the insert fix-up only rearranges (in-order sequence unchanged).
- `insFix_rotations`: at most two rotations.
- `insFix_balanced`: it restores the red-black invariant.
- `insert_spec`: `insert_counted` on an ordered, valid tree with a black root either finds an
  element equal to the key and chains (tree unchanged, no rotation) or returns a valid, ordered
  tree with a black root holding exactly the elements, in order, of the library's verified
  `RBNode.insert`, after at most two rotations.

**The red-black tree erase** (`Oris/RB/Fixup.lean`):

- `delFix_toList`: the erase fix-up only rearranges.
- `delFix_rotations`: at most three rotations.
- `delFix_balanced`: it restores the red-black invariant, starting from the "double black" a
  spliced-out black node leaves.
- `eraseAt_spec`, `erase_spec`: `erase_counted`'s `Node` branch (splice out the node or its
  in-order successor, `switch_with`, fix-up) on an ordered, valid tree with a black root, for a
  transitive comparison, erasing a key that some element compares equal to, finds that element
  and removes exactly it, keeps all others in order, and leaves a valid tree with a black root,
  after at most three rotations; the lookup fails only when no element compares equal to the
  key, and after it no element left compares equal to the key (`erase_unique`).

**HPHA's assertions, as theorems.** HPHA asserts four facts, at six sites, that the ports
neither check nor prove; each site is a theorem (each with a `_left` and a `_right` form):

- `insert_fixup`, `pp != &mHead`: under a red parent there is a grandparent
  (`hpha_grandparent_not_sentinel`);
- `erase_fixup`, `w != &mHead`, at all three sites: the sibling is never the sentinel at the loop
  top (`hpha_sibling_not_sentinel`), after the first case's block
  (`hpha_sibling_after_case1_not_sentinel`, and the loop top's theorem when the case did not
  run) and after the third (`hpha_sibling_after_case3_not_sentinel`);
- `erase_fixup`: a red sibling has black children (`hpha_red_sibling_children_black`), and before
  the fourth case the far child is red (`hpha_far_child_red`).

**The model agrees with the Rust code.** `rbtree.rs`'s ignored test
`print_lean_model_cross_check_trace` runs 20,000 inserts and erases and prints, after each, the
rotation count and kind, the whole tree of keys with every node's colour, the whole tree again
by node with every node's `parent` word and equal-key chain, and the sentinel's scratch
`parent` word. Keys repeat, so equal-key chains form (2,770 chained inserts, 1,554 `Link` and
1,188 `Promote` erases), and the tree's size goes through phases that drain it to empty 75 times,
so the fix-ups also run at the root (the root changes during 447 erases; every rotation count
from 0 to 3 occurs). `lake exe xcheck` replays the same operations through two Lean models and
fails on any difference:

- the zipper model the theorems are about (`Oris/RB/Fixup.lean`), against the tree of keys;
- the heap model (`Oris/RB/Heap.lean`), which runs the Rust's pointer code write by write on a
  model heap, against the whole line. On every erase it also runs `erase_fixup` with HPHA's
  reading of the root (re-read at each use, where the Rust reads it once) and requires the same
  rotation count and the same heap.

It also fails if the trace is truncated (it ends with an `XC-END` line giving its counts), or if
it stops exercising an operation kind, a rotation count, an emptied tree or a root change. Both
models agree with the Rust on all 20,000 lines, and the two root readings give identical heaps
on all 9,935 erases. `xcheck` was checked to fail on a flipped side bit, a changed chain member
or a changed sentinel field in the trace; on a truncated trace, a stale `XC-END` line, lines
after it, a trace missing a rotation count or never emptying the tree, and empty input; and,
injected into the heap model, on a black new node in `attach_to` and a chain link written the
wrong way in `link_into_chain`. (A wrong side bit in `rotateAt` no longer builds at all:
`rotateAt_refines_left` fails.) The run takes about 15 seconds after building.

## What is not (yet) proven, and the trust base

- **The pointer layer.** The theorems are about the algorithm on zippers. That the pointer code
  in `rbtree.rs` implements it is the next layer (design note:
  [`docs/heap-layer.md`](docs/heap-layer.md)). Its definitions are written
  (`Oris/RB/Heap.lean`, run against the Rust by the cross-check above), and so is the relation
  saying when a heap *is* a `(subtree, path)` pair, with its frame lemmas. One pointer function
  is proven so far: `NodeBase::rotate` performs the zipper rotation (`rotateAt_refines_left`,
  `rotateAt_refines_right`). That the fix-ups and the counted operations perform their zipper steps
  is not proven yet; until it is, that correspondence rests on the write-by-write transcription
  and on the cross-check. The duplicate-key chains, the sentinel's scratch `parent` field, and
  `erase_fixup`'s cached `root` (the Rust reads it once; HPHA, and the zipper model, re-read it;
  the heap model runs both readings and finds no difference) belong to that layer.
- **The `Link` and `Promote` branches** of `erase_counted` and the `Chain` branch of
  `insert_counted` change the equal-key chains, not the tree of keys: they belong to the heap
  layer, where a tree node carries its chain.
- **Memory management** (`tree.rs`'s invariants): after the tree.
- **What Lean does not cover at all:** undefined behaviour, provenance and aliasing (Tree
  Borrows), the lazy sentinel's no-move contract, `Drop`. Miri remains the gate for those.
- **`orisnitsa`.** The theorems are about `orisnik`; they carry over to `orisnitsa` to the extent
  the cross-port invariant holds, which the trace gate checks and nothing proves.

The trust base is Lean's kernel, the three standard axioms, and the faithfulness of the Lean
transcriptions to the Rust: reviewable side by side, cross-checked against the running code, and
to be mechanized by the heap layer. The theorems also assume that the Rust's comparison
(`T::cmp`, for `TestNode` and `FreeNode`) is a lawful total order (`docs/heap-layer.md`, §8).

## Rigour rules

In brief (the full rules, with the reasons, are in [`CONVENTIONS.md`](CONVENTIONS.md)):

1. **Kernel-checked only.** No `sorry`, `native_decide`, `bv_decide` or `axiom`. The audit
   enforces it on every declaration of every Oris and RBTree module (private and auxiliary ones
   included, whatever their names), and lints the proof sources against metaprogramming and
   debug options; the kernel replay re-checks every declaration. Both run in CI on every pull
   request, and were checked to reject each of the four, a theorem added with the kernel check
   switched off, a module redefining the audit command, and an axiom outside the `Oris`
   namespace.
2. **Transcribe, don't re-derive.** Each definition names the Rust it models, follows its
   operations in order and sets every colour the Rust sets; every deliberate departure is listed.
3. **Statements say what the docs say.** A fact a doc claims is proven is a theorem.
4. **Vendored code stays verbatim**, its provenance and any change recorded in its `NOTICE.md`.
5. Every source file begins with `-- SPDX-License-Identifier: MIT OR Apache-2.0` (vendored files
   keep their original headers).
