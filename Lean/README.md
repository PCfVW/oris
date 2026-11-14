# Lean proofs about `orisnik`

Machine-checked proofs, in [Lean 4](https://lean-lang.org/), about the algorithms `orisnik` (the
Rust port, `../Rust/`) runs: its size arithmetic, its red-black tree, and, to come, its tree-path
memory management. Every theorem is checked by Lean's kernel alone; a CI job also checks that
the proven model behaves exactly like the running Rust code.

## Build

Install [elan](https://github.com/leanprover/elan) (it fetches the pinned Lean toolchain by
itself), then from this directory, in bash (on Windows, Git Bash):

```
lake build --wfail
./scripts/check-imports.sh
```

A successful build means every theorem below compiled without warnings and passed the axiom
gate. The first build downloads and compiles the Batteries modules the vendored library needs
(about a minute). The cross-check against the Rust code (needs a Rust toolchain; `pipefail` makes
a failure anywhere in the pipe fail the command):

```
set -o pipefail
cargo test --manifest-path ../Rust/Cargo.toml --lib \
  rbtree::tests::print_lean_model_cross_check_trace -- --ignored --nocapture \
  | grep '^XC ' | lake exe xcheck
```

CI runs all three (`../.github/workflows/lean-ci.yml`).

## Layout

| Path | Contents |
|---|---|
| `RBTree/`, `RBTree.lean` | A verified functional red-black tree library, vendored verbatim (`RBTree/NOTICE.md`) |
| `Oris/Arith.lean` | Size arithmetic: `round_up`, `normalize_size`, `MAX_ALLOCATION`, `Tree::grow`, `alloc_aligned`'s guard, the bucket size classes |
| `Oris/RB/Fixup.lean` | `rbtree.rs`'s `insert_fixup`, `insert_counted`, `erase_fixup` and `erase_counted` (its `Node` branch), on zippers |
| `Oris/Audit.lean`, `Oris/Gate.lean` | The `#audit_axioms` command, and the gate that runs it over everything |
| `Oris.lean` | Imports every proof module (what the gate audits) |
| `Tools/XCheck.lean` | `lake exe xcheck`: replays `rbtree.rs`'s cross-check trace through the model |
| `docs/heap-layer.md` | The design note for the next stage, the pointer layer (proposal) |
| `scripts/check-imports.sh` | Fails if a module under `Oris/` escapes `Oris.lean`, hence the gate |
| `CONVENTIONS.md`, `CLAUDE.md` | How proofs here are written, and the pre-commit checks |

## What is proven

**Size arithmetic** (`Oris/Arith.lean`), on 64-bit words with Rust's exact operators:

- `round_up` computes the mathematical round-up whenever its addition does not overflow
  (`roundUp_spec`); its mask agrees with HPHA's `-(int)a` for every power-of-two alignment up to
  `2^30` (`hphaMask_eq`; above that HPHA's mask is undefined behaviour).
- ERRATA E1, both sides: every request up to `MAX_ALLOCATION` normalizes without overflow to a
  block size that is a multiple of 16, at least the request and at least `MIN_BLOCK_SIZE`
  (`normalizeSize_spec`), and `Tree::grow` cannot overflow on it (`growSize_spec`; composed in
  `alloc_sizes_no_overflow`); HPHA's unchecked normalization of `SIZE_MAX`, computed with HPHA's
  own `round_up` and mask, really is zero (`hpha_normalize_SIZE_MAX`).
- `alloc_aligned`'s guard cannot underflow and leaves enough headroom (`alloc_aligned_guard`).
- The bucket size classes: every small request maps to one of 32 buckets whose element size is
  the smallest class that fits; the inverse is an inverse; the aligned shortcut agrees; and
  `is_small_allocation` cannot be fooled by wrap-around (`bucketSpacing_spec` and neighbours).

**The red-black tree insert** (`Oris/RB/Fixup.lean`):

- `insFix_toList`: the insert fix-up only rearranges (in-order sequence unchanged).
- `insFix_rotations`: at most two rotations.
- `insFix_balanced`: it restores the red-black invariant.
- `insert_spec`: `insert_counted` on a valid tree with a black root either finds an element
  equal to the key and chains (tree unchanged, no rotation) or returns a valid, ordered tree
  with a black root holding exactly the elements, in order, of the library's verified
  `RBNode.insert`, after at most two rotations.

**The red-black tree erase** (`Oris/RB/Fixup.lean`):

- `delFix_toList`: the erase fix-up only rearranges.
- `delFix_rotations`: at most three rotations.
- `delFix_balanced`: it restores the red-black invariant, starting from the "double black" a
  spliced-out black node leaves.
- `eraseAt_spec`, `erase_spec`: `erase_counted`'s `Node` branch (splice out the node or its
  in-order successor, `switch_with`, fix-up) on a valid tree with a black root, erasing a key
  that some element compares equal to, finds that element and removes exactly it, keeps all
  others in order, and leaves a valid tree with a black root, after at most three rotations;
  the lookup fails only when no element compares equal to the key.

**HPHA's assertions, as theorems.** HPHA asserts four facts, at six sites, that the ports
neither check nor prove; each site is a theorem (each with a `_left` and a `_right` form):

- `insert_fixup`, `pp != &mHead`: under a red parent there is a grandparent
  (`hpha_grandparent_not_sentinel`);
- `erase_fixup`, `w != &mHead`, at all three sites: the sibling is never the sentinel at the loop
  top (`hpha_sibling_not_sentinel`), after the first case (`hpha_sibling_after_case1_not_sentinel`)
  and after the third (`hpha_sibling_after_case3_not_sentinel`);
- `erase_fixup`: a red sibling has black children (`hpha_red_sibling_children_black`), and before
  the fourth case the far child is red (`hpha_far_child_red`).

**The model agrees with the Rust code.** `rbtree.rs`'s ignored test
`print_lean_model_cross_check_trace` runs 20,000 operations (inserts and erases of distinct keys;
every rotation count from 0 to 3 occurs, including 71 erases with three) and prints, after each,
the rotation count and the whole tree's shape with every node's colour. `lake exe xcheck`
replays the same operations through the Lean model and fails on any difference: they agree on
all 20,000 lines. `xcheck` was checked to detect an injected one-rotation and one-colour
difference, malformed input, and empty input.

## What is not (yet) proven, and the trust base

- **The pointer layer.** The theorems are about the algorithm on zippers. That the pointer code
  in `rbtree.rs` implements it is the next layer (`Oris/RB/Heap.lean`; design note:
  [`docs/heap-layer.md`](docs/heap-layer.md)): each node with its chain
  of parents is a `(subtree, path)` pair, and each pointer write must be shown to perform the
  corresponding zipper step. Until then, the correspondence rests on the line-by-line
  transcription documented on each definition and on the cross-check above. The duplicate-key
  chains, the sentinel's scratch `parent` field, and `erase_fixup`'s cached `root` (the Rust
  reads it once; HPHA, and the model, re-read it) belong to that layer.
- **The `Link` and `Promote` branches** of `erase_counted` and the `Chain` branch of
  `insert_counted` change the equal-key chains, not the tree of keys: they belong to the heap
  layer, where a tree node carries its chain.
- **Memory management** (`tree.rs`'s invariants): after the tree.
- **What Lean does not cover at all:** undefined behaviour, provenance and aliasing (Tree
  Borrows), the lazy sentinel's no-move contract, `Drop`. Miri remains the gate for those.

The trust base is Lean's kernel, the three standard axioms, and the faithfulness of the Lean
transcriptions to the Rust: reviewable side by side, cross-checked against the running code, and
to be mechanized by the heap layer.

## Rigour rules

In brief (the full rules, with the reasons, are in [`CONVENTIONS.md`](CONVENTIONS.md)):

1. **Kernel-checked only.** No `sorry`, `native_decide`, `bv_decide` or `axiom`; the gate
   enforces it on every build, on every declaration (private ones included), for the vendored
   library too, and was checked to reject each of the four, and a private `native_decide`.
2. **Transcribe, don't re-derive.** Each definition names the Rust it models, follows its
   operations in order and sets every colour the Rust sets; every deliberate departure is listed.
3. **Statements say what the docs say.** A fact a doc claims is proven is a theorem.
4. **Vendored code stays verbatim**, its provenance and any change recorded in its `NOTICE.md`.
5. Every source file begins with `-- SPDX-License-Identifier: MIT OR Apache-2.0` (vendored files
   keep their original headers).
