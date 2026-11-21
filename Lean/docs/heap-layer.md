# Design note — the heap layer (`Oris/RB/Heap.lean`)

*Status: agreed, 2026-11-14. Steps 1, 1b and 2 are done (§5); steps 3 and 4 are not yet
written. Decisions taken are recorded in §7.*

`Oris/RB/Fixup.lean` proves `rbtree.rs`'s red-black algorithm correct **on zippers**: a node
together with its chain of parents is a `(subtree, path)` pair, and the fix-ups are functions on
that pair. What it does not prove is that the Rust's pointer code performs those zipper steps.
Today that correspondence rests on the transcription being reviewable and on the 20,000-operation
cross-check. The heap layer replaces both with a theorem.

It also settles the one open question the first stage left: the ports' `erase_fixup` reads the
root once, where HPHA re-reads it (`ROADMAP.md`, § Machine-checked proofs).

## 1. What the Rust does that the model must capture

From `Rust/src/rbtree.rs`. `orisnitsa`'s node is the same on-heap layout (`NodeBase` is an
`extern struct` in Zig, `#[repr(C)]` in Rust, "frozen" by the cross-port invariant), so the model
covers both ports' layout. The proofs, like the cross-check, are against the Rust's code.

- **A node is five words** (`NodeBase`): `children[2]`, `neighbours[2]` (the equal-key chain),
  and a tagged `parent` word whose bit 0 is the node's colour (1 = red) and bit 1 the side it
  hangs on (1 = right).
- **The sentinel `head` is every empty subtree.** Every nil child link points to `head`.
  `head.children[Left]` is the root, and `head.children[Right] == head` is what `is_nil` tests.
  The root's `parent` is `head`, side left. `head` is black, and must stay black: `insert_fixup`
  stops on `red(p)` when `p` is `head`.
- **`head`'s `parent` and side bit are scratch space.**
  - `erase_counted` writes them through `substitute_with(repl, repl_child)` when `repl_child` is
    `head`. That is how `erase_fixup`, starting from an empty hole, finds the hole's parent and
    side.
  - `switch_with(repl, node)` then overwrites them when one of `node`'s children is `head` at
    the time of the call: in a two-child erase whose successor `repl` was `node`'s right child
    with no right child, it writes the scratch `parent` as `repl`, side right, which is where the
    hole now is. That second value is the one `erase_fixup` reads, so the hole invariant of
    step 4 holds after `switch_with`, not after `substitute_with`.
  - `rotate` overwrites them whenever the child it moves across (`top_s_child`) is `head`.
  - `Fixup.lean` leaves this field out (the "sentinel's scratch `parent`" in its module doc).
- **Equal keys form a chain**, not duplicate tree nodes. One member of each group is attached to
  the tree (non-null `parent`); the others are threaded on `neighbours`, a circular list, with null
  `parent` and null children.
  - `insert_counted`'s `Chain` branch links the new node into the group.
  - `erase_counted`'s `Link` branch unlinks a non-attached member.
  - `Promote` moves the next member into the attached member's tree position (`switch_with`), so
    **a different address now sits at the same tree position, with an equal key**. A two-child
    `Node` erase does the same with the in-order successor.
- **Tree operations never allocate or free.** The caller hands in nodes that already exist, and
  keys never change.

## 2. Modelling decisions (proposed)

| Question | Proposal | Why |
|---|---|---|
| Addresses (**decided**, §7) | `abbrev Addr := Nat`, with `0` as the null pointer and an invariant that no node lives at `0` | The Rust compares against null (`is_attached`, `link_into_chain`), so null should be a value, as in the Rust. Address arithmetic is never needed here. |
| The heap | A total function `Heap := Addr → NodeRec`, updated pointwise | No allocation happens inside tree operations, so there is no domain to track. Liveness is part of the abstraction relation (§3). Pointwise update keeps the frame lemmas trivial. |
| A node | `structure NodeRec where left right prev next parent : Addr; red side : Bool` | One field per Rust field; the tagged word split into its three parts, as `TaggedPtr`'s accessors split it. |
| Keys | A fixed function `key : Addr → α` with a `cmp` satisfying `Std.TransCmp` | Keys never change (§1), and the Rust's `T::cmp` compares the keys of two nodes. |
| The abstract tree | `RBNode Addr`, ordered by `fun a b => cmp (key a) (key b)` | A tree of **addresses**, not of keys, so node identity survives. That identity is what `Promote`, `switch_with` and the cached-root question are about. `Fixup.lean`'s theorems are generic in the element type, so they apply unchanged. |
| Rust functions | One Lean function per Rust function, one heap update per Rust write, **in the Rust's order** | Transcription rule 2 of `CONVENTIONS.md`, now at pointer granularity: each Lean line can be checked against one Rust line. |
| The loops | `insert_fixup` and `erase_fixup` take explicit fuel, plus a theorem that fuel at least the tree's height plus one suffices (each loop spends one unit on its final, failing test) | Keeps the transcriptions executable (see §5, step 1b) and avoids a termination measure that would need the abstraction relation inside the definition. |

## 3. The abstraction relation

The relation says when a heap *is* a given zipper state.

```lean
-- Sketch, not compiled.
/-- In heap `h`, the subtree hanging at address `a`, under `parent` on side `side`, is `t`. -/
inductive Repr (h : Heap) (head : Addr) : Addr → Addr → Bool → RBNode Addr → Prop
  | nil  : Repr h head head parent side .nil        -- an empty subtree is the sentinel itself
  | node : a ≠ head → a ≠ 0 →
           (h a).parent = parent → (h a).side = side → (h a).red = (c == red) →
           Repr h head (h a).left  a false l →
           Repr h head (h a).right a true  r →
           Repr h head a parent side (.node c l a r)
```

- **The empty subtree constrains nothing.** In particular it says nothing about `head`'s scratch
  fields, so writes to them preserve `Repr` without any argument.
- **Back-pointers rule out sharing.** If one address were reachable twice, its `parent` and side
  fields would have to name both positions, so they would be the same position. To be proven as
  `Repr.nodup : Repr h head a p s t → t.toList.Nodup`. It is the lemma that makes frame reasoning
  sound.
- **The ancestors** get a matching relation, `ReprPath h head a path`, defined by recursion on
  the `Path`. For `.left c pp y b`, it says `a`'s parent is `y` with `a` as its left child and
  `b` as its right subtree. It ends at `.root`, where `a`'s parent is `head` and
  `head.children[Left] = a`.
- **A located node** is `Located h head a t path := Repr … a … t ∧ ReprPath h head a path`: the
  heap counterpart of the zipper pair `(t, path)`.
- **A whole tree** is `Tree h head t := Repr h head (h head).left head false t ∧ (h head).right =
  head ∧ (h head).red = false`.
- **Chains** add a map from each attached address to the list of its group's members, read along
  `neighbours`. That is the heap counterpart of "a tree node carries its chain", in a separate
  relation `Groups h t gs` so that the tree proofs don't need it.
- **The frame lemma.** Writes to addresses outside `t.toList`, `head`'s scratch fields included,
  preserve `Repr … t`. Most of the pointer proofs reduce to it.

**Half-done rotations need no relation.** A rotation is straight-line code: `rotate` performs
nine writes and returns. It is proven as one block, `Repr` before and `Repr` after, so the states
between its writes never need describing. The loops are the same: their invariants hold at the
loop head only. This settles the risk I first saw in this step.

**As built (step 2).** The relation is the sketch above, with these changes:
- **The names are `Rep` and `RepPath`.** `Repr` is Lean's printing class, and `deriving Repr`
  inside `Oris.RB.Heap` would no longer mean it.
- **`RepPath` is indexed by the slot, `(p, s)`, and by the slot's occupant**, not by the address
  below. `RepPath h head a p s path` says that `p`'s side-`s` link holds `a` and lies at `path`;
  `Located h head a p s t path := Rep h head a p s t ∧ RepPath h head a p s path`. The occupant is
  an index, never read from `a`'s own record, so the relation is the same for an empty hole,
  where `a` is the sentinel and its `parent` is scratch. And a write that changes the occupant
  (`rotate` putting `b` where `a` was) changes only that index: `RepPath.retarget` proves the
  path otherwise unchanged, once, for every operation that replaces a subtree in place. It asks
  only that the path's other records be kept, so writes off the path (the node `attach_to`
  attaches, the chain member `switch_with` promotes) need no separate frame step.
- **`RepPath` is an inductive predicate**, not a definition by recursion on the `Path`, so that
  proofs can do induction and case analysis on it; its root case reads nothing of `a`'s record
  (the root's `parent` and side are `Rep`'s part).
- **Sides and colours keep their types**: the side is a `Side`, not a `Bool`, and a colour
  `c : RBColor` is linked to the colour bit by `colourBit c`, not `c == red`.

`Rep.nodup` is proven from `Rep` alone, with no separate distinctness hypothesis, by two arguments:
the heap determines the tree below an address (`Rep.unique`), so a node cannot occur below itself;
and climbing `parent` pointers from an address in both subtrees of a node would reach its two
children at the same height, whose side bits differ. The back-pointers are needed for the second:
without them, a node whose two links both point to `c` would represent a tree holding `c` twice.

The frame lemma takes the form "a heap that agrees on every address of `t` represents `t`"
(`Rep.frame`), with a variant for the subtree a rotation moves across, whose first node takes a
new `parent` and side (`Rep.reroot`).

**Left for step 4** (found by the audit of 2026-11-15). `Tree` does not require `head ≠ null`:
in a heap whose sentinel is at `0`, the root reads as not attached, and `erase_counted` would take
the `Link` branch. And nothing constrains `prev` and `next`, which `erase_counted`'s branch choice
(`chained`) reads. The step-4 theorems will add `head ≠ null` (to `Tree`, or as a hypothesis), and
`Groups` must pin `prev = a` for an attached node with no equal-key duplicates; until then, the
step-3 theorems about the `Node` branch take `!chained h node` as a hypothesis.

## 4. The theorems, in order

Each step uses the ones before it.

1. ✅ **`rotate` performs the zipper rotation** (`rotateAt_refines_left`,
   `rotateAt_refines_right`). As built, the list of changed records is a separate theorem for each
   side, `rotateAt_refines_left_frame` and `_right_frame`, and field by field `rotateAt_links` (the
   moving subtree's first node, possibly the sentinel: only its `parent` word) and
   `rotateAt_parent_fields` (the slot's node: only the link that held `a`, plus its `parent` word
   when it is the sentinel and the moving subtree is empty). The heap's `child` and `rotate` are
   named `childAt` and `rotateAt`, apart from the zipper's (§7, decision 4).
   ```lean
   -- Sketch.
   theorem rotateAt_refines (hl : Located h head a t path) (ht : t = .node c l a (.node c' rl b rr)) :
       Located (rotateAt h a .left) head b (Oris.RB.rotate .left t) path
   ```
   The theorem also states exactly which addresses' fields changed: `a`, `b`, `rl`'s root, the
   parent, and `head` when `rl` is empty. Later frame arguments need that list.
2. **`attach_to`, `substitute_with` and `switch_with`.** Each performs the zipper step that
   `insert` (fill the empty hole with a red leaf) or `eraseAt` (splice, then put the successor in
   the erased node's place) performs. `switch_with` is the first theorem where the tree of
   addresses changes but its keys don't.
3. **`insert_fixup` performs `insFix`.** Its loop invariant is `Located h head cur t path`, `p`
   being `cur`'s parent or `head`, plus the colours `insFix` assumes.
4. **`erase_fixup` performs `delFix`.** The loop invariant adds a **hole invariant**: when `cur`
   is `head`, `head`'s scratch parent and side are the hole's. The proof shows the scratch is
   read only in the first iteration, and that no write reaches it before that read. Case 1's
   rotation would clobber it only if `w.child(s)` were the sentinel, which
   `hpha_sibling_after_case1_not_sentinel_*` rules out. Later writes come after the last read.
5. **The cached root (§6).** `erase_fixup` with the root read once produces the same heap and
   the same rotation count as with HPHA's re-reads.
6. **`insert_counted` and `erase_counted`, whole.** The descent loops perform `zoom`. The `Node`
   branches then perform `Oris.RB.insert` and `Oris.RB.erase`. The `Chain`, `Link` and `Promote`
   branches leave the tree of keys unchanged and update `Groups` as described in §1.
7. **The transfer theorems.** `insert_spec` and `erase_spec` restated for the heap operations, so
   that "valid, ordered, the right elements, at most two or three rotations" becomes a statement
   about `rbtree.rs`'s pointer code itself.

## 5. Plan and checkpoints

| Step | Content | Checkpoint |
|---|---|---|
| 0 | This note, agreed | Decisions in §2 accepted or changed |
| 1 ✅ | `Heap.lean`: `NodeRec`, the primitives, executable transcriptions of `rotate`, `attach_to`, `substitute_with`, `switch_with`, both fix-ups (in two variants: cached root and re-read root), and both counted operations | Each definition's doc names its Rust function, and its writes follow the Rust's order |
| 1b ✅ | Extend `lake exe xcheck` to replay the trace through the heap model too, comparing with the Rust's shapes and with the zipper model, and running both root variants. Time the replay | 20,000 operations, 0 mismatches, before any proof is attempted. This also tests the cached-root expectation at heap level, for free |
| 2 ✅ | `Repr`, `ReprPath`, `Repr.nodup`, the frame lemma, `rotateAt_refines` (as built: `Rep`, `RepPath`, `Rep.nodup`, `Rep.frame`, `RepPath.retarget`, `rotateAt_refines_left` and `_right`; §3, §4) | The first refinement theorem; if the encoding is clumsy, it shows here, cheaply |
| 3 | Steps 2–5 of §4 | `insert_fixup` and `erase_fixup` performing `insFix` and `delFix`; the cached-root theorem |
| 4 | Steps 6–7 of §4, chains included | `insert_spec` and `erase_spec` hold for the pointer code |

At every step, the build, the audit, the kernel replay and the cross-check stay green
(`../CLAUDE.md`).

**Running the heap model fast (step 1b).** A heap updated pointwise, executed as is, wraps the
previous heap in one more closure per write, so each read walks back through every earlier
write. Over 20,000 operations, roughly 400,000 writes, that is quadratic. The replay tool
therefore copies the heap into a table after each operation (`fun a => table.getD a default`),
which is extensionally equal to the heap it copies. Reads then cost one lookup, and the proven
definitions do not change: only the tool does the copying. With about 1,000 addresses, that is
about 20 million steps per run. (The Miri run, which interprets the Rust about a thousand times
slower, is limited to the first 1,000 steps; 20,000 is the native length. Natively the Rust
producer takes milliseconds, and the `xcheck` job then took about 50 seconds, mostly building;
with the heap replay, it took between 2 and 3 minutes on GitHub, §7.)

## 6. The cached root, sketched

This is the hardest case: an erase whose hole is empty (`cur = head`), where case 1 rotates at
the root and case 4 follows.

| Step | Rust (root read once: `root₀ = p`) | HPHA (root re-read) |
|---|---|---|
| Entry | `p` = `head`'s scratch parent, `s` = its scratch side, `w = p.child(o)`, red | the same |
| Case 1 | `make_black(w); make_red(p); w := w.child(s); rotate(p, s)`. `head.left` becomes the old `w`, so the root has changed. `head`'s scratch is not touched, because `w.child(s)` is not the sentinel | the same |
| Case 4 | `set_colour(w, colour(p)); make_black(p); make_black(w.child(o)); rotate(p, s)`. `p` is no longer the root, so the root stays the old `w` | the same |
| End of loop | `cur = root₀`, the old `p`. Loop test: `cur == root₀`, so stop | `cur = head.left`, the old `w`. Loop test: `cur` is the root, so stop |
| Final write | `make_black(old p)`. Already black: case 4 just made it so | `make_black(old w)`. Already black: case 1 made it so |

Both final writes leave the heap as it was, so the two heaps are equal.

The general argument follows the same pattern. The root changes only through a rotation at
`p == root`, which means case 1 or case 4 at the root:
- After case 1 at the root, case 2 stops the loop on `red(p)` before `root₀` is compared.
- After case 4, the loop ends at once, and both final `make_black`s land on a node that is
  already black.

The theorem to prove:

```lean
-- Sketch.
theorem eraseFixup_cached_eq (hl : Located h head cur t path) (hb : …)
    (hhole : HoleInv h head cur path) :
    eraseFixupRust fuel h head cur = eraseFixupHpha fuel h head cur
```

It is an equality of whole heaps and rotation counts, so the Rust inherits everything proven
about the HPHA reading. If the theorem turns out false, the counterexample is a fidelity bug in
both ports. It would then be fixed as a patch, with an entry in `Cpp/ERRATA.md`
(`ROADMAP.md`, § Versioning policy).

## 7. Decisions

1. **Null pointers: `0`** (decided 2026-11-14). It is what the Rust compares against. `Option
   Addr` would mostly guard places where null cannot occur: `Repr` (as built, `Rep`) already
   requires every tree node to be non-null (`a ≠ 0`). Null appears in earnest only in the chain
   code, where a few explicit checks cost less than wrapping every `parent` read.
2. **Step 1b stays a permanent CI check** (decided 2026-11-14). The heap replay is part of
   `lake exe xcheck`, so `lean-ci.yml` runs it on every pull request; on GitHub the `xcheck` job
   went from about 50 seconds to between 2 and 3 minutes. The replay then took about 95 seconds
   on the development machine, copying the whole heap into a table after each operation. Since
   the audit of 2026-11-15 it copies only the addresses an operation can reach (the live nodes,
   the sentinel and the operation's node), and the whole replay, with the richer trace (equal
   keys, drains to empty, every node's `parent` word and chain), takes about 15 seconds.
3. **The chains' proofs go in `Heap.lean`** (decided 2026-11-14).
4. **The heap's `child` and `rotate` are `childAt` and `rotateAt`** (decided 2026-11-21). Named
   `child` and `rotate`, as first written, they shadowed the zipper's `Oris.RB.child` and
   `Oris.RB.rotate` inside `Oris.RB.Heap`, so a statement naming both levels had to qualify the
   zipper's, and a file opening both namespaces could not use either name unqualified. The
   theorems about them were renamed with them (`rotate_refines_left` became
   `rotateAt_refines_left`, and so on), following `CONVENTIONS.md`'s `<def>_<property>`.

## 8. What stays outside the heap layer

- **Undefined behaviour, provenance and aliasing.** The model's heap is a total function, with
  no Tree Borrows and no `UnsafeCell`. Miri remains the gate. It runs the first 1,000 steps of
  the cross-check's sequence, so the pointer code of every fix-up case, and of the chain
  operations, runs under it.
- **The lazy sentinel's self-linking** (`head_ptr` on first touch) and its no-move contract. The
  model starts from a self-linked `head`.
- **The descent's calls to `T::cmp`** are modelled as `cmp (key a) (key b)`. That `TestNode`'s
  and `FreeNode`'s `cmp` implement a total order is assumed, as `Fixup.lean` assumes it today.
