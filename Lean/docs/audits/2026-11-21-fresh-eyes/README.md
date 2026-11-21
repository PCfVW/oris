# Fresh-eyes audit of the Lean proofs, 2026-11-21

An audit of `Lean/` as of commit `1a990a9` (`main` after PR #22: heap-layer steps 1, 2, 3a and
3b), done before step 3c. Kept for the record: what was found, what was decided, and which
change addressed it.

## How it was done

Five reviewers, each given the code, `CONVENTIONS.md`, the design note and the Rust, but not
the authors' own view of the weak points. Each covered one dimension:

| Key | Dimension |
|---|---|
| `honesty` | Do the statements say what their docs say? Is every hypothesis needed (tested by deleting it in a scratch file)? |
| `fidelity` | Do the models still transcribe `rbtree.rs`, `tree.rs`, `bucket.rs` and `align.rs` write by write? Are the departures listed? |
| `robustness` | Proofs likely to break on a toolchain bump, duplication, and factorings for step 3c |
| `structure` | Module layout (a split of `Heap.lean`), naming, documentation coherence |
| `readiness` | Can the relation express step 3c's hole invariant? Gaps in `Tools/Audit.lean` and `Tools/XCheck.lean` |

The reviewers were read-only on the repository. Their experiments ran in scratch files, kept in
[`scratch/`](scratch/). A second agent per dimension (all but `readiness`, which is advisory)
then tried to refute each finding, and gave a verdict and its own severity.

## Results

40 findings: 25 confirmed, 9 partly confirmed (real but overstated, or the proposed fix needed
correcting), 1 refuted, and 5 from `readiness`, not verified by an agent. The readiness
counterexamples behind R1 and D1, and the lint gap A1, were re-run by hand. Nothing was rated
high. The fidelity review found no defect in the models.

[`findings.json`](findings.json) holds everything, one entry per dimension:

- `review.summary`: the reviewer's overall assessment;
- `review.findings[]`: `id`, `title`, `severity`, `file`, `line`, `description`, `evidence`,
  `fix`;
- `review.recommendations[]`: advisory items that are not defects;
- `verdicts[]`: for each finding id, `verdict` (`confirmed`, `partly`, `refuted`), `reasoning`,
  `severity` and, where needed, `corrected_fix`. When a verdict corrects the fix, the
  `corrected_fix` is the one to apply.

The `line` numbers refer to commit `1a990a9`.

## Decisions

- **Step 3c's hypothesis** (readiness R1): `eraseFixupLoop_refines` cannot hold for every located
  input, as `insertFixupLoop_refines` does. On an unbalanced tree with an empty sibling, the heap
  model, like the Rust, paints the sentinel red (`scratch/nilsib.lean`). Decided: a predicate
  `DelFixClean path x` in `Fixup.lean`, true when `delFix` never reaches its nil-sibling
  departure, proven from the balance invariant of `delFix_balanced_aux`. The heap theorem
  takes it as a hypothesis.
- **The cached root needs a black root** (readiness D1, `scratch/redroot.lean`): on a red root,
  the two readings leave different heaps. Step 3d takes the black-root hypothesis that
  `insertFixup_refines` takes.
- **The unused frame lemmas** (`rotateAt_parent_fields`, `rotateAt_links`,
  `rotateAt_refines_left_frame`/`_right_frame`, `switchWith_frame`): re-proved robustly now.
  Whichever step 3c does not use is to be reconsidered then.

## Follow-up

Four pull requests, in this order:

- **A, honesty and docs:** the three unneeded hypotheses, the stale and contradictory
  documentation, the step labels 3a–3d, and recording the decisions above.
- **B, the checking tools:** the lint gaps (`#eval!`, `_root_.Lean`, line length) and the
  cross-check's "root changed" coverage item.
- **C, splitting `Heap.lean`** into `Oris/RB/Heap/*.lean`: a move with no change to proofs.
- **D, proof robustness:** per-branch loop lemmas, `Rep.ne_root`, named projections, no `simp [*]`,
  the frame lemmas re-proved, and a robustness section in `CONVENTIONS.md`.
