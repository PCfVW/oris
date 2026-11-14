# RBTree

Red-black trees for Lean 4, recycled from Batteries.

Most users should switch to `Std.TreeMap` and `Std.TreeSet` from the Lean standard library,
which are mostly drop-in replacements with a larger and more consistent API (notably, they have
no `ToStream` instance yet). This library keeps the old implementation available for code that
still depends on it.

- `RBTree.Basic` defines `RBNode α`, the underlying red-black tree, and the bundled types
  `RBSet α cmp` and `RBMap α β cmp`, ordered by a comparison function `cmp : α → α → Ordering`.
  The tree never stores two elements that compare `.eq` under `cmp`, but `cmp` need not be
  lawful; in `RBMap` only keys are compared. The API covers insertion, erasure, lookup, upper
  and lower bounds, folds, `ForIn` and `Std.ToStream` instances, and set operations such as
  `union`, `sdiff`, `filter`, `mergeWith` and `intersectWith`.
- `RBTree.WF` proves that `insert` and `erase` preserve the ordering and red-black balance
  invariants, which `RBSet` carries as a proof.
- `RBTree.Alter` provides "zipper" paths for in-place updates, with `RBSet.modifyP`,
  `RBSet.alterP` and the corresponding `RBMap.modify` and `RBMap.alter`.
- `RBTree.Depth` shows that a well-formed tree has depth `O(log n)`.
- `RBTree.Lemmas` collects lemmas about membership, lookup, folds and bounds.

```lean
import RBTree
open RBTree

def m : RBMap Nat String compare := RBMap.ofList [(3, "c"), (1, "a"), (2, "b")] compare

#eval m.find? 2                -- some "b"
#eval (m.insert 4 "d").toList  -- [(1, "a"), (2, "b"), (3, "c"), (4, "d")]
#eval (m.erase 1).contains 1   -- false
```

## Usage

Add the cell to your `lakefile.toml` and import `RBTree`:

```toml
[[require]]
name = "batteries-recycling"
git = "https://github.com/leanprover-community/batteries-recycling"
rev = "main"
```

The declarations live in the `RBTree` namespace (`RBTree.RBNode`, `RBTree.RBSet`,
`RBTree.RBMap`); in Batteries they were in the `Batteries` namespace. The library is not
actively maintained.

## Acknowledgements

The red-black tree originates from `Lean.RBMap` in Lean 4 core by Leonardo de Moura. It was
brought to Std (now Batteries) by Mario Carneiro in 2022, who added the correctness proofs, the
depth bound and the zipper API. Later contributions include:

- [std4#274][1] by Chris Wong: non-monotone `RBSet.map`.
- [batteries#738][2], [batteries#739][3] and [batteries#740][4] by Mario Carneiro: `RBSet` and
  `RBMap` lemmas.
- [batteries#775][5] by kei: `Union` and `SDiff` instances.
- [batteries#834][6] by Kim Morrison: API consolidated from Mathlib.
- [batteries#1792][7] by Kim Morrison: deprecated in Batteries and moved to recycling.
- [batteries#1868][8] by François G. Dorais: moved to `Batteries.Recycling`.
- [batteries#1955][9]: moved to this cell.

[1]: https://github.com/leanprover-community/batteries/pull/274
[2]: https://github.com/leanprover-community/batteries/pull/738
[3]: https://github.com/leanprover-community/batteries/pull/739
[4]: https://github.com/leanprover-community/batteries/pull/740
[5]: https://github.com/leanprover-community/batteries/pull/775
[6]: https://github.com/leanprover-community/batteries/pull/834
[7]: https://github.com/leanprover-community/batteries/pull/1792
[8]: https://github.com/leanprover-community/batteries/pull/1868
[9]: https://github.com/leanprover-community/batteries/pull/1955

---

Copyright (c) 2017 Microsoft Corporation and 2022 Mario Carneiro. Released under the Apache 2.0
license, see [LICENSE](../LICENSE).
