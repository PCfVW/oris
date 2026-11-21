-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Every proof module. `lake env leanchecker --fresh Oris` replays what is imported here, and
-- `lake exe audit` (Tools/Audit.lean) fails if a module under `Oris/` is missing from this list.
import Oris.Arith
import Oris.RB.Fixup
import Oris.RB.Heap
import Oris.RB.Heap.Model
import Oris.RB.Heap.Rep
import Oris.RB.Heap.Apply
import Oris.RB.Heap.Structural
import Oris.RB.Heap.InsertFixup
