-- SPDX-License-Identifier: MIT OR Apache-2.0
-- Scratch file from the 2026-11-21 fresh-eyes audit (see ../README.md); as of commit 1a990a9,
-- not maintained and not built by `lake build`. Paths are relative to this folder's parent.
import Oris.RB.Heap
open Oris.RB
#check @Oris.RB.Heap.Heap.modify
#check @Oris.RB.Heap.modify_red
#check @Oris.RB.Side.other
#check @Oris.RB.Heap.nodup_node
#check @Oris.RB.Heap.pathDepth
