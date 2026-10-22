# Transition-record events — where each one is emitted

The transition record ([`GRAMMAR.md`](GRAMMAR.md) §2) is only as good as the agreement on *where*
each event fires. This table is that agreement: for every event, the HPHA function that performs
the transition (the specification) and the function in each port that emits it. A port that
performs a transition somewhere else — or performs it without emitting — breaks the gate.

Functions are named rather than given by line, so the table survives line drift (the same
convention as [`Cpp/ERRATA.md`](../../Cpp/ERRATA.md)). The C++ events come from
[`Cpp/oracle/letopis.patch`](../../Cpp/oracle/letopis.patch), applied to a scratch copy of
`hpha.h`/`hpha.cpp` at build time; the reference files themselves are never modified.

| Event | HPHA (`Cpp/hpha.*`) | `orisnik` (`Rust/src/`) | `orisnitsa` (`Zig/src/`) |
|---|---|---|---|
| `map b` | `allocator::bucket_system_alloc` | `bucket.rs` `Buckets::system_alloc` | `bucket.zig` `Buckets.systemAlloc` |
| `map t` | `allocator::tree_system_alloc` | `tree.rs` `Tree::system_alloc` | `tree.zig` `Tree.systemAlloc` |
| `unmap` (bucket page) | `allocator::bucket_system_free` | `bucket.rs` `Buckets::system_free` | `bucket.zig` `Buckets.systemFree` |
| `unmap` (tree arena) | `allocator::tree_system_free` | `tree.rs` `Tree::system_free` | `tree.zig` `Tree.systemFree` |
| `page+` | after `add_free_page` in `allocator::bucket_alloc` and `allocator::bucket_alloc_direct` | `bucket.rs` `Buckets::alloc_direct` | `bucket.zig` `Buckets.allocDirect` |
| `page-` | `allocator::bucket_purge`, before `bucket_system_free` | `bucket.rs` `Buckets::purge` | `bucket.zig` `Buckets.purge` |
| `page-full` | `allocator::bucket::alloc`, the "auto sort to back" branch | `bucket.rs` `Bucket::alloc` | `bucket.zig` `Bucket.alloc` |
| `page-refill` | `allocator::bucket::free`, the "auto sort to front" branch | `bucket.rs` `Bucket::free` | `bucket.zig` `Bucket.free` |
| `split` | `allocator::split_block` | `tree.rs` `Tree::split` (wraps `split_block`) | `tree.zig` `Tree.split` (wraps `splitBlock`) |
| `shift` | `allocator::shift_block` | `tree.rs` `Tree::shift` (wraps `shift_block`) | `tree.zig` `Tree.shift` (wraps `shiftBlock`) |
| `merge` | every `block_header::unlink` of a block that disappears: `allocator::coalesce_block` (next, then self into prev), and the in-place absorptions in `tree_realloc`, `tree_realloc_aligned` and `tree_resize` | `tree.rs` `Tree::merge` (wraps `BlockHeader::unlink`), called from the same functions | `tree.zig` `Tree.merge` (wraps `BlockHeader.unlink`), called from the same functions |
| `tree+` | `allocator::tree_attach`, flushing the previous most-recently-freed block (`intrusive_multi_rbtree::do_insert` decides `chain`/`node`; `insert_fixup` rotates) | `tree.rs` `Tree::attach` (via `rbtree.rs` `insert_counted`) | `tree.zig` `Tree.attach` (via `rbtree.zig` `insertCounted`) |
| `list+` | `allocator::tree_attach`, flushing a block of at most 256 bytes | `tree.rs` `Tree::attach` | `tree.zig` `Tree.attach` |
| `mr` | `allocator::tree_attach` (`mr <blk>`, or `mr -` from `tree_attach(NULL)`); `allocator::tree_detach` of the cached block (`mr -`) | `tree.rs` `Tree::attach`, `Tree::detach` | `tree.zig` `Tree.attach`, `Tree.detach` |
| `tree-` | `allocator::tree_detach` (`intrusive_multi_rbtree::do_erase` decides `link`/`promote`/`node`; `erase_fixup` rotates) | `tree.rs` `Tree::detach` (via `rbtree.rs` `erase_counted`) | `tree.zig` `Tree.detach` (via `rbtree.zig` `eraseCounted`) |
| `list-` | `allocator::tree_detach` | `tree.rs` `Tree::detach` | `tree.zig` `Tree.detach` |

## Rules for changing this table

- **Every row lands in all three columns in the same commit.** A new transition, or a moved one,
  is a change under the cross-port invariant ([`ROADMAP.md`](../../ROADMAP.md)); the committed
  `*.record` files are then regenerated from the C++ oracle and both ports must reproduce them.
- **Emit where HPHA performs the transition, not where it is convenient.** The record is ordered,
  so an event emitted one call too early or too late is a divergence even when the final state
  agrees.
- **Teardown emits nothing.** `orisnik`'s `Drop` and `orisnitsa`'s `deinit` release memory by
  different means (see the roadmap's scope note); every replayer writes its summary and
  uninstalls its event log before tearing the allocator down.
