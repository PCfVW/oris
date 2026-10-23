// SPDX-License-Identifier: MIT OR Apache-2.0

// letopis_hooks.h — the transition-event hooks `letopis.patch` adds to a *scratch copy* of
// HPHA, so that the 2007 reference can write the same transition record as `orisnik` and
// `orisnitsa` (see `../../examples/traces/GRAMMAR.md` §2 and `../../examples/traces/EVENTS.md`).
//
// `../hpha.h` and `../hpha.cpp` are never modified: `build_trace_oracle.ps1` copies them to a
// build directory and applies `letopis.patch` there. The patch adds one `#include` of this
// header and one call per hook site, at exactly the HPHA lines `EVENTS.md` names; this header
// only declares what those calls need. `trace_replay.cpp` defines all of it.

#ifndef LETOPIS_HOOKS_H
#define LETOPIS_HOOKS_H

#include <cstddef>

// One record event (GRAMMAR.md §2.3). `a` is always an address (a mapping base, a page, or a
// block header); `b` a size, an offset or a bucket index, as each event needs.
enum letopis_event_type {
	LETOPIS_MAP_BUCKET,   // a: base, b: bytes
	LETOPIS_MAP_TREE,     // a: base, b: bytes
	LETOPIS_UNMAP,        // a: base, b: bytes
	LETOPIS_PAGE_SPAWN,   // a: page, b: bucket index
	LETOPIS_PAGE_RELEASE, // a: page, b: bucket index
	LETOPIS_PAGE_FULL,    // a: page, b: bucket index
	LETOPIS_PAGE_REFILL,  // a: page, b: bucket index
	LETOPIS_SPLIT,        // a: block, b: payload size kept
	LETOPIS_SHIFT,        // a: block, b: offset
	LETOPIS_MERGE,        // a: absorbed block
	LETOPIS_TREE_INSERT,  // a: block, b: size; branch and rotations from the globals below
	LETOPIS_TREE_ERASE,   // a: block, b: size; branch and rotations from the globals below
	LETOPIS_LIST_PUSH,    // a: block, b: size
	LETOPIS_LIST_ERASE,   // a: block, b: size
	LETOPIS_MR            // a: block, or NULL for "the cache is empty"
};

// Which branch of `intrusive_multi_rbtree::do_insert`/`do_erase` ran last: set by the patch
// inside those two templates, read when the `tree+`/`tree-` event is emitted.
enum letopis_branch_type {
	LETOPIS_BRANCH_CHAIN,   // do_insert: linked into an equal-key chain
	LETOPIS_BRANCH_NODE,    // do_insert or do_erase: a real tree node
	LETOPIS_BRANCH_LINK,    // do_erase: a chain member that is not the head
	LETOPIS_BRANCH_PROMOTE  // do_erase: a chain head, its successor promoted
};

extern int letopis_branch;
// Rotations since the last reset: the patch zeroes it right before `mFreeTree.insert`/`erase`
// in `tree_attach`/`tree_detach` and increments it after each of the five `rotate` calls in
// `insert_fixup`/`erase_fixup`.
extern unsigned letopis_rotations;

void letopis_event(letopis_event_type type, const void* a, size_t b);

#endif // LETOPIS_HOOKS_H
