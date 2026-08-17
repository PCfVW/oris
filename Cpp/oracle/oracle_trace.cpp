// SPDX-License-Identifier: MIT OR Apache-2.0

// oracle_trace.cpp — the C++ side of the three-way (C++/Rust/Zig) RB-tree
// cross-validation. Links against the real, unmodified `../hpha.h`/`../hpha.cpp`
// (never modified — see `../NOTICE.md`) and drives `intrusive_multi_rbtree<T>`
// through the identical PRNG-seeded insert/erase sequence, and prints the identical
// in-order trace format, as:
//
//   - `Rust/src/rbtree.rs`'s `#[ignore]`d
//     `rbtree::tests::print_oracle_cross_validation_trace`
//   - `Zig/src/rbtree.zig`'s skipped-by-default
//     `"oracle cross-validation trace (manual tool, not an assertion)"`
//
// All three must produce byte-identical stdout across the full 3000-step run for the
// cross-port invariant's RB-tree slice (ROADMAP.md) to hold. See `README.md` in this
// directory for the build/run/diff recipe. Manual tool, not part of this repo's CI —
// HPHA (and therefore this file) is Windows-only by `../hpha.h`'s own `#error` guard.

#include "../hpha.h"

#include <cstdio>
#include <vector>

namespace {

// The tree node under test. `intrusive_multi_rbtree<T>::node` must be T's first (and
// here, only) base so `node::data()`'s `*(T*)this` cast is valid — the same layout
// `../hpha.h`'s own `debug_record : public intrusive_multi_rbtree<debug_record>::node`
// relies on.
struct TestNode : public intrusive_multi_rbtree<TestNode>::node {
    int key;
    unsigned step;

    TestNode(int k, unsigned s) : key(k), step(s) {}

    // Required by intrusive_multi_rbtree's do_insert for tree-order comparisons;
    // this harness never calls lower_bound/upper_bound/find, so no comparison
    // against a bare key is needed.
    bool operator<(const TestNode& rhs) const { return key < rhs.key; }
    bool operator>(const TestNode& rhs) const { return key > rhs.key; }
};

// xorshift32, seeded identically to both ports' oracle-trace tests.
struct Xorshift32 {
    unsigned state = 0x12345678u;
    unsigned next() {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        return state;
    }
};

}  // namespace

int main() {
    Xorshift32 rng;
    intrusive_multi_rbtree<TestNode> tree;
    std::vector<TestNode*> live;

    for (unsigned step = 0; step < 3000; ++step) {
        int key = static_cast<int>(rng.next() % 32);
        bool do_insert = live.empty() || (rng.next() % 3 != 0);

        if (do_insert) {
            TestNode* n = new TestNode(key, step);
            tree.insert(n);
            live.push_back(n);
        } else {
            // swap_remove, matching orisnik's Vec::swap_remove / orisnitsa's
            // swapRemove exactly — the *position* selected by `idx` on every later
            // step depends on this history, so the three implementations must pick
            // the identical live-list occupant at every step, not just the same
            // count.
            std::size_t idx = static_cast<std::size_t>(rng.next()) % live.size();
            TestNode* n = live[idx];
            live[idx] = live.back();
            live.pop_back();
            tree.erase(n);
            delete n;
        }

        for (intrusive_multi_rbtree<TestNode>::iterator it = tree.begin(); it != tree.end(); ++it) {
            std::printf("%d ", it->key);
        }
        std::printf("\n");
    }

    for (std::vector<TestNode*>::iterator it = live.begin(); it != live.end(); ++it) {
        tree.erase(*it);
        delete *it;
    }

    return 0;
}
