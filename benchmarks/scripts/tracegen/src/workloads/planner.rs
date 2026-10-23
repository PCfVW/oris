// SPDX-License-Identifier: MIT OR Apache-2.0
//! A goal-oriented planner's allocation pattern — the brief's canonical workload
//! (`BRIEF.md`, "Target workloads").
//!
//! One plan is a best-first search. Expanding a node allocates its children, each a plan
//! node, a copy of the world state and a few precondition records: all small, all on the
//! bucket path, all short-lived. The open list is one growing buffer, reallocated as it
//! doubles. Dead ends are pruned as the search goes, and a scratch working set (a large
//! block) comes and goes now and then. When the plan is found everything it allocated is
//! released, and every few plans the planner returns its idle pages with `purge`, the
//! "bounded lifetime" the brief describes.

use crate::builder::{TraceBuilder, log_uniform};
use rand::Rng;
use rand::seq::SliceRandom;
use rand_chacha::ChaCha8Rng;

/// The handles one expanded node owns.
struct Node {
    node: u64,
    state: u64,
    preconditions: Vec<u64>,
}

/// Writes plans into `trace` until it holds at least `ops` operations.
pub fn generate(trace: &mut TraceBuilder, rng: &mut ChaCha8Rng, ops: u64) {
    let mut plans = 0u64;
    while trace.ops() < ops {
        plan(trace, rng, ops);
        plans += 1;
        if plans % 4 == 0 {
            trace.purge();
        }
    }
}

fn plan(trace: &mut TraceBuilder, rng: &mut ChaCha8Rng, ops: u64) {
    let mut open_capacity: u64 = 64; // entries of 8 bytes
    let open = trace.alloc(open_capacity * 8);
    let mut open_len: u64 = 0;
    let mut nodes: Vec<Node> = Vec::new();
    let expansions = rng.gen_range(40..400);
    for _ in 0..expansions {
        if trace.ops() >= ops {
            break;
        }
        for _ in 0..rng.gen_range(1..=6) {
            let node = trace.alloc(48 + 8 * rng.gen_range(0..14));
            let state = trace.alloc(64 + 8 * rng.gen_range(0..24));
            let preconditions = (0..rng.gen_range(0..4))
                .map(|_| trace.alloc(16 + 8 * rng.gen_range(0..4)))
                .collect();
            nodes.push(Node {
                node,
                state,
                preconditions,
            });
            open_len += 1;
            if open_len > open_capacity {
                open_capacity *= 2;
                trace.realloc(open, open_capacity * 8);
            }
        }
        // Prune a dead end: one of the most recent nodes and everything it owns.
        if rng.gen_bool(0.3) && !nodes.is_empty() {
            let recent = nodes.len().saturating_sub(8);
            let index = rng.gen_range(recent..nodes.len());
            release(trace, rng, nodes.swap_remove(index));
            open_len = open_len.saturating_sub(1);
        }
        // A scratch working set: a heuristic table, a path buffer.
        if rng.gen_bool(0.02) {
            let scratch = trace.alloc(log_uniform(rng, 1024, 64 * 1024));
            trace.free(scratch, rng);
        }
    }
    // The plan is found: everything goes, in no particular order.
    nodes.shuffle(rng);
    for node in nodes {
        release(trace, rng, node);
    }
    trace.free(open, rng);
}

fn release(trace: &mut TraceBuilder, rng: &mut ChaCha8Rng, node: Node) {
    for p in node.preconditions {
        trace.free(p, rng);
    }
    trace.free(node.state, rng);
    trace.free(node.node, rng);
}
