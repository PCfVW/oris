// SPDX-License-Identifier: MIT OR Apache-2.0
//! A parser's allocation pattern: small-allocation churn around one large buffer per file
//! (`BRIEF.md`, "Target workloads": parsers and interpreters).
//!
//! Each file is read into one large source buffer. The lexer appends tokens to a buffer
//! that grows by doubling (realloc) and allocates a small string for every identifier
//! and literal — most of which, whitespace and punctuation, it drops at once. The parser
//! builds the tree bottom-up: every node is a small block, and every node's child list a
//! small array grown by realloc as children arrive. Identifiers go into a symbol table.
//! When the file is done the tree is torn down in reverse, then the side tables, then the
//! buffers; every other file the parser purges.

use crate::builder::{TraceBuilder, log_uniform};
use rand::Rng;
use rand_chacha::ChaCha8Rng;

/// Writes parsed files into `trace` until it holds at least `ops` operations.
pub fn generate(trace: &mut TraceBuilder, rng: &mut ChaCha8Rng, ops: u64) {
    let mut files = 0u64;
    while trace.ops() < ops {
        parse_file(trace, rng, ops);
        files += 1;
        if files % 2 == 0 {
            trace.purge();
        }
    }
}

/// A tree node and its growable child list.
struct Node {
    node: u64,
    children: Option<(u64, u64)>, // (handle, capacity in pointers)
}

fn parse_file(trace: &mut TraceBuilder, rng: &mut ChaCha8Rng, ops: u64) {
    let source = trace.alloc(log_uniform(rng, 8 * 1024, 256 * 1024));
    let mut token_capacity: u64 = 32; // tokens of 16 bytes
    let tokens = trace.alloc(token_capacity * 16);
    let mut token_count: u64 = 0;
    let mut strings: Vec<u64> = Vec::new();
    let mut symbols: Vec<u64> = Vec::new();
    let mut nodes: Vec<Node> = Vec::new();
    let length = rng.gen_range(300..3000);
    for _ in 0..length {
        if trace.ops() >= ops {
            break;
        }
        // Lex one token.
        token_count += 1;
        if token_count > token_capacity {
            token_capacity *= 2;
            trace.realloc(tokens, token_capacity * 16);
        }
        let text = trace.alloc(rng.gen_range(2..48));
        if rng.gen_bool(0.6) {
            trace.free(text, rng); // whitespace, punctuation: dropped at once
        } else {
            strings.push(text);
            if rng.gen_bool(0.3) {
                symbols.push(trace.alloc(32 + 8 * rng.gen_range(0..9)));
            }
        }
        // Reduce: a node, attached as a child of a recent node.
        if rng.gen_bool(0.7) {
            let node = trace.alloc(24 + 8 * rng.gen_range(0..13));
            if let Some(parent) = nodes.len().checked_sub(1 + rng.gen_range(0..4)) {
                let parent = &mut nodes[parent];
                match parent.children {
                    None => {
                        let list = trace.alloc(2 * 8);
                        parent.children = Some((list, 2));
                    }
                    Some((list, capacity)) if rng.gen_bool(0.5) => {
                        trace.realloc(list, capacity * 2 * 8);
                        parent.children = Some((list, capacity * 2));
                    }
                    Some(_) => {}
                }
            }
            nodes.push(Node {
                node,
                children: None,
            });
        }
        if rng.gen_bool(0.01) {
            trace.size(source);
        }
    }
    // Tear down: the tree in reverse, then the side tables, then the buffers.
    while let Some(node) = nodes.pop() {
        if let Some((list, _)) = node.children {
            trace.free(list, rng);
        }
        trace.free(node.node, rng);
    }
    for s in symbols.into_iter().rev() {
        trace.free(s, rng);
    }
    for s in strings {
        trace.free(s, rng);
    }
    trace.free(tokens, rng);
    trace.free(source, rng);
}
