// SPDX-License-Identifier: MIT OR Apache-2.0
//! Synthetic workloads: a steady-state live set churned by random operations, one profile
//! per corner of the allocator.
//!
//! - `small`: sizes 1–256 only — the bucket path alone.
//! - `large`: sizes 257 B–256 KiB, log-uniform — the tree path alone, with coalescing.
//! - `mixed`: nine small requests to one large, some reallocs and resizes — both paths.
//! - `aligned`: `alloc_aligned` at alignments from 16 to 65536 — the padding, `shift` and
//!   aligned-extraction paths.
//! - `realloc`: a live set mostly resized in place or moved by `realloc`/`realloc_aligned`.

use crate::builder::{TraceBuilder, log_uniform};
use rand::Rng;
use rand_chacha::ChaCha8Rng;

/// One synthetic profile.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Profile {
    Small,
    Large,
    Mixed,
    Aligned,
    Realloc,
}

const ALIGNMENTS: [u64; 9] = [16, 32, 64, 128, 256, 512, 4096, 16384, 65536];

/// Writes random operations into `trace` until it holds at least `ops` operations.
pub fn generate(trace: &mut TraceBuilder, rng: &mut ChaCha8Rng, ops: u64, profile: Profile) {
    let target_live: usize = match profile {
        Profile::Small => 2000,
        Profile::Large => 150,
        Profile::Mixed => 800,
        Profile::Aligned => 300,
        Profile::Realloc => 300,
    };
    // Of the steps that do not allocate: the percentage that reallocate, then resize.
    let (realloc_pct, resize_pct) = match profile {
        Profile::Realloc => (70, 10),
        Profile::Mixed => (10, 4),
        Profile::Small | Profile::Large | Profile::Aligned => (0, 0),
    };
    let mut live: Vec<u64> = Vec::new();
    while trace.ops() < ops {
        // Allocate with probability 1 - fill/2 (fill = live / target), so the live set
        // settles around its target. Integer arithmetic only (see `log_uniform`).
        let allocate = live.is_empty() || rng.gen_range(0..2 * target_live) >= live.len();
        let roll = rng.gen_range(0..100);
        if allocate {
            live.push(allocate_one(trace, rng, profile));
        } else if roll < realloc_pct {
            let h = live[rng.gen_range(0..live.len())];
            let size = size_for(rng, profile);
            if rng.gen_bool(0.2) {
                trace.realloc_aligned(h, size, ALIGNMENTS[rng.gen_range(0..7)]);
            } else {
                trace.realloc(h, size);
            }
        } else if roll < realloc_pct + resize_pct {
            let h = live[rng.gen_range(0..live.len())];
            trace.resize(h, size_for(rng, profile));
        } else if roll < realloc_pct + resize_pct + 2 {
            let h = live[rng.gen_range(0..live.len())];
            trace.size(h);
        } else {
            let h = live.swap_remove(rng.gen_range(0..live.len()));
            trace.free(h, rng);
        }
        if rng.gen_range(0..2000) == 0 {
            trace.purge();
        }
    }
}

fn size_for(rng: &mut ChaCha8Rng, profile: Profile) -> u64 {
    match profile {
        Profile::Small => rng.gen_range(1..=256),
        Profile::Large => log_uniform(rng, 257, 256 * 1024),
        Profile::Mixed if rng.gen_bool(0.9) => rng.gen_range(1..=256),
        Profile::Mixed => log_uniform(rng, 257, 1024 * 1024),
        Profile::Aligned => log_uniform(rng, 1, 8 * 1024),
        Profile::Realloc => log_uniform(rng, 1, 32 * 1024),
    }
}

fn allocate_one(trace: &mut TraceBuilder, rng: &mut ChaCha8Rng, profile: Profile) -> u64 {
    let size = size_for(rng, profile);
    match profile {
        Profile::Aligned => {
            trace.alloc_aligned(size, ALIGNMENTS[rng.gen_range(0..ALIGNMENTS.len())])
        }
        Profile::Small | Profile::Mixed if rng.gen_bool(0.05) => {
            let count = rng.gen_range(1..=16);
            trace.calloc(count, size.div_ceil(count).max(1))
        }
        Profile::Small | Profile::Large | Profile::Mixed | Profile::Realloc => trace.alloc(size),
    }
}
