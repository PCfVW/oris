// SPDX-License-Identifier: MIT OR Apache-2.0
//! Writing a trace that is valid by construction.
//!
//! Every workload drives a [`TraceBuilder`]: it hands out handle numbers, remembers which
//! handles are live and how each was bound, and writes only operations that satisfy the
//! semantic constraints of `examples/traces/GRAMMAR.md` §1.3 — a sized free only right
//! after the allocation it names (C6/C7), a large size whenever a realloc asks for an
//! alignment above 256 (C8), sizes and alignments within bounds (C3/C4). A workload
//! therefore never has to think about the rules; `tracegen` still replays every trace
//! through `orisnik` before writing it, as a second line of defence.

use rand::Rng;
use rand_chacha::ChaCha8Rng;
use std::collections::HashMap;
use std::fmt::Write;

/// The largest size a trace may request (GRAMMAR.md C4).
pub const MAX_SIZE: u64 = 1 << 30;

/// What the builder knows about a live handle.
#[derive(Clone, Copy)]
struct Live {
    /// The size and alignment it was allocated with, while a sized free is still allowed
    /// (no realloc or resize since), for C6/C7.
    fresh: Option<(u64, u64)>,
}

/// A trace under construction.
pub struct TraceBuilder {
    text: String,
    live: HashMap<u64, Live>,
    next_h: u64,
    ops: u64,
}

impl TraceBuilder {
    /// A trace with its header and one comment line describing where it came from.
    pub fn new(comment: &str) -> Self {
        let mut text = String::from("oris-trace 1\n");
        for line in comment.lines() {
            let _ = writeln!(text, "# {line}");
        }
        Self {
            text,
            live: HashMap::new(),
            next_h: 0,
            ops: 0,
        }
    }

    /// Operations written so far.
    pub fn ops(&self) -> u64 {
        self.ops
    }

    /// The finished trace.
    pub fn finish(self) -> String {
        self.text
    }

    fn op(&mut self, line: std::fmt::Arguments<'_>) {
        let _ = writeln!(self.text, "{line}");
        self.ops += 1;
    }

    fn fresh_handle(&mut self, fresh: Option<(u64, u64)>) -> u64 {
        let h = self.next_h;
        self.next_h += 1;
        self.live.insert(h, Live { fresh });
        h
    }

    /// `alloc h S`; returns the new handle.
    pub fn alloc(&mut self, size: u64) -> u64 {
        let size = size.min(MAX_SIZE);
        let h = self.fresh_handle(Some((size, 0)));
        self.op(format_args!("alloc h{h} {size}"));
        h
    }

    /// `alloc_aligned h S A`; `alignment` must be 0 or a power of two at most 65536.
    pub fn alloc_aligned(&mut self, size: u64, alignment: u64) -> u64 {
        debug_assert!(alignment == 0 || (alignment.is_power_of_two() && alignment <= 65536));
        let size = size.min(MAX_SIZE);
        let h = self.fresh_handle(Some((size, alignment)));
        self.op(format_args!("alloc_aligned h{h} {size} {alignment}"));
        h
    }

    /// `calloc h N S`, with `N × S` capped at the size limit.
    pub fn calloc(&mut self, count: u64, size: u64) -> u64 {
        let count = MAX_SIZE
            .checked_div(size)
            .map_or(count, |cap| count.min(cap));
        let h = self.fresh_handle(Some((count * size, 0)));
        self.op(format_args!("calloc h{h} {count} {size}"));
        h
    }

    /// `realloc h S` on a live handle.
    pub fn realloc(&mut self, h: u64, size: u64) {
        let size = size.min(MAX_SIZE);
        self.touch(h);
        self.op(format_args!("realloc h{h} {size}"));
    }

    /// `realloc_aligned h S A` on a live handle; a size of at most 256 with an alignment
    /// above 256 is raised to 257 (C8).
    pub fn realloc_aligned(&mut self, h: u64, size: u64, alignment: u64) {
        debug_assert!(alignment == 0 || (alignment.is_power_of_two() && alignment <= 65536));
        let size = if alignment > 256 { size.max(257) } else { size }.min(MAX_SIZE);
        self.touch(h);
        self.op(format_args!("realloc_aligned h{h} {size} {alignment}"));
    }

    /// `resize h S` on a live handle (`S` at least 1, C5).
    pub fn resize(&mut self, h: u64, size: u64) {
        let size = size.clamp(1, MAX_SIZE);
        self.touch(h);
        self.op(format_args!("resize h{h} {size}"));
    }

    /// `size h` on a live handle.
    pub fn size(&mut self, h: u64) {
        debug_assert!(self.live.contains_key(&h));
        self.op(format_args!("size h{h}"));
    }

    /// Frees a live handle: with a sized free when the rules allow one and `rng` picks it
    /// (half the time), with a plain `free` otherwise.
    pub fn free(&mut self, h: u64, rng: &mut ChaCha8Rng) {
        let live = self.live.remove(&h).expect("free of a live handle");
        let sized = rng.gen_bool(0.5);
        match live.fresh {
            Some((size, alignment)) if sized && size >= 1 && alignment <= 8 => {
                self.op(format_args!("free_sized h{h} {size}"));
            }
            Some((size, alignment)) if sized && size >= 1 => {
                self.op(format_args!("free_sized_aligned h{h} {size} {alignment}"));
            }
            _ => self.op(format_args!("free h{h}")),
        }
    }

    /// `purge`.
    pub fn purge(&mut self) {
        self.op(format_args!("purge"));
    }

    /// A realloc or resize ends a handle's eligibility for a sized free.
    fn touch(&mut self, h: u64) {
        self.live.get_mut(&h).expect("live handle").fresh = None;
    }
}

/// A size drawn log-uniformly from `[lo, hi]`, about as many requests between 16 and 32
/// bytes as between 16 and 32 KiB — the shape real allocation sizes have.
///
/// Integer arithmetic only: a power-of-two octave is chosen uniformly, then a size uniformly
/// within it. Floating-point `ln`/`exp` would call the platform's math library, whose last
/// bit differs between Windows, glibc and macOS — and a trace must come out byte-identical
/// on every machine that generates it.
pub fn log_uniform(rng: &mut ChaCha8Rng, lo: u64, hi: u64) -> u64 {
    let lo = lo.max(1);
    let hi = hi.max(lo);
    let (first, last) = (lo.ilog2(), hi.ilog2());
    let octave = rng.gen_range(first..=last);
    let start = (1u64 << octave).max(lo);
    let end = ((1u64 << octave) * 2 - 1).min(hi);
    rng.gen_range(start..=end)
}
