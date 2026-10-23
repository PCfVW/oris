// SPDX-License-Identifier: MIT OR Apache-2.0
//! Replay and recorder tests. Each embedded trace and expected value also exists in
//! `orisnitsa`'s `letopis_tests.zig`, with the same expectation: a difference between the
//! two files is a cross-port divergence, caught here before CI's corpus gate.

use super::{Recorder, ReplayError, replay};
use crate::Orisnik;
#[cfg(not(feature = "debug-allocator"))]
use core::fmt::Write;

fn record_of(trace: &str) -> String {
    let mut out = String::new();
    if let Err(error) = replay(trace, &mut out) {
        panic!("replay failed: {error}");
    }
    out
}

#[test]
// The record pins exact sizes and offsets; the debug allocator's guard reservation shifts
// every one of them (the record is defined against the non-debug build, `GRAMMAR.md`).
#[cfg(not(feature = "debug-allocator"))]
fn the_grammar_example_trace() {
    let trace = "oris-trace 1\nalloc h0 24\nalloc h1 1000\nrealloc h1 2000\nfree_sized h0 24\n\
                 free h1\npurge\n";
    let expected = "oris-record 1
#0 alloc h0 24 -> m0+0x0 a=65536
  map b m0 65536
  page+ b2 m0
#1 alloc h1 1000 -> m1+0x20 a=131072
  map t m1 65536
  split m1+0x10 1008
  mr m1+0x410
#2 realloc h1 2000 -> m1+0x20 a=131072
  mr -
  merge m1+0x410
  split m1+0x10 2000
  mr m1+0x7f0
#3 free_sized h0 24 -> - a=131072
#4 free h1 -> - a=131072
  mr -
  merge m1+0x7f0
  mr m1+0x10
#5 purge -> - a=0
  tree+ m1+0x10 65488 node rot=0
  mr -
  tree- m1+0x10 65488 node rot=0
  unmap m1 65536
  mr -
  page- b2 m0
  unmap m0 65536
end ops=6 maps=2 unmaps=2 rotations=0 allocated=0
";
    assert_eq!(record_of(trace), expected);
}

/// The xorshift32 every port's tests share.
#[cfg(not(feature = "debug-allocator"))]
struct Xorshift(u32);

#[cfg(not(feature = "debug-allocator"))]
impl Xorshift {
    fn next(&mut self) -> u32 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 17;
        self.0 ^= self.0 << 5;
        self.0
    }

    /// A value in `[0, bound)`.
    fn below(&mut self, bound: u32) -> u32 {
        self.next() % bound
    }
}

/// A live handle of the generated trace: its number, and the size/alignment of the
/// allocation that bound it while a sized free is still allowed (`GRAMMAR.md` C6/C7).
#[cfg(not(feature = "debug-allocator"))]
struct Live {
    h: u32,
    fresh: Option<(u32, u32)>,
}

/// A deterministic mixed workload, generated identically by `orisnitsa`'s
/// `generatedTrace`: a burst that fills a bucket page, then 4000 random operations over
/// every kind the grammar has, satisfying every semantic constraint.
// INDEX: every index below is reduced modulo its array's length, or drawn by
// `Xorshift::below(live.len())` with `live` non-empty.
#[allow(clippy::indexing_slicing)]
#[cfg(not(feature = "debug-allocator"))]
fn generated_trace() -> String {
    let mut rng = Xorshift(0x5eed_1e70);
    let mut trace = String::from("oris-trace 1\n");
    let mut live: Vec<Live> = Vec::new();
    let mut next_h = 0;
    // 300 256-byte slots: more than one page of bucket 31 holds (255), so a page fills.
    for _ in 0..300 {
        let _ = writeln!(trace, "alloc h{next_h} 256");
        live.push(Live {
            h: next_h,
            fresh: Some((256, 0)),
        });
        next_h += 1;
    }
    for _ in 0..4000 {
        let r = rng.below(100);
        if live.is_empty() || r < 40 {
            let h = next_h;
            next_h += 1;
            let fresh = match rng.below(4) {
                0 => {
                    let size = 1 + rng.below(256);
                    let _ = writeln!(trace, "alloc h{h} {size}");
                    (size, 0)
                }
                1 => {
                    let size = 257 + rng.below(8000);
                    let _ = writeln!(trace, "alloc h{h} {size}");
                    (size, 0)
                }
                2 => {
                    let alignment = [16, 64, 256, 4096][usize::try_from(rng.below(4)).unwrap_or(0)];
                    let size = 1 + rng.below(3000);
                    let _ = writeln!(trace, "alloc_aligned h{h} {size} {alignment}");
                    (size, alignment)
                }
                _ => {
                    let count = 1 + rng.below(16);
                    let size = 1 + rng.below(64);
                    let _ = writeln!(trace, "calloc h{h} {count} {size}");
                    (count * size, 0)
                }
            };
            live.push(Live {
                h,
                fresh: Some(fresh),
            });
            continue;
        }
        let index = usize::try_from(rng.below(u32::try_from(live.len()).unwrap_or(1))).unwrap_or(0);
        if r < 60 {
            let size = 1 + rng.below(20_000);
            let entry = &mut live[index];
            let _ = writeln!(trace, "realloc h{} {size}", entry.h);
            entry.fresh = None;
        } else if r < 65 {
            let alignment = [16, 64, 512][usize::try_from(rng.below(3)).unwrap_or(0)];
            let size = if alignment > 256 {
                257 + rng.below(5000)
            } else {
                1 + rng.below(5000)
            };
            let entry = &mut live[index];
            let _ = writeln!(trace, "realloc_aligned h{} {size} {alignment}", entry.h);
            entry.fresh = None;
        } else if r < 70 {
            let size = 1 + rng.below(10_000);
            let entry = &mut live[index];
            let _ = writeln!(trace, "resize h{} {size}", entry.h);
            entry.fresh = None;
        } else if r < 72 {
            let _ = writeln!(trace, "size h{}", live[index].h);
        } else if r < 99 {
            let entry = live.swap_remove(index);
            let sized = rng.below(2) == 0;
            match entry.fresh {
                Some((size, alignment)) if sized && size >= 1 && alignment <= 8 => {
                    let _ = writeln!(trace, "free_sized h{} {size}", entry.h);
                }
                Some((size, alignment)) if sized && size >= 1 => {
                    let _ = writeln!(trace, "free_sized_aligned h{} {size} {alignment}", entry.h);
                }
                _ => {
                    let _ = writeln!(trace, "free h{}", entry.h);
                }
            }
        } else {
            trace.push_str("purge\n");
        }
    }
    trace
}

/// FNV-1a, 64-bit: a fingerprint of a whole record that both ports' tests can pin.
#[cfg(not(feature = "debug-allocator"))]
fn fnv1a(bytes: &[u8]) -> u64 {
    bytes.iter().fold(0xcbf2_9ce4_8422_2325, |hash, &b| {
        (hash ^ u64::from(b)).wrapping_mul(0x0000_0100_0000_01b3)
    })
}

#[test]
// The record pins exact sizes and offsets; the debug allocator's guard reservation shifts
// every one of them (the record is defined against the non-debug build, `GRAMMAR.md`).
#[cfg(not(feature = "debug-allocator"))]
// 4300 operations is minutes of interpretation under Miri; the unsafe code this exercises
// (the event tap) is covered there by every other replay test.
#[cfg_attr(
    miri,
    ignore = "slow under Miri; the tap is covered by the other replay tests"
)]
fn a_generated_workload_emits_every_event_kind_and_the_shared_fingerprint() {
    let trace = generated_trace();
    let record = record_of(&trace);
    for needle in [
        "\n  map b ",
        "\n  map t ",
        "\n  unmap ",
        "\n  page+ ",
        "\n  page- ",
        "\n  page-full ",
        "\n  page-refill ",
        "\n  split ",
        "\n  shift ",
        "\n  merge ",
        " chain rot=",
        " node rot=",
        " link rot=",
        " promote rot=",
        "\n  list+ ",
        "\n  list- ",
        "\n  mr m",
        "\n  mr -",
        " rot=1\n",
        " rot=2\n",
    ] {
        assert!(
            record.contains(needle),
            "no `{}` in the record",
            needle.trim()
        );
    }
    // The same value is pinned in `orisnitsa`'s `letopis_tests.zig`: the two ports wrote the
    // same 4300-operation record byte for byte.
    assert_eq!(
        (fnv1a(trace.as_bytes()), fnv1a(record.as_bytes())),
        (TRACE_FINGERPRINT, RECORD_FINGERPRINT)
    );
}

#[cfg(not(feature = "debug-allocator"))]
const TRACE_FINGERPRINT: u64 = 18_252_001_378_337_324_280;
#[cfg(not(feature = "debug-allocator"))]
const RECORD_FINGERPRINT: u64 = 7_125_967_866_125_270_486;

#[test]
fn a_rejected_trace_executes_nothing() {
    let mut out = String::new();
    let error = replay("oris-trace 1\nalloc h0 8\nfree h1\n", &mut out).expect_err("C2");
    assert!(
        matches!(error, ReplayError::Semantic { line: 3, .. }),
        "{error}"
    );
    assert!(out.is_empty(), "nothing is written for a rejected trace");
    assert!(error.to_string().contains("C2: h1 is not bound"));
}

#[test]
fn the_recorder_writes_what_replays_to_the_same_record() {
    let allocator = Box::new(Orisnik::new());
    let mut recorder = Recorder::new(&allocator, String::new());
    let small = recorder.alloc(24);
    let big = recorder.alloc_aligned(3000, 64);
    // In every block below, each pointer came from this recorder's allocator, is live, and
    // is freed (or reallocated) exactly once.
    // SAFETY: as above.
    let big = unsafe { recorder.realloc(big, 9000) };
    let zeroed = recorder.calloc(4, 8);
    // SAFETY: as above.
    let _ = unsafe { recorder.resize(big, 100) };
    // SAFETY: as above.
    let _ = unsafe { recorder.size(zeroed) };
    // SAFETY: null is always accepted (and, doing nothing, is not recorded).
    unsafe { recorder.free(None) };
    // SAFETY: as above; 24 is the size `small` was allocated with.
    unsafe { recorder.free_with_size(small, 24) };
    // SAFETY: as above.
    unsafe { recorder.free(zeroed) };
    // SAFETY: null is always accepted.
    let grown = unsafe { recorder.realloc(None, 40) };
    // SAFETY: as above.
    let gone = unsafe { recorder.realloc(grown, 0) };
    assert!(gone.is_none());
    // SAFETY: as above.
    unsafe { recorder.free(big) };
    recorder.purge();
    let trace = recorder.finish().expect("a String never fails");
    assert_eq!(
        trace,
        "oris-trace 1\nalloc h0 24\nalloc_aligned h1 3000 64\nrealloc h1 9000\ncalloc h2 4 8\n\
         resize h1 100\nsize h2\nfree_sized h0 24\nfree h2\nrealloc h3 40\nrealloc h3 0\nfree h1\n\
         purge\n"
    );
    // What was recorded replays (it satisfies every constraint), and replays the same way
    // twice: the record depends only on the trace.
    assert_eq!(record_of(&trace), record_of(&trace));
}
