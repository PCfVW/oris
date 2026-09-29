// SPDX-License-Identifier: MIT OR Apache-2.0
//! The Microsoft C runtime's `rand()`, reproduced exactly.
//!
//! `holdrand = holdrand * 214013 + 2531011; return (holdrand >> 16) & 0x7fff`. Taken
//! from Eric Jacopin's "Vintage RNGs" chapter (*Game AI Pro 3*), and verified against
//! the real CRT before being relied on: 200 000 draws after each of `srand(0)`,
//! `srand(1)`, `srand(42)`, `srand(1234)` and `srand(0xFFFF_FFFF)` are bit-identical
//! to `rand()` as linked on Windows (golden vectors pinned in this module's own
//! tests, where this generator first shipped as a test-only stress-workload helper
//! inside `orisnitsa.zig`).
//!
//! Promoted to production for `spomen`'s guard-byte ramp: HPHA seeds each
//! allocation's guard byte from `rand()` (`hpha.cpp:745-751`, `write_guard`), and
//! this port wants that content cross-port-identical rather than merely
//! per-port-plausible — `orisnik` carries the identical generator
//! (`Rust/src/rand.rs`), so both ports see one stream for the same seed. Why this
//! generator and not an arbitrary one: it is also what Dimitar Lazarov's own
//! `main.cpp` benchmark drives HPHA with (`srand(1234)`), so the stress workload in
//! this module's own tests and `spomen`'s guard bytes both trace back to the same,
//! real, historically-grounded source.

const std = @import("std");
const bucket = @import("bucket.zig");
const spomen = @import("spomen.zig");

const Config = spomen.Config;

/// One instance of the CRT's `rand()` state (`holdrand`). `pub` so both
/// `orisnitsa.zig`'s guard-byte seed stream (production) and its pre-existing
/// randomized stress-workload tests (test-only) can reach it via
/// `@import("rand.zig")`.
pub const VintageRand = struct {
    /// The CRT's `holdrand` LCG state — any `u32` is valid; `Orisnitsa`'s
    /// guard-byte stream starts it at `0` (see that field's doc).
    state: u32,

    /// A generator in the state the CRT's `srand(seed)` would leave it in
    /// (`holdrand = seed`).
    pub fn init(seed: u32) VintageRand {
        return .{ .state = seed };
    }

    /// One `rand()` draw: `0..=0x7fff`.
    pub fn next(self: *VintageRand) u32 {
        self.state = self.state *% 214_013 +% 2_531_011;
        return (self.state >> 16) & 0x7fff;
    }

    /// `main.cpp`'s `rand_size()`: 2..=4096, heavily skewed toward the floor.
    ///
    /// Test-only — specific to `orisnitsa.zig`'s stress workload, not used by the
    /// production guard-byte seeding (which only ever calls `init`/`next`). A
    /// `pub` method on the same type is this port's stand-in for `orisnik`'s
    /// second, test-only inherent `impl VintageRand` block in `orisnik.rs`; Zig
    /// has no module-scoped inherent-impl split, so it lives here instead,
    /// reachable from `orisnitsa.zig`'s tests as any other `pub` method would be.
    ///
    /// The C++ computes `MIN + (MAX - MIN) * powf(r, 8.0f)` with `r` a float in
    /// `[0,1]`. This uses an integer analogue — three squarings in 15-bit fixed
    /// point — deliberately: `powf` is not bit-reproducible across language
    /// runtimes, and a stress workload whose *shape* both ports agree on exactly
    /// is worth more here than one that matches C++'s last mantissa bit. The
    /// distribution is the same: overwhelmingly bucket-path, with a long tail
    /// crossing into the tree (measured: ~71% / ~29%).
    pub fn size(self: *VintageRand) usize {
        const MIN_SIZE: u64 = 2;
        const MAX_SIZE: u64 = 4096;
        const r: u64 = self.next();
        const r2 = (r * r) >> 15;
        const r4 = (r2 * r2) >> 15;
        const r8 = (r4 * r4) >> 15;
        // CAST: u64 -> usize, the result is at most MAX_SIZE (4096).
        return @intCast(MIN_SIZE + ((r8 * (MAX_SIZE - MIN_SIZE)) >> 15));
    }

    /// `main.cpp`'s `rand_alignment()`: one of 1, 2, 4, ..., 128. Test-only — see
    /// `size`'s doc.
    pub fn alignment(self: *VintageRand) usize {
        const MAX_ALIGNMENT_LOG2: u64 = 7;
        const r: u64 = self.next();
        // CAST: u64 -> u6, the shift is at most MAX_ALIGNMENT_LOG2 (7).
        const shift: u6 = @intCast((MAX_ALIGNMENT_LOG2 * r) >> 15);
        return @as(usize, 1) << shift;
    }

    /// `main.cpp`'s `i + rand() % (N - i)` — picks a survivor to swap with.
    /// Test-only — see `size`'s doc.
    pub fn indexIn(self: *VintageRand, remaining: usize) usize {
        return @as(usize, self.next()) % remaining;
    }
};

const testing = std.testing;

test "VintageRand matches the Microsoft CRT" {
    // Golden vector: the first draws of `random values from rand.txt` in the
    // Vintage RNGs corpus, produced by the real CRT after `srand(0)`.
    var r: VintageRand = .init(0);
    for ([_]u32{ 38, 7719, 21238, 2437, 8855, 11797, 8365, 32285, 10450 }) |expected| {
        try testing.expectEqual(expected, r.next());
    }
    // And the seed Lazarov's own `main.cpp` uses.
    var r2: VintageRand = .init(1234);
    for ([_]u32{ 4068, 213, 12761, 8758, 23056, 7717, 15274, 24508 }) |expected| {
        try testing.expectEqual(expected, r2.next());
    }
}

test "VintageRand derived stream is pinned across ports" {
    // Pins the *exact* derived stream both ports must see, with no allocator
    // involved — the cross-port invariant's requirement applied to the test
    // workload itself.
    //
    // The golden vectors above pin `next()`; this pins everything derived from
    // it, so a drift in `size`'s fixed-point arithmetic or `alignment`'s shift
    // cannot slip through in one port while the other stays put. `orisnik`
    // asserts the identical constants. Computed independently from the
    // reference LCG, not captured from this implementation's own output.
    //
    // `bucket.isSmallAllocation`'s threshold itself shifts down by
    // `guard.memoryGuardSize(config)` under `config.debug` (0 otherwise,
    // restoring the exact non-debug golden pairs) — see that function's own
    // doc — so a handful of sizes right at the boundary move from bucket to
    // tree path under that config; both sets of golden numbers were computed
    // from this same generator, not guessed.
    const Case = struct { n: usize, bucket: usize, tree: usize };
    inline for ([_]Config{ .{}, .{ .debug = true } }) |config| {
        const cases: [2]Case = if (config.debug)
            .{
                .{ .n = 150, .bucket = 107, .tree = 43 },
                .{ .n = 20_000, .bucket = 14_006, .tree = 5_994 },
            }
        else
            .{
                .{ .n = 150, .bucket = 108, .tree = 42 },
                .{ .n = 20_000, .bucket = 14_123, .tree = 5_877 },
            };
        for (cases) |c| {
            var rng: VintageRand = .init(1234);
            var bucket_path: usize = 0;
            var tree_path: usize = 0;
            for (0..c.n) |_| {
                if (bucket.isSmallAllocation(config, rng.size())) bucket_path += 1 else tree_path += 1;
            }
            try testing.expectEqual(c.bucket, bucket_path);
            try testing.expectEqual(c.tree, tree_path);
        }
    }

    // The aligned pass draws a size and an alignment per iteration; the sum of
    // the alignments pins that interleaving too. Config-independent — `size`'s
    // draw is never checked against `isSmallAllocation` in this pass.
    var rng: VintageRand = .init(1234);
    var alignment_sum: usize = 0;
    for (0..20_000) |_| {
        _ = rng.size();
        alignment_sum += rng.alignment();
    }
    try testing.expectEqual(@as(usize, 363_773), alignment_sum);
}
