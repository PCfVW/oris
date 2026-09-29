// SPDX-License-Identifier: MIT OR Apache-2.0
//! Extra bytes reserved after every allocation's payload once the `spomen` debug
//! subsystem is enabled, to detect a write past the end of the block.
//! Deliberately always compiled (unlike the rest of `spomen`, which stays gated
//! behind `config.debug` entirely) — `bucket.zig` (`isSmallAllocation`) and
//! `orisnitsa.zig` (through `inflate`/`deflate`) must reference
//! `memoryGuardSize(config)` unconditionally for their size arithmetic to
//! type-check in every configuration. (`tree.zig` never mentions it: like HPHA's
//! own `tree_alloc`, it just serves whatever already-inflated size it is handed.)
//! Ports `Cpp/hpha.h:936-942`'s `MEMORY_GUARD_SIZE` constant exactly, including
//! its value (16) and its being 0 outside a debug build.
//!
//! The guard *bytes themselves* — writing and checking the ramp — are `spomen`'s
//! job (`spomen_guard.zig`), not this module's: this module only holds the size
//! arithmetic every allocation path needs regardless of whether guard bytes are
//! ever actually written. Mirrors `orisnik`'s `Rust/src/guard.rs`.

const std = @import("std");

const Config = @import("spomen.zig").Config;

/// Extra bytes reserved after every allocation's payload once the debug subsystem
/// is enabled, to detect a write past the end of the block. 16 when
/// `config.debug` is true, 0 otherwise — every `inflate`/`deflate` call site in
/// `orisnitsa.zig` and the threshold in `bucket.isSmallAllocation`, and any loop
/// bounded by this value, becomes dead code the compiler removes when it's 0,
/// restoring v0.1.x's exact guard-free behaviour. Mirrors HPHA's own
/// `MEMORY_GUARD_SIZE` (`Cpp/hpha.h:936-942`).
pub fn memoryGuardSize(comptime config: Config) usize {
    return if (config.debug) 16 else 0;
}

/// The size to actually request from the bucket/tree allocator for a caller's
/// `requested` bytes, once guard-byte reservation is folded in — ports the
/// `size + MEMORY_GUARD_SIZE` HPHA computes inline at every `alloc`/`realloc`/
/// `resize` call site (`Cpp/hpha.h:1266-1440`), mirroring `orisnik`'s
/// `guard::inflate`. Identity when `config.debug` is false: the
/// `memoryGuardSize(config) == 0` branch below is `comptime`-resolved (`config`
/// is itself `comptime`), so the checked addition is never even emitted, not
/// merely folded away — matching this port's zero-cost-when-disabled requirement
/// more strongly than relying on the optimizer to prove `x + 0` never overflows.
///
/// `null` on overflow — an already-unserviceable request (within
/// `memoryGuardSize(config)` of `maxInt(usize)`) declined a few bytes earlier
/// than `tree.MAX_ALLOCATION` alone would, the same "no real input changes"
/// reasoning that bound's own doc gives.
pub fn inflate(comptime config: Config, requested: usize) ?usize {
    const memory_guard_size = comptime memoryGuardSize(config);
    if (memory_guard_size == 0) return requested;
    const sum = @addWithOverflow(requested, memory_guard_size);
    if (sum[1] != 0) return null;
    return sum[0];
}

/// The reverse of `inflate`: recovers the caller-visible size from a real,
/// guard-inflated block/slot size. Identity when `config.debug` is false.
///
/// `real` must be at least `memoryGuardSize(config)` — true of every block/slot
/// size this port ever reports, since every one of them passed through
/// `inflate` on the way in (`std.debug.assert`, not a public contract: this is
/// an internal arithmetic inverse, not a caller-facing precondition).
pub fn deflate(comptime config: Config, real: usize) usize {
    const memory_guard_size = comptime memoryGuardSize(config);
    // Vacuously true (`memory_guard_size == 0`, `usize`'s own minimum) when
    // `config.debug` is false — `comptime`-eliminated there, so the assert only
    // exists where it can actually catch something.
    if (memory_guard_size > 0) {
        std.debug.assert(real >= memory_guard_size);
    }
    return real - memory_guard_size;
}

const testing = std.testing;

test "memoryGuardSize folds to 0 by default and to 16 under debug" {
    try testing.expectEqual(@as(usize, 0), memoryGuardSize(.{}));
    try testing.expectEqual(@as(usize, 16), memoryGuardSize(.{ .debug = true }));
}

test "inflate and deflate round-trip" {
    inline for ([_]Config{ .{}, .{ .debug = true } }) |config| {
        for ([_]usize{ 0, 1, 64, 4096, std.math.maxInt(usize) / 2 }) |size| {
            const inflated = inflate(config, size) orelse return error.TestUnexpectedResult; // "not near maxInt(usize)"
            try testing.expectEqual(size, deflate(config, inflated));
        }
    }
}

test "inflate declines only within guard size of the maximum" {
    inline for ([_]Config{ .{}, .{ .debug = true } }) |config| {
        const guard_size = memoryGuardSize(config);
        const max = std.math.maxInt(usize);
        // Exactly at the maximum: overflows unless there is nothing to add.
        try testing.expectEqual(guard_size == 0, inflate(config, max) != null);
        // One `memoryGuardSize(config)` below it: always fits, by construction.
        try testing.expectEqual(@as(?usize, max), inflate(config, max - guard_size));
    }
}
