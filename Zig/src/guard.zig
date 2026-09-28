// SPDX-License-Identifier: MIT OR Apache-2.0
//! Extra bytes reserved after every allocation's payload once the `spomen` debug
//! subsystem is enabled, to detect a write past the end of the block.
//! Deliberately always compiled (unlike the rest of `spomen`, which stays gated
//! behind `config.debug` entirely) — `bucket.zig`/`tree.zig`/`orisnitsa.zig` must
//! reference `memoryGuardSize(config)` unconditionally for their size arithmetic
//! to type-check in every configuration. Ports `Cpp/hpha.h:936-942`'s
//! `MEMORY_GUARD_SIZE` constant exactly, including its value (16) and its being 0
//! outside a debug build.

const Config = @import("spomen.zig").Config;

/// Extra bytes reserved after every allocation's payload once the debug subsystem
/// is enabled, to detect a write past the end of the block. 16 when
/// `config.debug` is true, 0 otherwise — every `+`/`- memoryGuardSize(config)`
/// site (added in a later phase) and any loop bounded by it becomes dead code the
/// compiler removes when it's 0, restoring v0.1.x's exact guard-free behaviour.
/// Mirrors HPHA's own `MEMORY_GUARD_SIZE` (`Cpp/hpha.h:936-942`).
pub fn memoryGuardSize(comptime config: Config) usize {
    return if (config.debug) 16 else 0;
}

const testing = @import("std").testing;

test "memoryGuardSize folds to 0 by default and to 16 under debug" {
    try testing.expectEqual(@as(usize, 0), memoryGuardSize(.{}));
    try testing.expectEqual(@as(usize, 16), memoryGuardSize(.{ .debug = true }));
}
