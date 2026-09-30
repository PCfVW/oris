// SPDX-License-Identifier: MIT OR Apache-2.0
//! The debug allocator catching, on purpose, a write past the end of a block, then showing
//! what it knows about the live allocations.
//!
//! ```text
//! zig build example
//! ```
//!
//! Walkthrough: `docs/debug-allocator.md` (repository root). This program stops short of
//! leaking a block on purpose: a leak makes `deinit()` panic, and a Zig panic ends the
//! process — the guide shows what that looks like.

const std = @import("std");
const orisnitsa = @import("orisnitsa");

/// The debug instantiation: `.{}` would be the plain, zero-cost `Orisnitsa`.
const Debug = orisnitsa.OrisnitsaWith(.{ .debug = true });

pub fn main() !void {
    var allocator: Debug = .init();
    // Must be called: returns the memory, and — because this is a debug instance — panics
    // if any block is still live.
    defer allocator.deinit();

    // 1. A one-byte overrun. The allocator reserves a guard ramp just past every block.
    const block = allocator.alloc(24) orelse return error.OutOfMemory;
    const guard_byte = block[24];
    block[24] = guard_byte ^ 0xFF; // the bug: one byte past the 24 that were asked for

    // `check()` asks: is every live block intact? It reports instead of panicking; the
    // optional `Diagnostic` receives the description.
    var diagnostic: orisnitsa.Diagnostic = .{};
    if (allocator.check(&diagnostic)) |_| {
        std.debug.print("check(): all blocks intact\n", .{});
    } else |err| {
        var lines = std.mem.splitScalar(u8, diagnostic.message(), '\n');
        std.debug.print("check() found {s}: {s}\n", .{ @errorName(err), lines.first() });
    }

    // Undo the damage so the block can be freed. (Freeing it as it is would panic: every
    // `free` verifies the guard first.)
    block[24] = guard_byte;
    std.debug.print("check() after repair: {}\n", .{if (allocator.check(null)) |_| true else |_| false});

    // 2. A report of what is live right now: totals and one line per block. The raw return
    // addresses that follow each block (indented) are left out here.
    var buffer: [4096]u8 = undefined;
    var writer: std.Io.Writer = .fixed(&buffer);
    try allocator.report(&writer);
    var lines = std.mem.splitScalar(u8, writer.buffered(), '\n');
    while (lines.next()) |line| {
        if (line.len > 0 and line[0] != ' ') std.debug.print("{s}\n", .{line});
    }

    // 3. Free it, and `deinit()` (deferred above) finds nothing to complain about.
    allocator.free(block);
}
