// SPDX-License-Identifier: MIT OR Apache-2.0
//! A build-step probe, not part of the library (`root.zig` does not import it).
//!
//! `Orisnitsa(.{ .debug = true }).deinit()` ends in a panic when an allocation is still
//! live, and no Zig test can catch a panic — the test runner would die with it. So the panic
//! itself is pinned from outside: `build.zig`'s `test` step runs this program and requires
//! that it **fails**, with the leak report and the panic message on stderr. If `deinit`
//! stopped failing on a leak, the program would reach the `exit(0)` below and the step would
//! fail instead.

const std = @import("std");
const orisnitsa = @import("orisnitsa.zig");

pub fn main() void {
    var backing: orisnitsa.Orisnitsa(.{ .debug = true }) = .init();
    // Deliberately never freed.
    _ = backing.alloc(24) orelse std.process.exit(2);
    backing.deinit();
    // Reached only if the leak went unnoticed.
    std.process.exit(0);
}
