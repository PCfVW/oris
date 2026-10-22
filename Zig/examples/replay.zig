// SPDX-License-Identifier: MIT OR Apache-2.0
//! Replays a trace file on a fresh `Orisnitsa(.{ .trace = true })` and prints its
//! transition record on stdout.
//!
//! ```text
//! zig build replay -- ../examples/traces/handwritten/realloc.trace
//! ```
//!
//! The Zig leg of the cross-port trace gate: `orisnik`'s `cargo run --example replay
//! --features trace -- <file>` and the HPHA oracle's `trace_replay.exe <file>` print the
//! same record for the same trace, byte for byte, and CI diffs all three against the
//! committed `.record` file. See `docs/traces.md` and `examples/traces/GRAMMAR.md` in the
//! repository.

const std = @import("std");
const orisnitsa = @import("orisnitsa");

pub fn main(init: std.process.Init) !u8 {
    const args = try init.minimal.args.toSlice(init.arena.allocator());
    if (args.len != 2) {
        std.debug.print("usage: replay <trace-file>\n", .{});
        return 2;
    }
    const path = args[1];
    const trace = std.Io.Dir.cwd().readFileAlloc(init.io, path, init.gpa, .unlimited) catch |err| {
        std.debug.print("replay: failed to read {s}: {s}\n", .{ path, @errorName(err) });
        return 2;
    };
    defer init.gpa.free(trace);

    // The record goes to memory first, so a trace rejected halfway prints nothing.
    var record: std.Io.Writer.Allocating = .init(init.gpa);
    defer record.deinit();
    var diagnostic: orisnitsa.letopis.Diagnostic = .{};
    orisnitsa.letopis.replay(init.gpa, trace, &record.writer, &diagnostic) catch |err| {
        switch (err) {
            error.Syntax => std.debug.print("replay: {s}: syntax error (line {d}): {s}\n", .{ path, diagnostic.line, diagnostic.message() }),
            error.Semantic => std.debug.print("replay: {s}: trace rejected (line {d}): {s}\n", .{ path, diagnostic.line, diagnostic.message() }),
            else => std.debug.print("replay: {s}: {s}\n", .{ path, @errorName(err) }),
        }
        return 1;
    };

    // Raw bytes, LF line endings on every OS: the record is compared byte for byte.
    // Streaming, not the default positional writer: stdout is usually a pipe, which has no
    // position (on Windows a positional write to one is an unrecoverable error).
    var buffer: [4096]u8 = undefined;
    var stdout = std.Io.File.stdout().writerStreaming(init.io, &buffer);
    try stdout.interface.writeAll(record.written());
    try stdout.interface.flush();
    return 0;
}
