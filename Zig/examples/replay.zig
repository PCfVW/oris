// SPDX-License-Identifier: MIT OR Apache-2.0
//! Replays a trace file on a fresh `Orisnitsa(.{ .trace = true })` and prints its
//! transition record on stdout.
//!
//! ```text
//! zig build replay -- ../examples/traces/handwritten/realloc-branches.trace
//! ```
//!
//! The Zig leg of the cross-port trace gate: `orisnik`'s `cargo run --example replay
//! --features trace -- <file>` and the HPHA oracle's `trace_replay.exe <file>` print the
//! same record for the same trace, byte for byte, and CI diffs all three against the
//! committed `.record` file. See `docs/traces.md` and `examples/traces/GRAMMAR.md` in the
//! repository.

const std = @import("std");
const builtin = @import("builtin");
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
            error.Unmapped => std.debug.print("replay: {s}: line {d}: {s}\n", .{ path, diagnostic.line, diagnostic.message() }),
            else => std.debug.print("replay: {s}: {s}\n", .{ path, @errorName(err) }),
        }
        return 1;
    };

    // Raw bytes, LF line endings on every OS: the record is compared byte for byte.
    try writeStdout(init.io, record.written());
    return 0;
}

extern "kernel32" fn GetStdHandle(which: u32) callconv(.winapi) ?*anyopaque;
extern "kernel32" fn WriteFile(file: ?*anyopaque, buffer: [*]const u8, len: u32, written: *u32, overlapped: ?*anyopaque) callconv(.winapi) c_int;

/// Writes `bytes` to stdout. On Windows through `WriteFile` directly: Zig 0.16's `std.Io` file
/// writer can reach `unreachable` (an unexpected `NtWriteFile` status) when stdout is a pipe and
/// the reader is slower than the writer — observed with records of a few hundred KiB piped into
/// another program — and stdout is a pipe whenever the record is compared on the fly. Elsewhere,
/// a streaming writer (a pipe has no position, so not the default positional one).
fn writeStdout(io: std.Io, bytes: []const u8) !void {
    if (builtin.os.tag == .windows) {
        // CAST: STD_OUTPUT_HANDLE is (DWORD)-11; the bit pattern is what kernel32 expects.
        const STD_OUTPUT_HANDLE: u32 = @bitCast(@as(i32, -11));
        const handle = GetStdHandle(STD_OUTPUT_HANDLE);
        var rest = bytes;
        while (rest.len > 0) {
            var written: u32 = 0;
            // CAST: at most 1 MiB, which fits a u32.
            const chunk: u32 = @intCast(@min(rest.len, 1 << 20));
            if (WriteFile(handle, rest.ptr, chunk, &written, null) == 0 or written == 0) return error.WriteFailed;
            // INDEX: `written <= chunk <= rest.len`.
            rest = rest[written..];
        }
        return;
    }
    var buffer: [4096]u8 = undefined;
    var stdout = std.Io.File.stdout().writerStreaming(io, &buffer);
    try stdout.interface.writeAll(bytes);
    try stdout.interface.flush();
}
