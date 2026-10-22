// SPDX-License-Identifier: MIT OR Apache-2.0
//! Reading a trace: the contract grammar of `examples/traces/GRAMMAR.md` §1.1, then the
//! semantic constraints of §1.3, so that nothing undefined is ever replayed. Ports
//! `orisnik`'s `letopis/trace.rs`; the error messages are the same, word for word.

const std = @import("std");

/// The largest size (and `calloc` product) a trace may request: 2³⁰ (constraint C4).
pub const MAX_TRACE_SIZE: u64 = 1 << 30;

/// The largest alignment a trace may request: `PAGE_SIZE` (constraint C3).
pub const MAX_TRACE_ALIGNMENT: u64 = 1 << 16;

/// Why reading or replaying a trace stopped. The human-readable description goes into a
/// `Diagnostic`, as with `Orisnitsa.check`. Parity: `orisnik`'s `ReplayError`.
pub const Error = error{
    /// The trace does not match the grammar (`GRAMMAR.md` §1.1). Nothing was executed.
    Syntax,
    /// The trace breaks a semantic constraint (`GRAMMAR.md` §1.3). Nothing was executed.
    Semantic,
    /// The allocator reported an address outside every mapping it made — a bug in this
    /// package's hooks, not in the trace.
    Unmapped,
    /// The parser, the event log or the record writer ran out of memory.
    OutOfMemory,
    /// Writing the record failed.
    WriteFailed,
};

/// The description of an `Error`, written into a fixed buffer (no allocation), and the
/// 1-based line it concerns (0 when it concerns no line).
pub const Diagnostic = struct {
    /// The offending line, or 0.
    line: usize = 0,
    /// Backing storage for the message.
    buf: [256]u8 = undefined,
    /// How many bytes of `buf` hold the message.
    len: usize = 0,

    /// The description, or an empty slice.
    pub fn message(self: *const Diagnostic) []const u8 {
        return self.buf[0..self.len];
    }

    /// Fills this diagnostic. Truncates a message longer than the buffer.
    pub fn set(self: *Diagnostic, line: usize, comptime fmt: []const u8, args: anytype) void {
        var w: std.Io.Writer = .fixed(&self.buf);
        w.print(fmt, args) catch {}; // only `error.WriteFailed`: buffer full, keep what fit
        self.len = w.buffered().len;
        self.line = line;
    }
};

/// One trace operation. `h` is always the handle number (`hN`).
pub const Op = union(enum) {
    alloc: struct { h: u64, size: u64 },
    alloc_aligned: struct { h: u64, size: u64, alignment: u64 },
    calloc: struct { h: u64, count: u64, size: u64 },
    realloc: struct { h: u64, size: u64 },
    realloc_aligned: struct { h: u64, size: u64, alignment: u64 },
    resize: struct { h: u64, size: u64 },
    size: struct { h: u64 },
    free: struct { h: u64 },
    free_sized: struct { h: u64, size: u64 },
    free_sized_aligned: struct { h: u64, size: u64, alignment: u64 },
    purge,

    /// Writes the canonical rendering (§1.4): keyword and arguments separated by single
    /// spaces.
    pub fn render(self: Op, w: *std.Io.Writer) std.Io.Writer.Error!void {
        switch (self) {
            .alloc => |o| try w.print("alloc h{d} {d}", .{ o.h, o.size }),
            .alloc_aligned => |o| try w.print("alloc_aligned h{d} {d} {d}", .{ o.h, o.size, o.alignment }),
            .calloc => |o| try w.print("calloc h{d} {d} {d}", .{ o.h, o.count, o.size }),
            .realloc => |o| try w.print("realloc h{d} {d}", .{ o.h, o.size }),
            .realloc_aligned => |o| try w.print("realloc_aligned h{d} {d} {d}", .{ o.h, o.size, o.alignment }),
            .resize => |o| try w.print("resize h{d} {d}", .{ o.h, o.size }),
            .size => |o| try w.print("size h{d}", .{o.h}),
            .free => |o| try w.print("free h{d}", .{o.h}),
            .free_sized => |o| try w.print("free_sized h{d} {d}", .{ o.h, o.size }),
            .free_sized_aligned => |o| try w.print("free_sized_aligned h{d} {d} {d}", .{ o.h, o.size, o.alignment }),
            .purge => try w.writeAll("purge"),
        }
    }
};

/// A parsed operation and the 1-based line it came from.
pub const Line = struct {
    op: Op,
    number: usize,
};

/// Parses `text` against the contract grammar and checks every semantic constraint.
/// Returns the operations, owned by the caller (free with `gpa`).
pub fn parse(gpa: std.mem.Allocator, text: []const u8, diagnostic: ?*Diagnostic) Error![]Line {
    var scratch: Diagnostic = .{};
    const diag = diagnostic orelse &scratch;
    var lines = std.mem.splitScalar(u8, text, '\n');
    const header = stripCr(lines.first());
    var header_tokens = std.mem.tokenizeAny(u8, header, " \t");
    const header_ok = std.mem.eql(u8, header_tokens.next() orelse "", "oris-trace") and
        std.mem.eql(u8, header_tokens.next() orelse "", "1") and header_tokens.next() == null;
    if (!header_ok) {
        diag.set(1, "missing header `oris-trace 1`", .{});
        return error.Syntax;
    }
    var ops: std.ArrayList(Line) = .empty;
    errdefer ops.deinit(gpa);
    var number: usize = 1;
    // A final line without `eol` is accepted (GRAMMAR.md §1.5); `split` then yields it last,
    // while a well-terminated file yields an empty final piece, which is a blank.
    while (lines.next()) |raw| {
        number += 1;
        const line = stripCr(raw);
        const trimmed = std.mem.trimStart(u8, line, " \t");
        if (trimmed.len == 0 or trimmed[0] == '#') continue;
        const op = parseOp(line, number, diag) orelse return error.Syntax;
        try ops.append(gpa, .{ .op = op, .number = number });
    }
    try validate(gpa, ops.items, diag);
    return ops.toOwnedSlice(gpa);
}

fn stripCr(line: []const u8) []const u8 {
    return if (std.mem.endsWith(u8, line, "\r")) line[0 .. line.len - 1] else line;
}

const Keyword = struct { name: []const u8, arity: usize };

const keywords = [_]Keyword{
    .{ .name = "purge", .arity = 0 },
    .{ .name = "size", .arity = 1 },
    .{ .name = "free", .arity = 1 },
    .{ .name = "alloc", .arity = 2 },
    .{ .name = "realloc", .arity = 2 },
    .{ .name = "resize", .arity = 2 },
    .{ .name = "free_sized", .arity = 2 },
    .{ .name = "alloc_aligned", .arity = 3 },
    .{ .name = "calloc", .arity = 3 },
    .{ .name = "realloc_aligned", .arity = 3 },
    .{ .name = "free_sized_aligned", .arity = 3 },
};

fn parseOp(line: []const u8, number: usize, diag: *Diagnostic) ?Op {
    var tokens = std.mem.tokenizeAny(u8, line, " \t");
    const keyword = tokens.next() orelse "";
    var args: [4][]const u8 = undefined;
    var count: usize = 0;
    while (tokens.next()) |token| : (count += 1) {
        // INDEX: guarded — at most 4 arguments are kept; more than 3 is an arity error
        // for every keyword anyway, reported below with the true count.
        if (count < args.len) args[count] = token;
    }
    const arity = for (keywords) |k| {
        if (std.mem.eql(u8, k.name, keyword)) break k.arity;
    } else {
        diag.set(number, "unknown operation `{s}`", .{keyword});
        return null;
    };
    if (count != arity) {
        diag.set(number, "`{s}` takes {d} argument(s), found {d}", .{ keyword, arity, count });
        return null;
    }
    if (std.mem.eql(u8, keyword, "purge")) return .purge;
    const h = parseHandle(args[0], number, diag) orelse return null;
    var values: [2]u64 = .{ 0, 0 };
    for (1..arity) |i| {
        // INDEX: `i < arity <= 3`, so `i - 1 < 2` and `i < 4`.
        values[i - 1] = parseNumber(args[i], number, diag) orelse return null;
    }
    const a = values[0];
    const b = values[1];
    const eql = std.mem.eql;
    if (eql(u8, keyword, "alloc")) return .{ .alloc = .{ .h = h, .size = a } };
    if (eql(u8, keyword, "alloc_aligned")) return .{ .alloc_aligned = .{ .h = h, .size = a, .alignment = b } };
    if (eql(u8, keyword, "calloc")) return .{ .calloc = .{ .h = h, .count = a, .size = b } };
    if (eql(u8, keyword, "realloc")) return .{ .realloc = .{ .h = h, .size = a } };
    if (eql(u8, keyword, "realloc_aligned")) return .{ .realloc_aligned = .{ .h = h, .size = a, .alignment = b } };
    if (eql(u8, keyword, "resize")) return .{ .resize = .{ .h = h, .size = a } };
    if (eql(u8, keyword, "size")) return .{ .size = .{ .h = h } };
    if (eql(u8, keyword, "free")) return .{ .free = .{ .h = h } };
    if (eql(u8, keyword, "free_sized")) return .{ .free_sized = .{ .h = h, .size = a } };
    return .{ .free_sized_aligned = .{ .h = h, .size = a, .alignment = b } };
}

fn parseHandle(token: []const u8, number: usize, diag: *Diagnostic) ?u64 {
    if (token.len < 2 or token[0] != 'h' or !wellFormed(token[1..])) {
        diag.set(number, "expected a handle `hN`, found `{s}`", .{token});
        return null;
    }
    return std.fmt.parseInt(u64, token[1..], 10) catch {
        diag.set(number, "expected a handle `hN`, found `{s}`", .{token});
        return null;
    };
}

/// `"0" | nonzero_digit , { digit }`.
fn wellFormed(token: []const u8) bool {
    if (token.len == 0) return false;
    for (token) |c| if (!std.ascii.isDigit(c)) return false;
    return std.mem.eql(u8, token, "0") or token[0] != '0';
}

fn parseNumber(token: []const u8, number: usize, diag: *Diagnostic) ?u64 {
    if (!wellFormed(token)) {
        diag.set(number, "expected a number, found `{s}`", .{token});
        return null;
    }
    return std.fmt.parseInt(u64, token, 10) catch {
        diag.set(number, "number `{s}` does not fit in 64 bits", .{token});
        return null;
    };
}

/// What a bound handle was last bound by, for the sized-free rules C6/C7: the size and
/// alignment of its binding `alloc`/`calloc`/`alloc_aligned`, or `null` once a realloc or
/// resize has touched it.
const Binding = ?struct { size: u64, alignment: u64 };

fn sizeOk(size: u64) bool {
    return size <= MAX_TRACE_SIZE;
}

fn alignOk(alignment: u64) bool {
    return alignment == 0 or (std.math.isPowerOfTwo(alignment) and alignment <= MAX_TRACE_ALIGNMENT);
}

/// Checks the semantic constraints C1–C8 (`GRAMMAR.md` §1.3) over the whole trace.
fn validate(gpa: std.mem.Allocator, ops: []const Line, diag: *Diagnostic) Error!void {
    // Bound handles only; an absent key is an unbound handle.
    var bound: std.AutoHashMapUnmanaged(u64, Binding) = .empty;
    defer bound.deinit(gpa);
    for (ops) |line| {
        const n = line.number;
        switch (line.op) {
            inline .alloc, .alloc_aligned => |o, tag| {
                if (bound.contains(o.h)) return semantic(diag, n, "C1: h{d} is already bound", .{o.h});
                if (!sizeOk(o.size)) return semantic(diag, n, "C4: size {d} exceeds 2^30", .{o.size});
                const alignment: u64 = if (tag == .alloc_aligned) o.alignment else 0;
                if (!alignOk(alignment)) return semantic(diag, n, "C3: alignment {d} is not 0 or a power of two at most 65536", .{alignment});
                try bound.put(gpa, o.h, .{ .size = o.size, .alignment = alignment });
            },
            .calloc => |o| {
                if (bound.contains(o.h)) return semantic(diag, n, "C1: h{d} is already bound", .{o.h});
                const product = std.math.mul(u64, o.count, o.size) catch MAX_TRACE_SIZE + 1;
                if (!sizeOk(product)) return semantic(diag, n, "C4: {d} x {d} exceeds 2^30", .{ o.count, o.size });
                try bound.put(gpa, o.h, .{ .size = product, .alignment = 0 });
            },
            inline .realloc, .realloc_aligned => |o, tag| {
                if (!sizeOk(o.size)) return semantic(diag, n, "C4: size {d} exceeds 2^30", .{o.size});
                if (tag == .realloc_aligned) {
                    if (!alignOk(o.alignment)) return semantic(diag, n, "C3: alignment {d} is not 0 or a power of two at most 65536", .{o.alignment});
                    if (o.alignment > 256 and o.size <= 256) return semantic(diag, n, "C8: alignment {d} above 256 needs a size above 256, found {d}", .{ o.alignment, o.size });
                }
                try bound.put(gpa, o.h, null);
            },
            .resize => |o| {
                if (!bound.contains(o.h)) return semantic(diag, n, "C2: h{d} is not bound", .{o.h});
                if (o.size == 0) return semantic(diag, n, "C5: resize to 0", .{});
                if (!sizeOk(o.size)) return semantic(diag, n, "C4: size {d} exceeds 2^30", .{o.size});
                try bound.put(gpa, o.h, null);
            },
            .size => |o| {
                if (!bound.contains(o.h)) return semantic(diag, n, "C2: h{d} is not bound", .{o.h});
            },
            .free => |o| {
                if (!bound.remove(o.h)) return semantic(diag, n, "C2: h{d} is not bound", .{o.h});
            },
            .free_sized => |o| {
                const entry = bound.fetchRemove(o.h) orelse return semantic(diag, n, "C2: h{d} is not bound", .{o.h});
                const fits = if (entry.value) |b| o.size >= 1 and b.size == o.size and b.alignment <= 8 else false;
                if (!fits) return semantic(diag, n, "C6: free_sized h{d} {d} does not directly follow an allocation of exactly {d} bytes at alignment 8 or less", .{ o.h, o.size, o.size });
            },
            .free_sized_aligned => |o| {
                const entry = bound.fetchRemove(o.h) orelse return semantic(diag, n, "C2: h{d} is not bound", .{o.h});
                const fits = if (entry.value) |b| o.size >= 1 and o.alignment >= 1 and b.size == o.size and b.alignment == o.alignment else false;
                if (!fits) return semantic(diag, n, "C7: free_sized_aligned h{d} {d} {d} does not directly follow alloc_aligned h{d} {d} {d}", .{ o.h, o.size, o.alignment, o.h, o.size, o.alignment });
            },
            .purge => {},
        }
    }
}

fn semantic(diag: *Diagnostic, line: usize, comptime fmt: []const u8, args: anytype) Error {
    diag.set(line, fmt, args);
    return error.Semantic;
}

const testing = std.testing;

fn expectRejected(text: []const u8, expected_error: Error, needle: []const u8) !void {
    var diag: Diagnostic = .{};
    const result = parse(testing.allocator, text, &diag);
    if (result) |lines| {
        testing.allocator.free(lines);
        return error.TestUnexpectedResult;
    } else |err| {
        try testing.expectEqual(expected_error, err);
        if (std.mem.indexOf(u8, diag.message(), needle) == null) {
            std.debug.print("message \"{s}\" lacks \"{s}\"\n", .{ diag.message(), needle });
            return error.TestUnexpectedResult;
        }
    }
}

test "parses every operation and renders it canonically" {
    const text = "oris-trace 1\n# comment\n\nalloc h0 24\nalloc_aligned h1 100 64\n" ++
        "calloc h2 4 8\nrealloc h0 300\nrealloc_aligned h1 400 64\nresize h0 200\n" ++
        "size h0\nfree h0\nfree_sized h2 32\nfree h1\nalloc h3 7\nfree_sized h3 7\n" ++
        "alloc_aligned h4 300 512\nfree_sized_aligned h4 300 512\npurge\n";
    const lines = try parse(testing.allocator, text, null);
    defer testing.allocator.free(lines);
    var rendered: std.Io.Writer.Allocating = .init(testing.allocator);
    defer rendered.deinit();
    for (lines) |line| {
        try line.op.render(&rendered.writer);
        try rendered.writer.writeByte('\n');
    }
    var expected_lines = std.mem.splitScalar(u8, text, '\n');
    for (0..3) |_| _ = expected_lines.next();
    try testing.expectEqualStrings(expected_lines.rest(), rendered.written());
}

test "accepts tabs, runs of spaces, CRLF and a missing final eol" {
    const lines = try parse(testing.allocator, "oris-trace 1\r\n\t alloc \th0   24 \r\n  # indented comment\r\nfree h0", null);
    defer testing.allocator.free(lines);
    try testing.expectEqual(@as(usize, 2), lines.len);
    try testing.expectEqual(Op{ .alloc = .{ .h = 0, .size = 24 } }, lines[0].op);
    try testing.expectEqual(Op{ .free = .{ .h = 0 } }, lines[1].op);
    try testing.expectEqual(@as(usize, 4), lines[1].number);
}

test "rejects bad syntax with its line number" {
    var diag: Diagnostic = .{};
    try testing.expectError(error.Syntax, parse(testing.allocator, "", &diag));
    try testing.expectEqual(@as(usize, 1), diag.line);
    try expectRejected("oris-trace 2\n", error.Syntax, "header");
    try expectRejected("oris-trace 1\nalloc h0\n", error.Syntax, "argument");
    try expectRejected("oris-trace 1\nalloc h0 024\n", error.Syntax, "`024`");
    try expectRejected("oris-trace 1\nalloc x0 24\n", error.Syntax, "handle");
    try expectRejected("oris-trace 1\nalloc h0 18446744073709551616\n", error.Syntax, "64 bits");
    try expectRejected("oris-trace 1\npurge now\n", error.Syntax, "argument");
    try testing.expectError(error.Syntax, parse(testing.allocator, "oris-trace 1\n\nmalloc h0 24\n", &diag));
    try testing.expectEqual(@as(usize, 3), diag.line);
}

test "enforces every semantic constraint" {
    const cases = [_]struct { []const u8, []const u8 }{
        .{ "alloc h0 8\nalloc h0 8", "C1" },
        .{ "free h0", "C2" },
        .{ "alloc h0 8\nfree h0\nfree h0", "C2" },
        .{ "alloc_aligned h0 8 3", "C3" },
        .{ "alloc_aligned h0 8 131072", "C3" },
        .{ "alloc h0 1073741825", "C4" },
        .{ "calloc h0 1073741824 2", "C4" },
        .{ "calloc h0 4294967296 4294967296", "C4" },
        .{ "alloc h0 8\nresize h0 0", "C5" },
        .{ "alloc h0 100\nrealloc h0 20\nfree_sized h0 20", "C6" },
        .{ "alloc h0 100\nfree_sized h0 64", "C6" },
        .{ "alloc h0 0\nfree_sized h0 0", "C6" },
        .{ "alloc_aligned h0 5 4096\nfree_sized h0 5", "C6" },
        .{ "alloc_aligned h0 64 16\nfree_sized_aligned h0 64 32", "C7" },
        .{ "alloc h0 64\nfree_sized_aligned h0 64 8", "C7" },
        .{ "realloc_aligned h0 100 512", "C8" },
    };
    for (cases) |case| {
        var buf: [128]u8 = undefined;
        const text = try std.fmt.bufPrint(&buf, "oris-trace 1\n{s}\n", .{case[0]});
        try expectRejected(text, error.Semantic, case[1]);
    }
}

test "accepts the boundaries of every constraint" {
    const text = "oris-trace 1\nalloc h0 1073741824\nfree h0\nalloc_aligned h1 8 65536\n" ++
        "free_sized_aligned h1 8 65536\nalloc_aligned h2 8 0\nfree_sized h2 8\n" ++
        "calloc h3 2 12\nfree_sized h3 24\nrealloc h4 10\nrealloc h4 0\nsize h4\n" ++
        "free h4\nrealloc_aligned h5 257 512\nresize h5 1\nfree h5\nalloc h0 0\nfree h0\n";
    const lines = try parse(testing.allocator, text, null);
    defer testing.allocator.free(lines);
    try testing.expectEqual(@as(usize, 17), lines.len);
}
