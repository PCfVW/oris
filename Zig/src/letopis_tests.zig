// SPDX-License-Identifier: MIT OR Apache-2.0
//! Replay and recorder tests. Each embedded trace and expected record also exists in
//! `orisnik`'s `letopis/tests.rs`, with the same expectation: a difference between the
//! two files is a cross-port divergence, caught here before CI's corpus gate.

const std = @import("std");
const letopis = @import("letopis.zig");
const orisnitsa = @import("orisnitsa.zig");

const testing = std.testing;

fn expectRecord(trace: []const u8, expected: []const u8) !void {
    var out: std.Io.Writer.Allocating = .init(testing.allocator);
    defer out.deinit();
    var diag: letopis.Diagnostic = .{};
    letopis.replay(testing.allocator, trace, &out.writer, &diag) catch |err| {
        std.debug.print("replay failed: {s} (line {d}): {s}\n", .{ @errorName(err), diag.line, diag.message() });
        return err;
    };
    try testing.expectEqualStrings(expected, out.written());
}

test "the grammar's example trace" {
    try expectRecord(
        \\oris-trace 1
        \\alloc h0 24
        \\alloc h1 1000
        \\realloc h1 2000
        \\free_sized h0 24
        \\free h1
        \\purge
        \\
    ,
        \\oris-record 1
        \\#0 alloc h0 24 -> m0+0x0 a=65536
        \\  map b m0 65536
        \\  page+ b2 m0
        \\#1 alloc h1 1000 -> m1+0x20 a=131072
        \\  map t m1 65536
        \\  split m1+0x10 1008
        \\  mr m1+0x410
        \\#2 realloc h1 2000 -> m1+0x20 a=131072
        \\  mr -
        \\  merge m1+0x410
        \\  split m1+0x10 2000
        \\  mr m1+0x7f0
        \\#3 free_sized h0 24 -> - a=131072
        \\#4 free h1 -> - a=131072
        \\  mr -
        \\  merge m1+0x7f0
        \\  mr m1+0x10
        \\#5 purge -> - a=0
        \\  tree+ m1+0x10 65488 node rot=0
        \\  mr -
        \\  tree- m1+0x10 65488 node rot=0
        \\  unmap m1 65536
        \\  mr -
        \\  page- b2 m0
        \\  unmap m0 65536
        \\end ops=6 maps=2 unmaps=2 rotations=0 allocated=0
        \\
    );
}

/// The xorshift32 every port's tests share.
const Xorshift = struct {
    state: u32,

    fn next(self: *Xorshift) u32 {
        self.state ^= self.state << 13;
        self.state ^= self.state >> 17;
        self.state ^= self.state << 5;
        return self.state;
    }

    /// A value in `[0, bound)`.
    fn below(self: *Xorshift, bound: u32) u32 {
        return self.next() % bound;
    }
};

/// A live handle of the generated trace: its number, and the size/alignment of the
/// allocation that bound it while a sized free is still allowed (`GRAMMAR.md` C6/C7).
const Live = struct {
    h: u32,
    fresh: ?struct { size: u32, alignment: u32 },
};

/// A deterministic mixed workload, generated identically by `orisnik`'s
/// `generated_trace`: a burst that fills a bucket page, then 4000 random operations over
/// every kind the grammar has, satisfying every semantic constraint. Caller frees.
fn generatedTrace(gpa: std.mem.Allocator) ![]u8 {
    var rng: Xorshift = .{ .state = 0x5eed_1e70 };
    var out: std.Io.Writer.Allocating = .init(gpa);
    errdefer out.deinit();
    const w = &out.writer;
    try w.writeAll("oris-trace 1\n");
    var live: std.ArrayList(Live) = .empty;
    defer live.deinit(gpa);
    var next_h: u32 = 0;
    // 300 256-byte slots: more than one page of bucket 31 holds (255), so a page fills.
    for (0..300) |_| {
        try w.print("alloc h{d} 256\n", .{next_h});
        try live.append(gpa, .{ .h = next_h, .fresh = .{ .size = 256, .alignment = 0 } });
        next_h += 1;
    }
    for (0..4000) |_| {
        const r = rng.below(100);
        if (live.items.len == 0 or r < 40) {
            const h = next_h;
            next_h += 1;
            var size: u32 = undefined;
            var alignment: u32 = 0;
            switch (rng.below(4)) {
                0 => {
                    size = 1 + rng.below(256);
                    try w.print("alloc h{d} {d}\n", .{ h, size });
                },
                1 => {
                    size = 257 + rng.below(8000);
                    try w.print("alloc h{d} {d}\n", .{ h, size });
                },
                2 => {
                    alignment = ([_]u32{ 16, 64, 256, 4096 })[rng.below(4)];
                    size = 1 + rng.below(3000);
                    try w.print("alloc_aligned h{d} {d} {d}\n", .{ h, size, alignment });
                },
                else => {
                    const count = 1 + rng.below(16);
                    const each = 1 + rng.below(64);
                    size = count * each;
                    try w.print("calloc h{d} {d} {d}\n", .{ h, count, each });
                },
            }
            try live.append(gpa, .{ .h = h, .fresh = .{ .size = size, .alignment = alignment } });
            continue;
        }
        const index = rng.below(@intCast(live.items.len));
        if (r < 60) {
            const size = 1 + rng.below(20_000);
            const entry = &live.items[index];
            try w.print("realloc h{d} {d}\n", .{ entry.h, size });
            entry.fresh = null;
        } else if (r < 65) {
            const alignment = ([_]u32{ 16, 64, 512 })[rng.below(3)];
            const size = if (alignment > 256) 257 + rng.below(5000) else 1 + rng.below(5000);
            const entry = &live.items[index];
            try w.print("realloc_aligned h{d} {d} {d}\n", .{ entry.h, size, alignment });
            entry.fresh = null;
        } else if (r < 70) {
            const size = 1 + rng.below(10_000);
            const entry = &live.items[index];
            try w.print("resize h{d} {d}\n", .{ entry.h, size });
            entry.fresh = null;
        } else if (r < 72) {
            try w.print("size h{d}\n", .{live.items[index].h});
        } else if (r < 99) {
            const entry = live.swapRemove(index);
            const sized = rng.below(2) == 0;
            if (entry.fresh != null and sized and entry.fresh.?.size >= 1 and entry.fresh.?.alignment <= 8) {
                try w.print("free_sized h{d} {d}\n", .{ entry.h, entry.fresh.?.size });
            } else if (entry.fresh != null and sized and entry.fresh.?.size >= 1) {
                try w.print("free_sized_aligned h{d} {d} {d}\n", .{ entry.h, entry.fresh.?.size, entry.fresh.?.alignment });
            } else {
                try w.print("free h{d}\n", .{entry.h});
            }
        } else {
            try w.writeAll("purge\n");
        }
    }
    return out.toOwnedSlice();
}

/// FNV-1a, 64-bit: a fingerprint of a whole record that both ports' tests can pin.
fn fnv1a(bytes: []const u8) u64 {
    var hash: u64 = 0xcbf2_9ce4_8422_2325;
    for (bytes) |b| hash = (hash ^ b) *% 0x0000_0100_0000_01b3;
    return hash;
}

test "a generated workload emits every event kind and the shared fingerprint" {
    const trace = try generatedTrace(testing.allocator);
    defer testing.allocator.free(trace);
    var out: std.Io.Writer.Allocating = .init(testing.allocator);
    defer out.deinit();
    try letopis.replay(testing.allocator, trace, &out.writer, null);
    const record = out.written();
    const needles = [_][]const u8{
        "\n  map b ",     "\n  map t ",       "\n  unmap ", "\n  page+ ",    "\n  page- ",
        "\n  page-full ", "\n  page-refill ", "\n  split ", "\n  shift ",    "\n  merge ",
        " chain rot=",    " node rot=",       " link rot=", " promote rot=", "\n  list+ ",
        "\n  list- ",     "\n  mr m",         "\n  mr -",   " rot=1\n",      " rot=2\n",
    };
    for (needles) |needle| {
        if (std.mem.indexOf(u8, record, needle) == null) {
            std.debug.print("no `{s}` in the record\n", .{needle});
            return error.TestUnexpectedResult;
        }
    }
    // The same values are pinned in `orisnik`'s `letopis/tests.rs`: the two ports wrote the
    // same 4300-operation record byte for byte.
    try testing.expectEqual(@as(u64, 18_252_001_378_337_324_280), fnv1a(trace));
    try testing.expectEqual(@as(u64, 7_125_967_866_125_270_486), fnv1a(record));
}

test "a rejected trace executes nothing" {
    var out: std.Io.Writer.Allocating = .init(testing.allocator);
    defer out.deinit();
    var diag: letopis.Diagnostic = .{};
    try testing.expectError(error.Semantic, letopis.replay(testing.allocator, "oris-trace 1\nalloc h0 8\nfree h1\n", &out.writer, &diag));
    try testing.expectEqual(@as(usize, 3), diag.line);
    try testing.expectEqualStrings("C2: h1 is not bound", diag.message());
    try testing.expectEqual(@as(usize, 0), out.written().len);
}

test "the recorder writes what replays to the same record" {
    var backing: orisnitsa.Orisnitsa(.{}) = .init();
    defer backing.deinit();
    var trace: std.Io.Writer.Allocating = .init(testing.allocator);
    defer trace.deinit();
    var recorder = letopis.Recorder(.{}).init(&backing, testing.allocator, &trace.writer);
    defer recorder.deinit();

    const small = recorder.alloc(24);
    var big = recorder.allocAligned(3000, 64);
    big = recorder.realloc(big, 9000);
    const zeroed = recorder.calloc(4, 8);
    _ = recorder.resize(big, 100);
    _ = recorder.querySize(zeroed);
    recorder.free(null); // not recorded: nothing to record
    recorder.freeWithSize(small, 24);
    recorder.free(zeroed);
    const grown = recorder.realloc(null, 40);
    try testing.expect(recorder.realloc(grown, 0) == null);
    recorder.free(big);
    recorder.purge();
    try recorder.finish();
    try testing.expectEqualStrings(
        "oris-trace 1\nalloc h0 24\nalloc_aligned h1 3000 64\nrealloc h1 9000\ncalloc h2 4 8\n" ++
            "resize h1 100\nsize h2\nfree_sized h0 24\nfree h2\nrealloc h3 40\nrealloc h3 0\nfree h1\n" ++
            "purge\n",
        trace.written(),
    );

    // Through the `std.mem.Allocator` interface, too.
    const gpa = recorder.allocator();
    const slice = try gpa.alloc(u8, 100);
    gpa.free(slice);
    try recorder.finish();
    try testing.expect(std.mem.endsWith(u8, trace.written(), "purge\nalloc h4 100\nfree h4\n"));

    // What was recorded replays: it satisfies every constraint.
    var record: std.Io.Writer.Allocating = .init(testing.allocator);
    defer record.deinit();
    try letopis.replay(testing.allocator, trace.written(), &record.writer, null);
}
