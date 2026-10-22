// SPDX-License-Identifier: MIT OR Apache-2.0
//! Replays an Oris trace (`examples/traces/GRAMMAR.md`) through one allocator and reports
//! one measurement pass as JSON lines on stdout — the Zig twin of `bench-rust`, with the same
//! command line, passes and record fields. See `benchmarks/methodology.md`.
//!
//! ```text
//! bench-zig --allocator orisnitsa --trace ../../traces/planner-1m.trace --pass wall
//! ```
//!
//! Allocators: `orisnitsa` (driven through its own API, so every trace operation means
//! what it means to the transition record), `smp` (`std.heap.smp_allocator`) and `c`
//! (`std.heap.c_allocator`). The two `std.mem.Allocator`s get the same treatment as
//! `bench-rust`'s `GlobalAlloc`s: `resize` and `size` report the tracked size, `purge` does
//! nothing, a plain allocation asks for alignment 8.
//!
//! The harness's own memory (the trace text, the operation array) comes from
//! `std.heap.page_allocator` and is never freed, so no allocator under test can reuse it
//! — the memory pass would otherwise measure the harness.

const std = @import("std");
const builtin = @import("builtin");
const orisnitsa = @import("orisnitsa");

const Oris = orisnitsa.Orisnitsa;

const Op = union(enum) {
    alloc: struct { slot: usize, size: usize, alignment: usize },
    calloc: struct { slot: usize, count: usize, size: usize },
    realloc: struct { slot: usize, size: usize, alignment: usize },
    resize: struct { slot: usize, size: usize },
    size: struct { slot: usize },
    free: struct { slot: usize, sized: bool },
    purge,
};

const Slot = struct {
    ptr: ?[*]u8 = null,
    size: usize = 0,
    alignment: usize = 0,
};

const Trace = struct {
    name: []const u8,
    ops: []Op,
    slots: usize,
    peak_live: u64,
};

fn loadTrace(arena: std.mem.Allocator, io: std.Io, path: []const u8) !Trace {
    const text = try std.Io.Dir.cwd().readFileAlloc(io, path, arena, .unlimited);
    var lines = std.mem.splitScalar(u8, text, '\n');
    const header = std.mem.trim(u8, lines.first(), " \t\r");
    if (!std.mem.eql(u8, header, "oris-trace 1")) return error.MissingHeader;
    var slot_of: std.AutoHashMapUnmanaged(u64, usize) = .empty;
    var ops: std.ArrayList(Op) = .empty;
    var live: std.ArrayList(u64) = .empty;
    var live_now: u64 = 0;
    var peak_live: u64 = 0;
    while (lines.next()) |raw| {
        const line = std.mem.trim(u8, raw, " \t\r");
        if (line.len == 0 or line[0] == '#') continue;
        var tokens = std.mem.tokenizeAny(u8, line, " \t");
        const keyword = tokens.next().?;
        if (std.mem.eql(u8, keyword, "purge")) {
            try ops.append(arena, .purge);
            continue;
        }
        const handle = tokens.next() orelse return error.BadLine;
        if (handle.len < 2 or handle[0] != 'h') return error.BadLine;
        const h = try std.fmt.parseInt(u64, handle[1..], 10);
        var nums: [2]usize = .{ 0, 0 };
        var count: usize = 0;
        while (tokens.next()) |t| : (count += 1) {
            if (count == nums.len) return error.BadLine;
            nums[count] = try std.fmt.parseInt(usize, t, 10);
        }
        const entry = try slot_of.getOrPut(arena, h);
        if (!entry.found_existing) {
            entry.value_ptr.* = slot_of.count() - 1;
            try live.append(arena, 0);
        }
        const slot = entry.value_ptr.*;
        const eql = std.mem.eql;
        const op: Op = if (eql(u8, keyword, "alloc"))
            .{ .alloc = .{ .slot = slot, .size = nums[0], .alignment = 0 } }
        else if (eql(u8, keyword, "alloc_aligned"))
            .{ .alloc = .{ .slot = slot, .size = nums[0], .alignment = nums[1] } }
        else if (eql(u8, keyword, "calloc"))
            .{ .calloc = .{ .slot = slot, .count = nums[0], .size = nums[1] } }
        else if (eql(u8, keyword, "realloc"))
            .{ .realloc = .{ .slot = slot, .size = nums[0], .alignment = 0 } }
        else if (eql(u8, keyword, "realloc_aligned"))
            .{ .realloc = .{ .slot = slot, .size = nums[0], .alignment = nums[1] } }
        else if (eql(u8, keyword, "resize"))
            .{ .resize = .{ .slot = slot, .size = nums[0] } }
        else if (eql(u8, keyword, "size"))
            .{ .size = .{ .slot = slot } }
        else if (eql(u8, keyword, "free"))
            .{ .free = .{ .slot = slot, .sized = false } }
        else
            .{ .free = .{ .slot = slot, .sized = true } };
        const new_live: ?u64 = switch (op) {
            .alloc => |o| o.size,
            .realloc => |o| o.size,
            .calloc => |o| o.count * o.size,
            .free => 0,
            .resize, .size, .purge => null,
        };
        if (new_live) |size| {
            live_now = live_now - live.items[slot] + size;
            live.items[slot] = size;
            peak_live = @max(peak_live, live_now);
        }
        try ops.append(arena, op);
    }
    return .{ .name = std.fs.path.stem(path), .ops = ops.items, .slots = slot_of.count(), .peak_live = peak_live };
}

/// One allocator under test.
const Backend = union(enum) {
    oris: *Oris,
    std_allocator: std.mem.Allocator,

    fn alignmentOf(alignment: usize) std.mem.Alignment {
        return .fromByteUnits(@max(alignment, 8));
    }

    fn alloc(self: Backend, size: usize, alignment: usize) ?[*]u8 {
        switch (self) {
            .oris => |o| return if (alignment == 0) o.alloc(size) else o.allocAligned(size, alignment),
            .std_allocator => |a| {
                if (size == 0) return null; // as `orisnitsa` (and HPHA) answer alloc(0)
                return a.rawAlloc(size, alignmentOf(alignment), @returnAddress());
            },
        }
    }

    fn calloc(self: Backend, count: usize, size: usize) ?[*]u8 {
        switch (self) {
            .oris => |o| return o.calloc(count, size),
            .std_allocator => {
                const p = self.alloc(count * size, 0) orelse return null;
                @memset(p[0 .. count * size], 0);
                return p;
            },
        }
    }

    fn realloc(self: Backend, old: Slot, size: usize, alignment: usize) ?[*]u8 {
        switch (self) {
            .oris => |o| return if (alignment == 0) o.realloc(old.ptr, size) else o.reallocAligned(old.ptr, size, alignment),
            .std_allocator => |a| {
                const p = old.ptr orelse return self.alloc(size, alignment);
                const old_memory = p[0..@max(old.size, 1)];
                if (size == 0) {
                    a.rawFree(old_memory, alignmentOf(old.alignment), @returnAddress());
                    return null;
                }
                if (@max(alignment, 8) == @max(old.alignment, 8)) {
                    if (a.rawRemap(old_memory, alignmentOf(alignment), size, @returnAddress())) |q| return q;
                }
                const q = a.rawAlloc(size, alignmentOf(alignment), @returnAddress()) orelse return null;
                @memcpy(q[0..@min(old.size, size)], p[0..@min(old.size, size)]);
                a.rawFree(old_memory, alignmentOf(old.alignment), @returnAddress());
                return q;
            },
        }
    }

    fn resize(self: Backend, slot: Slot, size: usize) usize {
        return switch (self) {
            .oris => |o| o.resize(slot.ptr, size),
            .std_allocator => slot.size,
        };
    }

    fn querySize(self: Backend, slot: Slot) usize {
        return switch (self) {
            .oris => |o| o.querySize(slot.ptr),
            .std_allocator => slot.size,
        };
    }

    fn free(self: Backend, slot: Slot, sized: bool) void {
        switch (self) {
            .oris => |o| {
                if (!sized) return o.free(slot.ptr);
                if (slot.alignment <= 8) return o.freeWithSize(slot.ptr, slot.size);
                o.freeWithSizeAligned(slot.ptr, slot.size, slot.alignment);
            },
            .std_allocator => |a| if (slot.ptr) |p| a.rawFree(p[0..@max(slot.size, 1)], alignmentOf(slot.alignment), @returnAddress()),
        }
    }

    fn purge(self: Backend) void {
        switch (self) {
            .oris => |o| o.purge(),
            .std_allocator => {},
        }
    }

    fn mapped(self: Backend) ?u64 {
        return switch (self) {
            .oris => |o| o.allocated(),
            .std_allocator => null,
        };
    }
};

/// Writes one byte per 4 KiB page of a fresh block, as a program filling it would.
fn touch(p: [*]u8, size: usize) void {
    var offset: usize = 0;
    while (offset < size) : (offset += 4096) {
        const byte: *volatile u8 = &p[offset];
        byte.* = 1;
    }
}

fn step(backend: Backend, op: Op, slots: []Slot) void {
    switch (op) {
        .alloc => |o| {
            const p = backend.alloc(o.size, o.alignment);
            if (p) |q| touch(q, o.size);
            slots[o.slot] = .{ .ptr = p, .size = o.size, .alignment = o.alignment };
        },
        .calloc => |o| slots[o.slot] = .{ .ptr = backend.calloc(o.count, o.size), .size = o.count * o.size },
        .realloc => |o| {
            const old = slots[o.slot];
            const p = backend.realloc(old, o.size, o.alignment);
            if (p) |q| if (o.size > old.size) touch(q + old.size, o.size - old.size);
            if (p != null or o.size == 0) slots[o.slot] = .{ .ptr = p, .size = o.size, .alignment = o.alignment };
        },
        .resize => |o| slots[o.slot].size = backend.resize(slots[o.slot], o.size),
        .size => |o| std.mem.doNotOptimizeAway(backend.querySize(slots[o.slot])),
        .free => |o| {
            backend.free(slots[o.slot], o.sized);
            slots[o.slot] = .{};
        },
        .purge => backend.purge(),
    }
}

fn release(backend: Backend, slots: []Slot) void {
    for (slots) |*slot| {
        if (slot.ptr != null) backend.free(slot.*, false);
        slot.* = .{};
    }
}

const Sampler = struct { peak_rss: u64, peak_mapped: u64 };

const Probe = union(enum) {
    none,
    latency: *std.ArrayList(u64),
    memory: *Sampler,
};

fn now(io: std.Io) i96 {
    return std.Io.Clock.awake.now(io).nanoseconds;
}

fn replay(io: std.Io, backend: Backend, trace: Trace, slots: []Slot, probe: Probe) void {
    for (trace.ops, 0..) |op, i| {
        switch (probe) {
            .none => step(backend, op, slots),
            .latency => |times| {
                const start = now(io);
                step(backend, op, slots);
                times.appendAssumeCapacity(@intCast(now(io) - start));
            },
            .memory => |sampler| {
                step(backend, op, slots);
                if (i % 256 == 0 or op == .purge) {
                    sampler.peak_rss = @max(sampler.peak_rss, currentRss(io));
                    if (backend.mapped()) |m| sampler.peak_mapped = @max(sampler.peak_mapped, m);
                }
            },
        }
    }
}

// ---- resident set size ----

const PROCESS_MEMORY_COUNTERS = extern struct {
    cb: u32,
    PageFaultCount: u32,
    PeakWorkingSetSize: usize,
    WorkingSetSize: usize,
    QuotaPeakPagedPoolUsage: usize,
    QuotaPagedPoolUsage: usize,
    QuotaPeakNonPagedPoolUsage: usize,
    QuotaNonPagedPoolUsage: usize,
    PagefileUsage: usize,
    PeakPagefileUsage: usize,
};
extern "kernel32" fn K32GetProcessMemoryInfo(process: std.os.windows.HANDLE, counters: *PROCESS_MEMORY_COUNTERS, cb: u32) callconv(.winapi) c_int;
extern "kernel32" fn GetCurrentProcess() callconv(.winapi) std.os.windows.HANDLE;

/// The current resident set: `VmRSS` on Linux, the working set on Windows, `ru_maxrss` (a
/// lifetime peak) elsewhere — as `bench-rust` measures it.
fn currentRss(io: std.Io) u64 {
    switch (builtin.os.tag) {
        .windows => {
            var counters: PROCESS_MEMORY_COUNTERS = std.mem.zeroes(PROCESS_MEMORY_COUNTERS);
            if (K32GetProcessMemoryInfo(GetCurrentProcess(), &counters, @sizeOf(PROCESS_MEMORY_COUNTERS)) == 0) return 0;
            return counters.WorkingSetSize;
        },
        .linux => {
            var buf: [4096]u8 = undefined;
            const status = std.Io.Dir.cwd().readFile(io, "/proc/self/status", &buf) catch return 0;
            var lines = std.mem.splitScalar(u8, status, '\n');
            while (lines.next()) |line| {
                if (std.mem.startsWith(u8, line, "VmRSS:")) {
                    var t = std.mem.tokenizeAny(u8, line["VmRSS:".len..], " \tk");
                    const kb = std.fmt.parseInt(u64, t.next() orelse "0", 10) catch 0;
                    return kb * 1024;
                }
            }
            return 0;
        },
        else => {
            var usage: std.c.rusage = undefined;
            _ = std.c.getrusage(std.c.rusage.SELF, &usage);
            return @intCast(usage.maxrss);
        },
    }
}

// ---- main ----

fn timerOverhead(io: std.Io, scratch: std.mem.Allocator) !u64 {
    const samples = try scratch.alloc(u64, 10_001);
    for (samples) |*s| {
        const a = now(io);
        s.* = @intCast(now(io) - a);
    }
    std.mem.sort(u64, samples, {}, std.sort.asc(u64));
    return samples[samples.len / 2];
}

pub fn main(init: std.process.Init) !u8 {
    const io = init.io;
    var arena_state = std.heap.ArenaAllocator.init(std.heap.page_allocator);
    const arena = arena_state.allocator(); // never freed: see the module doc
    const argv = try init.minimal.args.toSlice(arena);

    var allocator_name: []const u8 = "";
    var trace_path: []const u8 = "";
    var pass: []const u8 = "";
    var warmup: usize = 2;
    var repetitions: usize = 10;
    var env: []const u8 = "null";
    var i: usize = 1;
    while (i < argv.len) : (i += 2) {
        const flag = argv[i];
        if (std.mem.eql(u8, flag, "--list")) {
            std.debug.print("orisnitsa smp c\n", .{});
            return 0;
        }
        if (i + 1 >= argv.len) {
            std.debug.print("bench-zig: {s} needs a value\n", .{flag});
            return 2;
        }
        const value = argv[i + 1];
        if (std.mem.eql(u8, flag, "--allocator")) allocator_name = value else if (std.mem.eql(u8, flag, "--trace")) trace_path = value else if (std.mem.eql(u8, flag, "--pass")) pass = value else if (std.mem.eql(u8, flag, "--warmup")) warmup = try std.fmt.parseInt(usize, value, 10) else if (std.mem.eql(u8, flag, "--repetitions")) repetitions = try std.fmt.parseInt(usize, value, 10) else if (std.mem.eql(u8, flag, "--env-file")) {
            env = std.mem.trim(u8, try std.Io.Dir.cwd().readFileAlloc(io, value, arena, .unlimited), " \t\r\n");
        } else {
            std.debug.print("bench-zig: unknown argument `{s}`\n", .{flag});
            return 2;
        }
    }
    if (allocator_name.len == 0 or trace_path.len == 0 or pass.len == 0) {
        std.debug.print("usage: bench-zig --allocator orisnitsa|smp|c --trace <file> --pass wall|latency|memory [--warmup N] [--repetitions N] [--env-file <json>]\n", .{});
        return 2;
    }
    const trace = loadTrace(arena, io, trace_path) catch |err| {
        std.debug.print("bench-zig: {s}: {s}\n", .{ trace_path, @errorName(err) });
        return 2;
    };

    var oris: Oris = .init(); // not moved after first use; its address is stable here
    const backend: Backend = if (std.mem.eql(u8, allocator_name, "orisnitsa"))
        .{ .oris = &oris }
    else if (std.mem.eql(u8, allocator_name, "smp"))
        .{ .std_allocator = std.heap.smp_allocator }
    else if (std.mem.eql(u8, allocator_name, "c"))
        .{ .std_allocator = std.heap.c_allocator }
    else {
        std.debug.print("bench-zig: unknown allocator `{s}` (orisnitsa, smp, c)\n", .{allocator_name});
        return 2;
    };
    const slots = try arena.alloc(Slot, trace.slots);
    @memset(slots, .{});

    var out_buffer: [4096]u8 = undefined;
    var stdout = std.Io.File.stdout().writerStreaming(io, &out_buffer);
    const w = &stdout.interface;
    const head = "{{\"schema_version\":1,\"harness\":\"zig\",\"allocator\":\"{s}\",\"trace\":\"{s}\",\"ops\":{d},\"pass\":\"{s}\",\"env\":{s}";

    if (std.mem.eql(u8, pass, "wall")) {
        for (0..warmup) |_| {
            replay(io, backend, trace, slots, .none);
            release(backend, slots);
        }
        for (0..repetitions) |rep| {
            const start = now(io);
            replay(io, backend, trace, slots, .none);
            const wall: i96 = now(io) - start;
            release(backend, slots);
            try w.print(head ++ ",\"rep\":{d},\"wall_ns\":{d}}}\n", .{ allocator_name, trace.name, trace.ops.len, pass, env, rep, wall });
        }
    } else if (std.mem.eql(u8, pass, "latency")) {
        for (0..warmup) |_| {
            replay(io, backend, trace, slots, .none);
            release(backend, slots);
        }
        var times = try std.ArrayList(u64).initCapacity(arena, trace.ops.len);
        replay(io, backend, trace, slots, .{ .latency = &times });
        release(backend, slots);
        std.mem.sort(u64, times.items, {}, std.sort.asc(u64));
        const t = times.items;
        const at = struct {
            fn f(sorted: []const u64, q: f64) u64 {
                if (sorted.len == 0) return 0;
                const index: usize = @intFromFloat(@round(@as(f64, @floatFromInt(sorted.len - 1)) * q));
                return sorted[index];
            }
        }.f;
        try w.print(head ++ ",\"p50_ns\":{d},\"p99_ns\":{d},\"p999_ns\":{d},\"max_ns\":{d},\"timer_overhead_ns\":{d}}}\n", .{
            allocator_name, trace.name,  trace.ops.len, pass,                               env,
            at(t, 0.5),     at(t, 0.99), at(t, 0.999),  if (t.len > 0) t[t.len - 1] else 0, try timerOverhead(io, arena),
        });
    } else if (std.mem.eql(u8, pass, "memory")) {
        const baseline = currentRss(io);
        var sampler: Sampler = .{ .peak_rss = baseline, .peak_mapped = backend.mapped() orelse 0 };
        replay(io, backend, trace, slots, .{ .memory = &sampler });
        sampler.peak_rss = @max(sampler.peak_rss, currentRss(io));
        const delta = sampler.peak_rss -| baseline;
        const fragmentation: f64 = if (trace.peak_live == 0) 0 else @as(f64, @floatFromInt(delta)) / @as(f64, @floatFromInt(trace.peak_live));
        var mapped_buf: [32]u8 = undefined;
        const mapped = if (backend.mapped() != null) try std.fmt.bufPrint(&mapped_buf, "{d}", .{sampler.peak_mapped}) else "null";
        try w.print(head ++ ",\"baseline_rss_bytes\":{d},\"peak_rss_bytes\":{d},\"peak_rss_delta_bytes\":{d},\"peak_live_bytes\":{d},\"fragmentation\":{d},\"peak_mapped_bytes\":{s}}}\n", .{
            allocator_name, trace.name,       trace.ops.len, pass,            env,
            baseline,       sampler.peak_rss, delta,         trace.peak_live, fragmentation,
            mapped,
        });
        release(backend, slots);
    } else {
        std.debug.print("bench-zig: unknown pass `{s}`\n", .{pass});
        return 2;
    }
    try w.flush();
    release(backend, slots);
    oris.deinit();
    return 0;
}
