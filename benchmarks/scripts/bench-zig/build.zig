// SPDX-License-Identifier: MIT OR Apache-2.0
const std = @import("std");

/// `zig build -Doptimize=ReleaseFast` builds `zig-out/bin/bench-zig`: the Zig half of the
/// trace-replay benchmarks (`benchmarks/methodology.md`), replaying Oris traces through
/// `orisnitsa`, `std.heap.smp_allocator` and `std.heap.c_allocator`.
pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const orisnitsa = b.dependency("orisnitsa", .{ .target = target, .optimize = optimize });
    const exe = b.addExecutable(.{
        .name = "bench-zig",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/main.zig"),
            .target = target,
            .optimize = optimize,
            .imports = &.{.{ .name = "orisnitsa", .module = orisnitsa.module("orisnitsa") }},
            // `c_allocator` is one of the allocators under test.
            .link_libc = true,
        }),
    });
    b.installArtifact(exe);
}
