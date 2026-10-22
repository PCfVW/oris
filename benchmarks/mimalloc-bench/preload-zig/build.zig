// SPDX-License-Identifier: MIT OR Apache-2.0
const std = @import("std");

/// `zig build -Doptimize=ReleaseFast` builds `zig-out/lib/liborispreload-zig.so`, the
/// `LD_PRELOAD` shim mimalloc-bench runs as allocator `onit` (Linux only).
pub fn build(b: *std.Build) void {
    const target = b.standardTargetOptions(.{});
    const optimize = b.standardOptimizeOption(.{});
    const orisnitsa = b.dependency("orisnitsa", .{ .target = target, .optimize = optimize });
    const lib = b.addLibrary(.{
        .name = "orispreload-zig",
        .linkage = .dynamic,
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/preload.zig"),
            .target = target,
            .optimize = optimize,
            .link_libc = true,
            .imports = &.{.{ .name = "orisnitsa", .module = orisnitsa.module("orisnitsa") }},
        }),
    });
    b.installArtifact(lib);
}
