// SPDX-License-Identifier: MIT OR Apache-2.0
//! The transition events the allocator's hooks emit, and the slot they are emitted into.
//! Ports `orisnik`'s `letopis/event.rs`.
//!
//! An `Event` carries raw addresses: the hooks know nothing about normalization, which is
//! the replayer's job (`letopis_record.zig`). Every address is read with `@intFromPtr` for
//! its value only, never turned back into a pointer.
//!
//! # How events reach the replayer
//! `Buckets(config)` and `Tree(config)` each own a `Tap` when `config.trace` is set (a
//! `void` field otherwise, and every `if (config.trace)` emission is eliminated). A tap
//! holds either nothing (every emission is dropped) or a pointer to an `EventLog`, which
//! only `Orisnitsa.setLetopis` installs — and only the replayer calls that, on an instance
//! it owns, uninstalling it before the instance is torn down.

const std = @import("std");
const rbtree = @import("rbtree.zig");

/// Which sub-allocator mapped memory: the `b`/`t` of a record's `map` event.
pub const MapKind = enum { bucket, tree };

/// A page-list event's operands.
pub const PageEvent = struct {
    /// The bucket index.
    bucket: usize,
    /// Any address inside the page (its `Page` footer).
    page: usize,
};

/// A free-list event's operands.
pub const BlockEvent = struct {
    /// The block header's address.
    block: usize,
    /// The block's payload size.
    size: usize,
};

/// One state transition, as the allocator performed it. Each member is one event line of
/// the transition record (`examples/traces/GRAMMAR.md` §2.3); `examples/traces/EVENTS.md`
/// lists where each is emitted. Mirrors `orisnik`'s `Event` member for member.
pub const Event = union(enum) {
    /// Memory was mapped from the OS.
    map: struct { kind: MapKind, base: usize, bytes: usize },
    /// A mapping was returned to the OS.
    unmap: struct { base: usize, bytes: usize },
    /// A fresh page entered a bucket's page list (`page+`).
    page_spawn: PageEvent,
    /// An empty page left a bucket's page list (`page-`).
    page_release: PageEvent,
    /// A page became full and moved to the back of its list (`page-full`).
    page_full: PageEvent,
    /// A full page got a slot back and moved to the front of its list (`page-refill`).
    page_refill: PageEvent,
    /// The block at `block` was cut to `size` payload bytes (`split`).
    split: BlockEvent,
    /// The block at `block` moved `offset` bytes forward (`shift`).
    shift: struct { block: usize, offset: usize },
    /// The block whose header is at this address was absorbed into its physical
    /// predecessor (`merge`).
    merge: usize,
    /// A free block entered the red-black tree (`tree+`).
    tree_insert: struct { block: usize, size: usize, kind: rbtree.InsertKind, rotations: u32 },
    /// A free block left the red-black tree (`tree-`).
    tree_erase: struct { block: usize, size: usize, kind: rbtree.EraseKind, rotations: u32 },
    /// A free block entered the small free list (`list+`).
    list_push: BlockEvent,
    /// A free block left the small free list (`list-`).
    list_erase: BlockEvent,
    /// The most-recently-freed cache now holds this block, or nothing (`mr`).
    mr: ?usize,
};

/// The events one traced instance has emitted, in order. Appending allocates from `gpa`
/// (never from the traced instance); a failed append is remembered in `failed` rather
/// than reported from inside a hook, which has no way to fail.
pub const EventLog = struct {
    /// Backs `events`.
    gpa: std.mem.Allocator,
    /// Appended by `Tap.emit`, taken by the replayer after each operation.
    events: std.ArrayList(Event) = .empty,
    /// Set if an append ran out of memory; the replayer then fails with `error.OutOfMemory`.
    failed: bool = false,

    /// An empty log allocating from `gpa`.
    pub fn init(gpa: std.mem.Allocator) EventLog {
        return .{ .gpa = gpa };
    }

    /// Releases the log's storage.
    pub fn deinit(self: *EventLog) void {
        self.events.deinit(self.gpa);
    }

    fn append(self: *EventLog, event: Event) void {
        self.events.append(self.gpa, event) catch {
            self.failed = true;
        };
    }
};

/// Where a sub-allocator emits its events: empty by default, pointed at an `EventLog` only
/// while a replay runs. Parity: `orisnik`'s `Tap`.
pub const Tap = struct {
    /// The installed log, if any.
    log: ?*EventLog = null,

    /// Appends `event` to the installed log, if any.
    pub fn emit(self: *const Tap, event: Event) void {
        if (self.log) |log| log.append(event);
    }
};
