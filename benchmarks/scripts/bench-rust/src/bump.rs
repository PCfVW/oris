// SPDX-License-Identifier: MIT OR Apache-2.0
//! The harness's own allocator: a bump allocator over memory mapped straight from the OS,
//! which never frees.
//!
//! The memory pass measures how much the resident set grows while an allocator replays a
//! trace. That only means something if the allocator under test starts from nothing — but
//! the harness itself allocates (the trace text, the operation array), and if it did so
//! through the C heap, the `system` backend would find those pages already resident and
//! reuse them after the parse, appearing to need almost no memory. So the harness allocates
//! from here instead: chunks mapped directly from the OS, handed out in order and never
//! returned, untouchable by any allocator under test. Single-threaded, like the harness.

use std::alloc::{GlobalAlloc, Layout};
use std::cell::Cell;

const CHUNK: usize = 64 << 20;

pub struct Bump {
    next: Cell<usize>,
    end: Cell<usize>,
}

// SAFETY: the harness is single-threaded (it never spawns a thread).
unsafe impl Sync for Bump {}

impl Bump {
    pub const fn new() -> Self {
        Self {
            next: Cell::new(0),
            end: Cell::new(0),
        }
    }
}

unsafe impl GlobalAlloc for Bump {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let align = layout.align();
        let mut start = (self.next.get() + align - 1) & !(align - 1);
        if self.next.get() == 0 || start + layout.size() > self.end.get() {
            let len = layout.size().max(CHUNK).next_multiple_of(4096) + align;
            let base = os_map(len);
            if base.is_null() {
                return std::ptr::null_mut();
            }
            self.next.set(base as usize);
            self.end.set(base as usize + len);
            start = (base as usize + align - 1) & !(align - 1);
        }
        self.next.set(start + layout.size());
        start as *mut u8
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        // Growing the most recent block in place is the common case (a Vec being filled).
        if ptr as usize + layout.size() == self.next.get()
            && ptr as usize + new_size <= self.end.get()
        {
            self.next.set(ptr as usize + new_size);
            return ptr;
        }
        // SAFETY: `new_size` is nonzero (GlobalAlloc's contract), the alignment unchanged.
        let new =
            unsafe { self.alloc(Layout::from_size_align_unchecked(new_size, layout.align())) };
        if !new.is_null() {
            // SAFETY: both blocks are valid for the smaller size and do not overlap.
            unsafe { std::ptr::copy_nonoverlapping(ptr, new, layout.size().min(new_size)) };
        }
        new
    }
}

#[cfg(windows)]
fn os_map(len: usize) -> *mut u8 {
    use windows_sys::Win32::System::Memory::{
        MEM_COMMIT, MEM_RESERVE, PAGE_READWRITE, VirtualAlloc,
    };
    // SAFETY: a fresh anonymous reservation; null on failure.
    unsafe {
        VirtualAlloc(
            std::ptr::null(),
            len,
            MEM_COMMIT | MEM_RESERVE,
            PAGE_READWRITE,
        )
        .cast()
    }
}

#[cfg(unix)]
fn os_map(len: usize) -> *mut u8 {
    // SAFETY: a fresh anonymous private mapping; MAP_FAILED on failure.
    let p = unsafe {
        libc::mmap(
            std::ptr::null_mut(),
            len,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANON,
            -1,
            0,
        )
    };
    if p == libc::MAP_FAILED {
        std::ptr::null_mut()
    } else {
        p.cast()
    }
}
