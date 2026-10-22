// SPDX-License-Identifier: MIT OR Apache-2.0
//! The allocators a replay can run through, behind one interface.
//!
//! `orisnik` is driven through its own API, so every trace operation means exactly what it
//! means to the transition record. Every other allocator is a `GlobalAlloc` called directly
//! (never installed as this process's global allocator), which has no counterpart for three
//! operations: `resize` reports the current size without changing anything, `size` returns
//! the size the replay tracks, and `purge` does nothing. A plain allocation asks for
//! alignment 8, `orisnik`'s default, so every allocator answers the same request.

use crate::trace::Slot;
use orisnik::Orisnik;
use std::alloc::{GlobalAlloc, Layout, System};

/// One allocator under test. `align` 0 means the default (8).
pub trait Backend {
    /// # Safety
    /// As the allocator's own `alloc`.
    unsafe fn alloc(&self, size: usize, align: usize) -> *mut u8;
    /// # Safety
    /// As the allocator's own `calloc`.
    unsafe fn calloc(&self, count: usize, size: usize) -> *mut u8;
    /// Reallocates `old` (possibly null) to `size` bytes at `align`; size 0 frees.
    ///
    /// # Safety
    /// `old` must be a live block of this backend, or null.
    unsafe fn realloc(&self, old: Slot, size: usize, align: usize) -> *mut u8;
    /// # Safety
    /// `slot` must be a live block of this backend, or null.
    unsafe fn resize(&self, slot: Slot, size: usize) -> usize;
    /// # Safety
    /// As `resize`.
    unsafe fn size(&self, slot: Slot) -> usize;
    /// # Safety
    /// `slot` must be a live block of this backend, or null; it is not used again.
    unsafe fn free(&self, slot: Slot, sized: bool);
    fn purge(&self);
    /// Bytes mapped from the OS, for an allocator that knows (`orisnik`).
    fn mapped(&self) -> Option<u64> {
        None
    }
}

/// Every allocator this build can run.
pub const NAMES: &[&str] = &[
    "orisnik",
    "system",
    #[cfg(feature = "mimalloc")]
    "mimalloc",
    #[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
    "jemalloc",
    #[cfg(feature = "snmalloc")]
    "snmalloc",
];

/// Runs `f` with the named backend, or returns `None` for an unknown name.
pub fn with_backend<R>(name: &str, f: impl FnOnce(&dyn Backend) -> R) -> Option<R> {
    match name {
        "orisnik" => {
            // Boxed: an `Orisnik` must not move after first use.
            let oris = Box::new(Orisnik::new());
            Some(f(&OrisBackend(&oris)))
        }
        "system" => Some(f(&Global(System))),
        #[cfg(feature = "mimalloc")]
        "mimalloc" => Some(f(&Global(mimalloc::MiMalloc))),
        #[cfg(all(feature = "jemalloc", not(target_env = "msvc")))]
        "jemalloc" => Some(f(&Global(tikv_jemallocator::Jemalloc))),
        #[cfg(feature = "snmalloc")]
        "snmalloc" => Some(f(&Global(snmalloc_rs::SnMalloc))),
        _ => None,
    }
}

fn nn(p: *mut u8) -> Option<std::ptr::NonNull<u8>> {
    std::ptr::NonNull::new(p)
}

fn raw(p: Option<std::ptr::NonNull<u8>>) -> *mut u8 {
    p.map_or(std::ptr::null_mut(), std::ptr::NonNull::as_ptr)
}

struct OrisBackend<'a>(&'a Orisnik);

impl Backend for OrisBackend<'_> {
    unsafe fn alloc(&self, size: usize, align: usize) -> *mut u8 {
        if align == 0 {
            raw(self.0.alloc(size))
        } else {
            raw(self.0.alloc_aligned(size, align))
        }
    }
    unsafe fn calloc(&self, count: usize, size: usize) -> *mut u8 {
        raw(self.0.calloc(count, size))
    }
    unsafe fn realloc(&self, old: Slot, size: usize, align: usize) -> *mut u8 {
        // SAFETY: forwarded.
        unsafe {
            if align == 0 {
                raw(self.0.realloc(nn(old.ptr), size))
            } else {
                raw(self.0.realloc_aligned(nn(old.ptr), size, align))
            }
        }
    }
    unsafe fn resize(&self, slot: Slot, size: usize) -> usize {
        // SAFETY: forwarded.
        unsafe { self.0.resize(nn(slot.ptr), size) }
    }
    unsafe fn size(&self, slot: Slot) -> usize {
        // SAFETY: forwarded.
        unsafe { self.0.size(nn(slot.ptr)) }
    }
    unsafe fn free(&self, slot: Slot, sized: bool) {
        // SAFETY: forwarded.
        unsafe {
            match (sized, slot.align) {
                (false, _) => self.0.free(nn(slot.ptr)),
                (true, 0..=8) => self.0.free_with_size(nn(slot.ptr), slot.size),
                (true, align) => self
                    .0
                    .free_with_size_aligned(nn(slot.ptr), slot.size, align),
            }
        }
    }
    fn purge(&self) {
        self.0.purge();
    }
    fn mapped(&self) -> Option<u64> {
        Some(self.0.allocated() as u64)
    }
}

struct Global<A: GlobalAlloc>(A);

/// The layout a block was allocated with: at least one byte, alignment at least 8.
fn layout(size: usize, align: usize) -> Layout {
    Layout::from_size_align(size.max(1), align.max(8)).expect("valid layout")
}

impl<A: GlobalAlloc> Backend for Global<A> {
    unsafe fn alloc(&self, size: usize, align: usize) -> *mut u8 {
        if size == 0 {
            return std::ptr::null_mut(); // as `orisnik` (and HPHA) answer alloc(0)
        }
        // SAFETY: the layout has a nonzero size.
        unsafe { self.0.alloc(layout(size, align)) }
    }
    unsafe fn calloc(&self, count: usize, size: usize) -> *mut u8 {
        if count * size == 0 {
            return std::ptr::null_mut();
        }
        // SAFETY: as above.
        unsafe { self.0.alloc_zeroed(layout(count * size, 0)) }
    }
    unsafe fn realloc(&self, old: Slot, size: usize, align: usize) -> *mut u8 {
        // SAFETY (every call): `old` is live with the layout it was allocated with.
        unsafe {
            if old.ptr.is_null() {
                return self.alloc(size, align);
            }
            if size == 0 {
                self.0.dealloc(old.ptr, layout(old.size, old.align));
                return std::ptr::null_mut();
            }
            if align.max(8) == old.align.max(8) {
                return self.0.realloc(old.ptr, layout(old.size, old.align), size);
            }
            // A change of alignment: `GlobalAlloc::realloc` keeps the old one.
            let new = self.0.alloc(layout(size, align));
            if !new.is_null() {
                std::ptr::copy_nonoverlapping(old.ptr, new, old.size.min(size));
                self.0.dealloc(old.ptr, layout(old.size, old.align));
            }
            new
        }
    }
    unsafe fn resize(&self, slot: Slot, _size: usize) -> usize {
        slot.size
    }
    unsafe fn size(&self, slot: Slot) -> usize {
        slot.size
    }
    unsafe fn free(&self, slot: Slot, _sized: bool) {
        if !slot.ptr.is_null() {
            // SAFETY: live, with the layout it was allocated (or last reallocated) with.
            unsafe { self.0.dealloc(slot.ptr, layout(slot.size, slot.align)) };
        }
    }
    fn purge(&self) {}
}
