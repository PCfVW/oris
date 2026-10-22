// SPDX-License-Identifier: MIT OR Apache-2.0
//! `LD_PRELOAD` shim: the C allocation API over one process-wide `orisnik` instance, so that
//! mimalloc-bench can run its programs on Oris (allocator name `onik`). Linux only.
//!
//! What the shim adds to the allocator, and why — each is stated next to every result:
//!
//! - **One global lock.** Oris is single-threaded (multithreaded mode is v2.x on the
//!   roadmap); a program that allocates from several threads gets every call serialized
//!   behind one `pthread_mutex`. Multithreaded benchmarks therefore measure Oris *plus a
//!   lock*, and say so.
//! - **16-byte alignment.** `malloc` must return memory aligned for any fundamental type,
//!   16 bytes on x86-64; Oris's default is 8 (HPHA's `DEFAULT_ALIGNMENT`). Every request is
//!   made with `alloc_aligned(round_up(size, 16), 16)`, which lands small requests in a
//!   16-multiple size class — so a bucket slot is always 16-aligned.
//! - **`malloc(0)` returns a unique pointer** (a 16-byte block), as glibc's does; Oris's own
//!   `alloc(0)` returns null.
//! - **`fork` keeps the lock consistent** (`pthread_atfork`).
//!
//! Nothing here allocates through the C heap: `orisnik` maps its pages with `mmap`.

#![allow(clippy::missing_safety_doc)]

use core::ffi::{c_int, c_void};
use core::ptr::{self, NonNull};
use orisnik::Orisnik;

static ORIS: Orisnik = Orisnik::new();
static mut LOCK: libc::pthread_mutex_t = libc::PTHREAD_MUTEX_INITIALIZER;

const MIN_ALIGN: usize = 16;

/// Holds the global lock for its lifetime.
struct Guard;

impl Guard {
    fn new() -> Self {
        // SAFETY: a statically initialized mutex, never destroyed.
        unsafe { libc::pthread_mutex_lock(&raw mut LOCK) };
        Guard
    }
}

impl Drop for Guard {
    fn drop(&mut self) {
        // SAFETY: locked by this guard's `new`.
        unsafe { libc::pthread_mutex_unlock(&raw mut LOCK) };
    }
}

extern "C" fn lock_for_fork() {
    // SAFETY: as in `Guard::new`.
    unsafe { libc::pthread_mutex_lock(&raw mut LOCK) };
}

extern "C" fn unlock_after_fork() {
    // SAFETY: locked by `lock_for_fork`, in this process (parent) or its copy (child).
    unsafe { libc::pthread_mutex_unlock(&raw mut LOCK) };
}

extern "C" fn register_fork_handlers() {
    // SAFETY: plain function pointers with the signature pthread_atfork expects.
    unsafe { libc::pthread_atfork(Some(lock_for_fork), Some(unlock_after_fork), Some(unlock_after_fork)) };
}

/// Runs `register_fork_handlers` when the library is loaded.
#[used]
#[unsafe(link_section = ".init_array")]
static INIT: extern "C" fn() = register_fork_handlers;

fn round_up(size: usize, align: usize) -> Option<usize> {
    size.max(1).checked_add(align - 1).map(|s| s & !(align - 1))
}

fn out(p: Option<NonNull<u8>>) -> *mut c_void {
    p.map_or(ptr::null_mut(), |p| p.as_ptr().cast())
}

fn nn(p: *mut c_void) -> Option<NonNull<u8>> {
    NonNull::new(p.cast())
}

fn aligned(size: usize, align: usize) -> *mut c_void {
    let align = align.max(MIN_ALIGN);
    let Some(size) = round_up(size, MIN_ALIGN) else {
        return ptr::null_mut();
    };
    let _g = Guard::new();
    out(ORIS.alloc_aligned(size, align))
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn malloc(size: usize) -> *mut c_void {
    aligned(size, MIN_ALIGN)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn calloc(count: usize, size: usize) -> *mut c_void {
    let Some(total) = count.checked_mul(size) else {
        return ptr::null_mut();
    };
    let p = aligned(total, MIN_ALIGN);
    if !p.is_null() {
        // SAFETY: a fresh block of at least `total` bytes.
        unsafe { ptr::write_bytes(p.cast::<u8>(), 0, total) };
    }
    p
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn realloc(p: *mut c_void, size: usize) -> *mut c_void {
    if p.is_null() {
        return aligned(size, MIN_ALIGN);
    }
    if size == 0 {
        // SAFETY: forwarded: `p` is a live block of this allocator.
        unsafe { free(p) };
        return ptr::null_mut();
    }
    let Some(size) = round_up(size, MIN_ALIGN) else {
        return ptr::null_mut();
    };
    let _g = Guard::new();
    // SAFETY: `p` is a live, 16-aligned block of `ORIS` (the caller's contract with realloc).
    out(unsafe { ORIS.realloc_aligned(nn(p), size, MIN_ALIGN) })
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn free(p: *mut c_void) {
    if p.is_null() {
        return;
    }
    let _g = Guard::new();
    // SAFETY: `p` is a live block of `ORIS` (the caller's contract with free).
    unsafe { ORIS.free(nn(p)) };
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn posix_memalign(out_ptr: *mut *mut c_void, align: usize, size: usize) -> c_int {
    if !align.is_power_of_two() || align % size_of::<*mut c_void>() != 0 {
        return libc::EINVAL;
    }
    let p = aligned(size, align);
    if p.is_null() {
        return libc::ENOMEM;
    }
    // SAFETY: the caller provides a valid out-parameter.
    unsafe { out_ptr.write(p) };
    0
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn aligned_alloc(align: usize, size: usize) -> *mut c_void {
    if !align.is_power_of_two() {
        return ptr::null_mut();
    }
    aligned(size, align)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn memalign(align: usize, size: usize) -> *mut c_void {
    if !align.is_power_of_two() {
        return ptr::null_mut();
    }
    aligned(size, align)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn valloc(size: usize) -> *mut c_void {
    aligned(size, 4096)
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn pvalloc(size: usize) -> *mut c_void {
    match round_up(size, 4096) {
        Some(size) => aligned(size, 4096),
        None => ptr::null_mut(),
    }
}

#[unsafe(no_mangle)]
pub unsafe extern "C" fn malloc_usable_size(p: *mut c_void) -> usize {
    let _g = Guard::new();
    // SAFETY: `p` is a live block of `ORIS`, or null.
    unsafe { ORIS.size(nn(p)) }
}
