// SPDX-License-Identifier: MIT OR Apache-2.0
//! `oris_*` — the C-ABI surface. Every function takes an explicit `*mut Orisnik`
//! handle, mirroring HPHA's own instantiable `class allocator` rather than a hidden
//! global singleton (`BRIEF.md`'s explicit-opt-in stance) — a C caller creates one
//! with [`oris_new`], threads the handle through every other call, and destroys it
//! with [`oris_destroy`] when done. Naming and behaviour otherwise mirror
//! `allocator`'s own public methods one-to-one, `*mut u8`/null in place of
//! `Option<NonNull<u8>>`.
//!
//! `#[unsafe(no_mangle)]` (edition 2024's unsafe-attribute syntax, `Rust/CONVENTIONS.md`'s
//! MSRV lint guard note) keeps every symbol name stable for C linkage.

use crate::orisnik::Orisnik;
use core::ptr::NonNull;

/// Creates a fresh allocator instance on the heap, returning an opaque owning
/// handle. Pair with [`oris_destroy`]. Never null — allocating the handle itself
/// uses `Box::new`, which aborts on OS memory exhaustion rather than returning an
/// error (Rust has no stable fallible-`Box` API without the `allocator_api`
/// feature); this is a property of the handle's own storage, unrelated to the
/// `Orisnik` instance's own allocation paths, which do return null on failure.
#[must_use]
#[unsafe(no_mangle)]
pub extern "C" fn oris_new() -> *mut Orisnik {
    Box::into_raw(Box::new(Orisnik::new()))
}

/// Destroys an allocator instance created by [`oris_new`].
///
/// # Safety
/// `handle` must be a still-live result of [`oris_new`] (or null, in which case this
/// is a no-op), not yet destroyed, and not used again after this call — by this
/// function or any other `oris_*` call. Every allocation made through `handle`
/// should already be freed or intentionally leaked first: destroying the instance
/// does not return its outstanding OS pages/arenas (matching HPHA, which never
/// returns memory to the OS except via an explicit `purge()`) — call
/// [`oris_purge`] beforehand if reclaiming that memory matters.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_destroy(handle: *mut Orisnik) {
    let Some(handle) = NonNull::new(handle) else {
        return;
    };
    // SAFETY: `handle` is a still-live `Box::into_raw` result from `oris_new`, not
    // used again after this call (this function's own contract).
    drop(unsafe { Box::from_raw(handle.as_ptr()) });
}

/// Allocates `size` bytes at the allocator's default alignment. `size == 0` returns
/// null. Ports `allocator::alloc(size_t)`.
///
/// # Safety
/// `handle` must be live (a still-live result of [`oris_new`], not yet destroyed).
#[must_use]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_alloc(handle: *mut Orisnik, size: usize) -> *mut u8 {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    orisnik
        .alloc(size)
        .map_or(core::ptr::null_mut(), NonNull::as_ptr)
}

/// Allocates `size` bytes aligned to `alignment`. `size == 0` returns null. Ports
/// `allocator::alloc(size_t, size_t)`.
///
/// # Safety
/// `handle` must be live.
#[must_use]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_alloc_aligned(
    handle: *mut Orisnik,
    size: usize,
    alignment: usize,
) -> *mut u8 {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    orisnik
        .alloc_aligned(size, alignment)
        .map_or(core::ptr::null_mut(), NonNull::as_ptr)
}

/// Allocates `count * size` bytes at the default alignment, zeroed. Ports
/// `allocator::calloc`.
///
/// # Safety
/// `handle` must be live.
#[must_use]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_calloc(handle: *mut Orisnik, count: usize, size: usize) -> *mut u8 {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    orisnik
        .calloc(count, size)
        .map_or(core::ptr::null_mut(), NonNull::as_ptr)
}

/// Grows, shrinks, or moves `ptr` to `size` bytes at the default alignment. `ptr ==
/// null` acts as [`oris_alloc`]; `size == 0` acts as [`oris_free`] and returns null.
/// Ports `allocator::realloc(void*, size_t)`.
///
/// # Safety
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
#[must_use]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_realloc(handle: *mut Orisnik, ptr: *mut u8, size: usize) -> *mut u8 {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    // SAFETY: `ptr`, if non-null, is a still-live allocation `orisnik` produced
    // (this function's own contract).
    unsafe { orisnik.realloc(NonNull::new(ptr), size) }
        .map_or(core::ptr::null_mut(), NonNull::as_ptr)
}

/// Grows, shrinks, or moves `ptr` to `size` bytes aligned to `alignment`. `ptr ==
/// null` acts as [`oris_alloc_aligned`]; `size == 0` acts as [`oris_free`] and
/// returns null. Ports `allocator::realloc(void*, size_t, size_t)`.
///
/// # Safety
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
#[must_use]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_realloc_aligned(
    handle: *mut Orisnik,
    ptr: *mut u8,
    size: usize,
    alignment: usize,
) -> *mut u8 {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    // SAFETY: `ptr`, if non-null, is a still-live allocation `orisnik` produced
    // (this function's own contract).
    unsafe { orisnik.realloc_aligned(NonNull::new(ptr), size, alignment) }
        .map_or(core::ptr::null_mut(), NonNull::as_ptr)
}

/// Grows or shrinks `ptr` in place to the extent possible, returning the resulting
/// size. `ptr == null` returns 0. Ports `allocator::resize`.
///
/// # Safety
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
#[must_use]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_resize(handle: *mut Orisnik, ptr: *mut u8, size: usize) -> usize {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    // SAFETY: `ptr`, if non-null, is a still-live allocation `orisnik` produced
    // (this function's own contract).
    unsafe { orisnik.resize(NonNull::new(ptr), size) }
}

/// Queries the usable size of `ptr`'s allocation. `ptr == null` returns 0. Ports
/// `allocator::size`.
///
/// # Safety
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
#[must_use]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_size(handle: *mut Orisnik, ptr: *mut u8) -> usize {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    // SAFETY: `ptr`, if non-null, is a still-live allocation `orisnik` produced
    // (this function's own contract).
    unsafe { orisnik.size(NonNull::new(ptr)) }
}

/// Frees `ptr`. `ptr == null` is a no-op. Ports `allocator::free(void*)`.
///
/// # Safety
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_free(handle: *mut Orisnik, ptr: *mut u8) {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    // SAFETY: `ptr`, if non-null, is a still-live allocation `orisnik` produced
    // (this function's own contract).
    unsafe { orisnik.free(NonNull::new(ptr)) };
}

/// Frees `ptr`, given its original request size at the default alignment. `ptr ==
/// null` is a no-op. Ports `allocator::free(void*, size_t)`.
///
/// `orig_size` must be `ptr`'s size **at the moment it was allocated**, not a size
/// from any later [`oris_realloc`]/[`oris_resize`] call — see
/// [`Orisnik::free_with_size`]'s own doc for why. Prefer [`oris_free`] whenever
/// `ptr`'s allocation history isn't certain to be realloc-free.
///
/// # Safety
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced with `orig_size` at the default alignment.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_free_with_size(handle: *mut Orisnik, ptr: *mut u8, orig_size: usize) {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    // SAFETY: `ptr`, if non-null, is a still-live allocation `orisnik` produced
    // with `orig_size` (this function's own contract).
    unsafe { orisnik.free_with_size(NonNull::new(ptr), orig_size) };
}

/// Frees `ptr`, given its original request size and alignment. `ptr == null` is a
/// no-op. Ports `allocator::free(void*, size_t, size_t)`.
///
/// `orig_size`/`old_alignment` must be `ptr`'s size/alignment **at the moment it was
/// allocated** — see [`oris_free_with_size`]'s doc for why. Prefer [`oris_free`]
/// whenever `ptr`'s allocation history isn't certain to be realloc-free.
///
/// # Safety
/// `handle` must be live. `ptr`, if non-null, must be a still-live allocation
/// `handle` produced with `orig_size`/`old_alignment`.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_free_with_size_aligned(
    handle: *mut Orisnik,
    ptr: *mut u8,
    orig_size: usize,
    old_alignment: usize,
) {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    // SAFETY: `ptr`, if non-null, is a still-live allocation `orisnik` produced
    // with `orig_size`/`old_alignment` (this function's own contract).
    unsafe { orisnik.free_with_size_aligned(NonNull::new(ptr), orig_size, old_alignment) };
}

/// Returns every fully-unused page/arena to the OS. Ports `allocator::purge`.
///
/// # Safety
/// `handle` must be live.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_purge(handle: *mut Orisnik) {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    orisnik.purge();
}

/// Total bytes currently claimed from the OS across both allocation paths. Ports
/// `allocator::allocated`.
///
/// # Safety
/// `handle` must be live.
#[must_use]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn oris_allocated(handle: *mut Orisnik) -> usize {
    // SAFETY: `handle` is live (this function's own contract).
    let orisnik = unsafe { &*handle };
    orisnik.allocated()
}

#[cfg(test)]
mod tests {
    use super::*;

    // Every allocating call below reaches real `os::map` through a freshly
    // `oris_new`-created handle (see `orisnik.rs`'s test module doc for why: no
    // OS-free seeding seam exists at this layer). Miri-ignored for the same reason
    // as `orisnik.rs`'s own OS-touching tests.

    #[test]
    #[cfg_attr(miri, ignore)]
    fn c_abi_round_trip_alloc_realloc_free_purge() {
        let handle = oris_new();
        assert!(!handle.is_null());

        // SAFETY: `handle` is live.
        let ptr = unsafe { oris_alloc(handle, 64) };
        assert!(!ptr.is_null());
        // SAFETY: `ptr` is a live allocation of at least 64 bytes.
        unsafe { ptr.write_bytes(0xAB, 64) };

        // SAFETY: `handle` is live; `ptr` is a live allocation `handle` produced.
        assert_eq!(unsafe { oris_size(handle, ptr) }, 64);

        // SAFETY: `handle` is live; `ptr` is a live allocation `handle` produced.
        let grown = unsafe { oris_realloc(handle, ptr, 512) };
        assert!(!grown.is_null());
        // SAFETY: the first 64 bytes must have been preserved across the realloc.
        let preserved = unsafe { core::slice::from_raw_parts(grown, 64) };
        assert!(preserved.iter().all(|&b| b == 0xAB));

        // SAFETY: `handle` is live.
        assert!(unsafe { oris_allocated(handle) } > 0);

        // SAFETY: `handle` is live; `grown` is a live allocation `handle` produced.
        unsafe { oris_free(handle, grown) };
        // SAFETY: `handle` is live.
        unsafe { oris_purge(handle) };
        // SAFETY: `handle` is live.
        assert_eq!(unsafe { oris_allocated(handle) }, 0);

        // SAFETY: `handle` is a still-live, not-yet-destroyed `oris_new` result, not
        // used again after this call.
        unsafe { oris_destroy(handle) };
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn c_abi_aligned_alloc_and_free_with_size() {
        let handle = oris_new();

        // SAFETY: `handle` is live.
        let ptr = unsafe { oris_alloc_aligned(handle, 48, 128) };
        assert!(!ptr.is_null());
        assert_eq!(ptr.addr() % 128, 0);
        // SAFETY: `handle` is live; `ptr` is a live allocation `handle` produced
        // with 48 bytes at alignment 128.
        unsafe { oris_free_with_size_aligned(handle, ptr, 48, 128) };

        // SAFETY: `handle` is live.
        let calloc_ptr = unsafe { oris_calloc(handle, 4, 16) };
        assert!(!calloc_ptr.is_null());
        // SAFETY: `calloc_ptr` is a live allocation of at least 64 bytes, zeroed by
        // `oris_calloc`.
        let zeroed = unsafe { core::slice::from_raw_parts(calloc_ptr, 64) };
        assert!(zeroed.iter().all(|&b| b == 0));
        // SAFETY: `handle` is live; `calloc_ptr` is a live allocation `handle`
        // produced with 64 bytes at the default alignment.
        unsafe { oris_free_with_size(handle, calloc_ptr, 64) };

        // SAFETY: `handle` is a still-live, not-yet-destroyed `oris_new` result.
        unsafe { oris_destroy(handle) };
    }

    #[test]
    fn oris_destroy_on_null_handle_is_a_no_op() {
        // SAFETY: null trivially satisfies `oris_destroy`'s "or null" contract.
        unsafe { oris_destroy(core::ptr::null_mut()) };
    }
}
