// SPDX-License-Identifier: MIT OR Apache-2.0
//! Cross-platform virtual-memory layer.
//!
//! Ports `Cpp/hpha.h`'s `virtual_alloc`/`virtual_free` and `VIRTUAL_PAGE_SIZE`. HPHA is
//! Win32-only (`VirtualAlloc`); this module abstracts the same "get `PAGE_SIZE`-aligned
//! pages from the OS, return them only on `purge`" contract over Windows
//! (`VirtualAlloc`/`VirtualFree`) and Unix (`mmap`/`munmap`).
//!
//! [`PAGE_SIZE`] is fixed at 64 KiB on **every** platform — not each OS's native page
//! size — because the bucket and tree allocators' page-count and split/coalesce math
//! must be identical across OSes for the cross-port invariant (`ROADMAP.md`) to hold
//! even within one language. On Windows this matches the OS's own 64 KiB "allocation
//! granularity" for free (`VirtualAlloc` addresses are naturally aligned to it). On
//! Unix, `mmap` only guarantees native-page alignment (4 KiB, or 16 KiB on Apple
//! Silicon) — [`map`]'s Unix implementation over-allocates and trims to reach 64 KiB,
//! the same technique jemalloc/mimalloc use for chunk alignment on POSIX.

use core::ptr::NonNull;

/// The page size every allocator subsystem grows by, in bytes. Fixed across all
/// platforms — see the module doc.
pub(crate) const PAGE_SIZE: usize = 1 << 16; // 64 KiB, matches HPHA's VIRTUAL_PAGE_SIZE_LOG2

/// Requests `size` bytes from the OS, aligned to [`PAGE_SIZE`].
///
/// `size` must be a non-zero multiple of [`PAGE_SIZE`]. Returns `None` on OS failure
/// (out of address space / memory pressure) — allocation failure is a value, not a
/// panic, per `Rust/CONVENTIONS.md`.
#[must_use]
pub(crate) fn map(size: usize) -> Option<NonNull<u8>> {
    debug_assert!(size > 0 && size % PAGE_SIZE == 0);
    #[cfg(test)]
    {
        if test_vm::should_fail() {
            return None;
        }
        if test_vm::ACTIVE {
            return test_vm::map(size);
        }
    }
    imp::map(size)
}

/// Returns memory previously obtained from [`map`] back to the OS.
///
/// # Safety
/// - `ptr` must have been returned by a prior call to [`map`] on this platform and not
///   already unmapped.
/// - `size` must be the exact size passed to that `map` call.
pub(crate) unsafe fn unmap(ptr: NonNull<u8>, size: usize) {
    debug_assert!(size > 0 && size % PAGE_SIZE == 0);
    #[cfg(test)]
    if test_vm::ACTIVE {
        // SAFETY: forwarded; under `ACTIVE` every live mapping came from
        // `test_vm::map`, so this is the matching deallocation.
        unsafe { test_vm::unmap(ptr, size) };
        return;
    }
    // SAFETY: forwarded verbatim; this function's own contract (documented above)
    // is exactly imp::unmap's contract.
    unsafe { imp::unmap(ptr, size) };
}

/// Test-only seams over the OS boundary: a heap-backed stand-in for the real VM, and
/// an out-of-memory injector. Compiled out entirely outside `cfg(test)`.
///
/// # Why a stand-in backend exists
/// Miri cannot interpret either platform's VM syscall (see this module's test-module
/// doc). Before v0.1.1 that meant **every test that actually allocated** — the whole
/// `Orisnik` dispatcher, the `oris_*` C-ABI, both idiomatic surfaces — was
/// `#[cfg_attr(miri, ignore)]`, so the crate's public surface never reached the
/// soundness gate; only `bucket.rs`/`tree.rs`, which had built their own
/// `FakePage`/`FakeArena` seams, did. [`ACTIVE`] generalizes those seams to the one
/// place they were always needed: `map`/`unmap` themselves.
///
/// The stand-in is used **only under Miri**. A native `cargo test` still exercises the
/// real `VirtualAlloc`/`mmap`, so this trades nothing away — it adds Miri coverage
/// where there was none, rather than replacing real-VM coverage.
#[cfg(test)]
pub(crate) mod test_vm {
    use super::PAGE_SIZE;
    use core::cell::Cell;
    use core::ptr::NonNull;

    /// Whether `map`/`unmap` use the heap-backed stand-in instead of the real syscall.
    /// True exactly under Miri — see this module's doc for why that is the right
    /// boundary rather than "always, in tests".
    pub(crate) const ACTIVE: bool = cfg!(miri);

    thread_local! {
        /// Successful [`super::map`] calls remaining before it starts returning
        /// `None`; `None` disables injection. Thread-local because `cargo test` runs
        /// tests in parallel and a process-global counter would let one test's
        /// injection starve another's allocations.
        static FAIL_AFTER: Cell<Option<usize>> = const { Cell::new(None) };
    }

    /// Makes the next `successes` calls to [`super::map`] succeed and every call after
    /// that fail, until [`clear_failure`]. The returned guard restores the previous
    /// setting on drop, so a panicking assertion cannot leak injection into the next
    /// test on this thread.
    #[must_use]
    pub(crate) fn fail_map_after(successes: usize) -> FailureGuard {
        FAIL_AFTER.with(|f| f.set(Some(successes)));
        FailureGuard
    }

    /// Disables out-of-memory injection on this thread.
    pub(crate) fn clear_failure() {
        FAIL_AFTER.with(|f| f.set(None));
    }

    /// Restores "no injection" when it goes out of scope.
    pub(crate) struct FailureGuard;

    impl Drop for FailureGuard {
        fn drop(&mut self) {
            clear_failure();
        }
    }

    /// Consumes one budgeted success, reporting whether this `map` call must fail.
    pub(crate) fn should_fail() -> bool {
        FAIL_AFTER.with(|f| match f.get() {
            None => false,
            Some(0) => true,
            Some(n) => {
                f.set(Some(n - 1));
                false
            }
        })
    }

    /// The heap-backed stand-in for a real mapping: `PAGE_SIZE`-aligned and zeroed,
    /// matching what `VirtualAlloc(MEM_COMMIT)` and `mmap(MAP_ANON)` both guarantee.
    #[must_use]
    pub(crate) fn map(size: usize) -> Option<NonNull<u8>> {
        let layout = std::alloc::Layout::from_size_align(size, PAGE_SIZE)
            .expect("size is a non-zero multiple of PAGE_SIZE, which is a power of two");
        // SAFETY: `layout` has a non-zero size (`map`'s own precondition, asserted by
        // its caller). `alloc_zeroed` matches the real mappings' zero-fill guarantee.
        let ptr = unsafe { std::alloc::alloc_zeroed(layout) };
        NonNull::new(ptr)
    }

    /// # Safety
    /// `ptr`/`size` must describe a still-live result of this module's own [`map`].
    pub(crate) unsafe fn unmap(ptr: NonNull<u8>, size: usize) {
        let layout = std::alloc::Layout::from_size_align(size, PAGE_SIZE)
            .expect("size matched a prior `map` call, so the layout is valid");
        // SAFETY: forwarded from this function's own contract — `ptr` came from
        // `alloc_zeroed` with exactly this layout and is not used again.
        unsafe { std::alloc::dealloc(ptr.as_ptr(), layout) };
    }
}

#[cfg(windows)]
mod imp {
    use super::PAGE_SIZE;
    use core::ffi::c_void;
    use core::ptr::NonNull;

    const MEM_COMMIT: u32 = 0x0000_1000;
    const MEM_RELEASE: u32 = 0x0000_8000;
    const PAGE_READWRITE: u32 = 0x04;

    #[link(name = "kernel32")]
    unsafe extern "system" {
        fn VirtualAlloc(
            lp_address: *mut c_void,
            dw_size: usize,
            fl_allocation_type: u32,
            fl_protect: u32,
        ) -> *mut c_void;
        fn VirtualFree(lp_address: *mut c_void, dw_size: usize, dw_free_type: u32) -> i32;
    }

    pub(super) fn map(size: usize) -> Option<NonNull<u8>> {
        // SAFETY: a null lpAddress lets the OS choose the base address; MEM_COMMIT |
        // PAGE_READWRITE requests a fresh, writable mapping of exactly `size` bytes.
        // VirtualAlloc returns null on failure and otherwise a pointer that aliases no
        // live Rust allocation (it is fresh OS-backed memory).
        let ptr = unsafe { VirtualAlloc(core::ptr::null_mut(), size, MEM_COMMIT, PAGE_READWRITE) };
        // VirtualAlloc's result is a raw byte-addressable region; `.cast` reinterprets
        // the pointee type without touching the address (no alignment change: `u8` has
        // the loosest possible alignment requirement, so no `// ALIGN:` is needed).
        let bytes = ptr.cast::<u8>();
        // Windows' allocation granularity is documented as 64 KiB, matching PAGE_SIZE;
        // this holds unconditionally (`assert!`, not `debug_assert!`) because a
        // misaligned page would silently corrupt every downstream bucket/tree offset.
        assert!(bytes.is_null() || bytes.addr() % PAGE_SIZE == 0);
        NonNull::new(bytes)
    }

    /// # Safety
    /// Same contract as [`super::unmap`] (this is its Windows implementation): `ptr`
    /// must be a still-live result of `map` above.
    pub(super) unsafe fn unmap(ptr: NonNull<u8>, _size: usize) {
        // SAFETY: caller guarantees ptr was returned by a prior VirtualAlloc call from
        // `map` above and not yet freed; VirtualFree with dwFreeType = MEM_RELEASE
        // requires dwSize == 0 and releases the entire original region, matching
        // HPHA's own `VirtualFree(addr, 0, MEM_RELEASE)` call.
        let ok = unsafe { VirtualFree(ptr.as_ptr().cast::<c_void>(), 0, MEM_RELEASE) };
        debug_assert!(ok != 0, "VirtualFree failed");
    }
}

#[cfg(unix)]
mod imp {
    use super::PAGE_SIZE;
    use crate::align::round_up;
    use core::ptr::NonNull;

    pub(super) fn map(size: usize) -> Option<NonNull<u8>> {
        // mmap only guarantees native-page alignment (4 KiB, or 16 KiB on Apple
        // Silicon); over-request by one PAGE_SIZE so there is always enough slack to
        // trim an aligned `size`-byte window out of the mapping.
        let request = size + PAGE_SIZE;
        // SAFETY: anonymous, private mapping; addr = null lets the kernel choose the
        // base address, fd = -1 and offset = 0 are the POSIX-required values for
        // MAP_ANON. Failure is reported as MAP_FAILED and checked below before any
        // use of `raw`, so no invalid pointer is ever read.
        let raw = unsafe {
            libc::mmap(
                core::ptr::null_mut(),
                request,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_PRIVATE | libc::MAP_ANON,
                -1,
                0,
            )
        };
        if raw == libc::MAP_FAILED {
            return None;
        }
        // mmap's result is a raw byte-addressable region; `.cast` reinterprets the
        // pointee type without touching the address (no alignment change: `u8` has the
        // loosest possible alignment requirement, so no `// ALIGN:` is needed here).
        let base = raw.cast::<u8>();
        // PROVENANCE: `aligned` and every sub-range munmap'd below are address-only
        // views into this single mmap'd region; map_addr keeps `base`'s provenance
        // through the alignment step (no pointer here is ever formed via `as usize`).
        // ALIGN: round the mapping's base address up to PAGE_SIZE — mmap only
        // guarantees native-page alignment, not PAGE_SIZE (64 KiB) alignment.
        let aligned = base.map_addr(|addr| round_up(addr, PAGE_SIZE));

        let head_len = aligned.addr() - base.addr();
        if head_len > 0 {
            // SAFETY: `aligned` is within [base, base + request) since request has a
            // full PAGE_SIZE of slack over `size`, so head_len is in [0, PAGE_SIZE) and
            // [base, base + head_len) is a strict, still-mapped prefix of the mmap'd
            // region — trimming it does not touch [aligned, aligned + size).
            unsafe { libc::munmap(base.cast::<core::ffi::c_void>(), head_len) };
        }
        let tail_len = request - head_len - size;
        if tail_len > 0 {
            // ALIGN: `aligned + size` is the end of the window being returned to the
            // caller; everything after it up to the mapping's end is unused slack.
            let tail = aligned.map_addr(|addr| addr + size);
            // SAFETY: aligned's address + size + tail_len == base's address + request
            // (the full mapped length), so [tail, tail + tail_len) is a strict,
            // still-mapped suffix of the mmap'd region, disjoint from
            // [aligned, aligned + size).
            unsafe { libc::munmap(tail.cast::<core::ffi::c_void>(), tail_len) };
        }
        NonNull::new(aligned)
    }

    /// # Safety
    /// Same contract as [`super::unmap`] (this is its Unix implementation): `ptr`/`size`
    /// must describe a still-live result of `map` above.
    pub(super) unsafe fn unmap(ptr: NonNull<u8>, size: usize) {
        // SAFETY: caller guarantees ptr/size describe exactly the [aligned, aligned +
        // size) sub-range `map` returned above, which after trimming the head/tail
        // slivers is itself a single, still-mapped region.
        let ret = unsafe { libc::munmap(ptr.as_ptr().cast::<core::ffi::c_void>(), size) };
        debug_assert!(ret == 0, "munmap failed");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Every test below is Miri-ignored. This is a deliberate, permanent exception to
    // the crate's "every unsafe block gets a Miri-covered test" rule (Rust/CONVENTIONS.md),
    // not a "pending" gap — Miri cannot model either platform's raw VM syscall here:
    //   - Windows: Miri does not shim `VirtualAlloc` at all (confirmed empirically:
    //     "unsupported operation: can't call foreign function `VirtualAlloc`").
    //   - Unix: Miri's `mmap`/`munmap` shim only supports whole-region alloc/dealloc
    //     pairs ("simple allocation-like use cases"); it reports UB on the partial
    //     `munmap` that `map`'s trim-to-PAGE_SIZE-alignment step requires — a
    //     documented Miri scope limitation (see rust-lang/miri's shims/unix/mem
    //     docs), not a bug in this module. The trim technique itself is standard and
    //     race-free (PHP's memory manager uses the identical "map 2x, trim head and
    //     tail" technique for aligned chunk allocation).
    // This module's actual OS-level correctness is instead verified by native
    // `cargo test` on all three OSes (rust-ci.yml's `check` matrix), which exercises
    // the real kernel rather than Miri's synthetic memory model.

    #[test]
    #[cfg_attr(miri, ignore)]
    fn map_returns_page_size_aligned_memory() {
        let ptr = map(PAGE_SIZE).expect("OS map failed");
        assert_eq!(ptr.addr().get() % PAGE_SIZE, 0);
        // SAFETY: `ptr` was just returned by `map` above with the same size, and is
        // not used again after this call.
        unsafe { unmap(ptr, PAGE_SIZE) };
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn map_multi_page_region_is_writable_end_to_end() {
        let size = PAGE_SIZE * 3;
        let ptr = map(size).expect("OS map failed");
        assert_eq!(ptr.addr().get() % PAGE_SIZE, 0);
        // SAFETY: `ptr` denotes a fresh, exclusively-owned `size`-byte mapping; the
        // slice is valid for exactly that length and dropped before `unmap` below.
        unsafe {
            let slice = core::slice::from_raw_parts_mut(ptr.as_ptr(), size);
            slice.fill(0xAB);
            assert!(slice.iter().all(|&b| b == 0xAB));
        }
        // SAFETY: `ptr`/`size` match the `map` call above exactly.
        unsafe { unmap(ptr, size) };
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn repeated_map_unmap_cycles_stay_aligned() {
        for _ in 0..8 {
            let ptr = map(PAGE_SIZE).expect("OS map failed");
            assert_eq!(ptr.addr().get() % PAGE_SIZE, 0);
            // SAFETY: `ptr` was just returned by `map` above with the same size.
            unsafe { unmap(ptr, PAGE_SIZE) };
        }
    }

    #[test]
    #[cfg_attr(miri, ignore)]
    fn concurrent_live_mappings_do_not_alias() {
        let a = map(PAGE_SIZE).expect("OS map failed");
        let b = map(PAGE_SIZE).expect("OS map failed");
        assert_ne!(a, b);
        let ranges_overlap = {
            let a_start = a.addr().get();
            let b_start = b.addr().get();
            a_start < b_start + PAGE_SIZE && b_start < a_start + PAGE_SIZE
        };
        assert!(!ranges_overlap);
        // SAFETY: `a` is a mapping from `map` above, unmapped exactly once here.
        unsafe { unmap(a, PAGE_SIZE) };
        // SAFETY: `b` is a mapping from `map` above, unmapped exactly once here.
        unsafe { unmap(b, PAGE_SIZE) };
    }
}
