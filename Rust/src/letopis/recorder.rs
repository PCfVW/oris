// SPDX-License-Identifier: MIT OR Apache-2.0
//! Recording a trace from a live program: a wrapper around an [`Orisnik`] that forwards
//! every call and writes it as a canonical trace line.

use crate::Orisnik;
use core::fmt;
use core::ptr::NonNull;
use std::collections::HashMap;

/// Records every call made through it as a trace (`examples/traces/GRAMMAR.md` §1), then
/// forwards it to the wrapped [`Orisnik`].
///
/// Pointers become symbolic handles: each allocation gets the next `hN`, a realloc keeps its
/// pointer's handle, a free retires it. The written trace replays with
/// [`replay`](super::replay()) on any of the three implementations.
///
/// What it does not do:
///
/// - **It is not a `#[global_allocator]`.** It keeps its pointer-to-handle table in a
///   `HashMap` and writes through `W`, both of which may allocate — through the global
///   allocator, which must therefore be some other allocator.
/// - **It does not check the semantic constraints** (`GRAMMAR.md` §1.3) that only a trace,
///   not a program, must meet: a program may legitimately `free_with_size` after a
///   `realloc`, or ask for more than 2³⁰ bytes. Such a call is recorded faithfully, and
///   [`replay`](super::replay()) then refuses the trace with the rule and line it breaks.
/// - **A null pointer passed to `free`, `resize` or `size`** is forwarded but not
///   recorded: the call does nothing, and a trace has no handle for it.
/// - **A pointer the recorder did not hand out** (from another allocator, or from before
///   recording started) is passed through to the allocator unchanged and recorded under a
///   handle that was never bound — which the replayer rejects (constraint C2), so a
///   recording that would not replay says so.
///
/// A write error does not interrupt the program: the first one is kept and returned by
/// [`finish`](Self::finish), and nothing more is written after it.
///
/// ```
/// use orisnik::Orisnik;
/// use orisnik::letopis::{Recorder, replay};
///
/// let allocator = Orisnik::new();
/// let mut recorder = Recorder::new(&allocator, String::new());
/// let p = recorder.alloc(24);
/// // SAFETY: `p` came from this recorder's allocator and is freed once.
/// unsafe { recorder.free(p) };
/// let trace = recorder.finish().unwrap();
/// assert_eq!(trace, "oris-trace 1\nalloc h0 24\nfree h0\n");
///
/// let mut record = String::new();
/// replay(&trace, &mut record).unwrap();
/// assert!(record.starts_with("oris-record 1\n#0 alloc h0 24 -> m0+0x0 a=65536\n"));
/// ```
pub struct Recorder<'a, W: fmt::Write> {
    /// The allocator every call is forwarded to.
    allocator: &'a Orisnik,
    /// Where the trace is written.
    out: W,
    /// The handle each live pointer was recorded under.
    handles: HashMap<usize, u64>,
    /// The handle the next unknown pointer or allocation gets.
    next_handle: u64,
    /// The first write error, after which nothing more is written.
    error: Option<fmt::Error>,
}

impl<'a, W: fmt::Write> Recorder<'a, W> {
    /// Starts recording calls to `allocator` into `out`, beginning with the trace header.
    pub fn new(allocator: &'a Orisnik, out: W) -> Self {
        let mut recorder = Self {
            allocator,
            out,
            handles: HashMap::new(),
            next_handle: 0,
            error: None,
        };
        recorder.line(format_args!("oris-trace 1"));
        recorder
    }

    /// Ends the recording and returns the writer.
    ///
    /// # Errors
    /// The first error `out` returned, if any (everything after it was not written).
    pub fn finish(self) -> Result<W, fmt::Error> {
        match self.error {
            Some(error) => Err(error),
            None => Ok(self.out),
        }
    }

    fn line(&mut self, args: fmt::Arguments<'_>) {
        if self.error.is_none() {
            if let Err(error) = writeln!(self.out, "{args}") {
                self.error = Some(error);
            }
        }
    }

    fn fresh_handle(&mut self) -> u64 {
        let h = self.next_handle;
        self.next_handle += 1;
        h
    }

    /// The handle `ptr` was recorded under, or a never-bound one (see the type's doc).
    fn handle_of(&mut self, ptr: Option<NonNull<u8>>) -> u64 {
        let known = ptr.and_then(|p| self.handles.get(&p.addr().get()).copied());
        known.unwrap_or_else(|| self.fresh_handle())
    }

    fn bind(&mut self, h: u64, ptr: Option<NonNull<u8>>) -> Option<NonNull<u8>> {
        if let Some(p) = ptr {
            self.handles.insert(p.addr().get(), h);
        }
        ptr
    }

    /// Retires `ptr`'s handle and returns it; `None` for a null `ptr` (nothing to record).
    fn unbind(&mut self, ptr: Option<NonNull<u8>>) -> Option<u64> {
        let p = ptr?;
        let h = self.handle_of(ptr);
        self.handles.remove(&p.addr().get());
        Some(h)
    }

    /// [`Orisnik::alloc`], recorded as `alloc`.
    #[must_use]
    pub fn alloc(&mut self, size: usize) -> Option<NonNull<u8>> {
        let h = self.fresh_handle();
        self.line(format_args!("alloc h{h} {size}"));
        let ptr = self.allocator.alloc(size);
        self.bind(h, ptr)
    }

    /// [`Orisnik::alloc_aligned`], recorded as `alloc_aligned`.
    #[must_use]
    pub fn alloc_aligned(&mut self, size: usize, alignment: usize) -> Option<NonNull<u8>> {
        let h = self.fresh_handle();
        self.line(format_args!("alloc_aligned h{h} {size} {alignment}"));
        let ptr = self.allocator.alloc_aligned(size, alignment);
        self.bind(h, ptr)
    }

    /// [`Orisnik::calloc`], recorded as `calloc`.
    #[must_use]
    pub fn calloc(&mut self, count: usize, size: usize) -> Option<NonNull<u8>> {
        let h = self.fresh_handle();
        self.line(format_args!("calloc h{h} {count} {size}"));
        let ptr = self.allocator.calloc(count, size);
        self.bind(h, ptr)
    }

    /// [`Orisnik::realloc`], recorded as `realloc`.
    ///
    /// # Safety
    /// As [`Orisnik::realloc`].
    #[must_use]
    pub unsafe fn realloc(&mut self, ptr: Option<NonNull<u8>>, size: usize) -> Option<NonNull<u8>> {
        let h = self.handle_of(ptr);
        self.line(format_args!("realloc h{h} {size}"));
        // SAFETY: forwarded from this function's own contract.
        let new = unsafe { self.allocator.realloc(ptr, size) };
        self.rebound(h, ptr, size, new)
    }

    /// [`Orisnik::realloc_aligned`], recorded as `realloc_aligned`.
    ///
    /// # Safety
    /// As [`Orisnik::realloc_aligned`].
    #[must_use]
    pub unsafe fn realloc_aligned(
        &mut self,
        ptr: Option<NonNull<u8>>,
        size: usize,
        alignment: usize,
    ) -> Option<NonNull<u8>> {
        let h = self.handle_of(ptr);
        self.line(format_args!("realloc_aligned h{h} {size} {alignment}"));
        // SAFETY: forwarded from this function's own contract.
        let new = unsafe { self.allocator.realloc_aligned(ptr, size, alignment) };
        self.rebound(h, ptr, size, new)
    }

    /// A realloc's binding update: the old pointer is gone unless the call failed.
    fn rebound(
        &mut self,
        h: u64,
        old: Option<NonNull<u8>>,
        size: usize,
        new: Option<NonNull<u8>>,
    ) -> Option<NonNull<u8>> {
        if new.is_some() || size == 0 {
            if let Some(p) = old {
                self.handles.remove(&p.addr().get());
            }
        }
        self.bind(h, new)
    }

    /// [`Orisnik::resize`], recorded as `resize`.
    ///
    /// # Safety
    /// As [`Orisnik::resize`].
    #[must_use]
    pub unsafe fn resize(&mut self, ptr: Option<NonNull<u8>>, size: usize) -> usize {
        if ptr.is_some() {
            let h = self.handle_of(ptr);
            self.line(format_args!("resize h{h} {size}"));
        }
        // SAFETY: forwarded from this function's own contract.
        unsafe { self.allocator.resize(ptr, size) }
    }

    /// [`Orisnik::size`], recorded as `size`.
    ///
    /// # Safety
    /// As [`Orisnik::size`].
    #[must_use]
    pub unsafe fn size(&mut self, ptr: Option<NonNull<u8>>) -> usize {
        if ptr.is_some() {
            let h = self.handle_of(ptr);
            self.line(format_args!("size h{h}"));
        }
        // SAFETY: forwarded from this function's own contract.
        unsafe { self.allocator.size(ptr) }
    }

    /// [`Orisnik::free`], recorded as `free`.
    ///
    /// # Safety
    /// As [`Orisnik::free`].
    pub unsafe fn free(&mut self, ptr: Option<NonNull<u8>>) {
        if let Some(h) = self.unbind(ptr) {
            self.line(format_args!("free h{h}"));
        }
        // SAFETY: forwarded from this function's own contract.
        unsafe { self.allocator.free(ptr) };
    }

    /// [`Orisnik::free_with_size`], recorded as `free_sized`.
    ///
    /// # Safety
    /// As [`Orisnik::free_with_size`].
    pub unsafe fn free_with_size(&mut self, ptr: Option<NonNull<u8>>, orig_size: usize) {
        if let Some(h) = self.unbind(ptr) {
            self.line(format_args!("free_sized h{h} {orig_size}"));
        }
        // SAFETY: forwarded from this function's own contract.
        unsafe { self.allocator.free_with_size(ptr, orig_size) };
    }

    /// [`Orisnik::free_with_size_aligned`], recorded as `free_sized_aligned`.
    ///
    /// # Safety
    /// As [`Orisnik::free_with_size_aligned`].
    pub unsafe fn free_with_size_aligned(
        &mut self,
        ptr: Option<NonNull<u8>>,
        orig_size: usize,
        old_alignment: usize,
    ) {
        if let Some(h) = self.unbind(ptr) {
            self.line(format_args!(
                "free_sized_aligned h{h} {orig_size} {old_alignment}"
            ));
        }
        // SAFETY: forwarded from this function's own contract.
        unsafe {
            self.allocator
                .free_with_size_aligned(ptr, orig_size, old_alignment);
        };
    }

    /// [`Orisnik::purge`], recorded as `purge`.
    pub fn purge(&mut self) {
        self.line(format_args!("purge"));
        self.allocator.purge();
    }
}
