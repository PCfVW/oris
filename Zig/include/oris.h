/* SPDX-License-Identifier: MIT OR Apache-2.0 */

/*
 * oris.h — C prototypes for the oris_* C-ABI, implemented identically by both
 * Oris ports: `orisnik` (Rust, Rust/src/capi.rs) and `orisnitsa` (Zig,
 * Zig/src/capi.zig). Link against either liborisnik.* or liborisnitsa.* —
 * this header does not care which.
 *
 * Every function takes an explicit OrisAllocator* handle, mirroring HPHA's
 * own instantiable `class allocator` rather than a hidden global singleton
 * (see BRIEF.md's explicit-opt-in stance): a caller creates one with
 * oris_new(), threads the handle through every other call, and destroys it
 * with oris_destroy() when done.
 *
 * Thread safety: neither port implements internal locking for this slice
 * (HPHA's own MULTITHREADED mode is out of scope for both ports — see
 * ROADMAP.md); a given OrisAllocator* must not be used concurrently from
 * more than one thread without external synchronization.
 */

#ifndef ORIS_H
#define ORIS_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque allocator instance. Never dereference or inspect its layout — the
 * two ports lay it out differently. */
typedef struct OrisAllocator OrisAllocator;

/* Creates a fresh allocator instance on the heap, returning an opaque owning
 * handle. Pair with oris_destroy(). Never returns NULL. */
OrisAllocator *oris_new(void);

/* Destroys an allocator instance created by oris_new(). handle == NULL is a
 * no-op. Every allocation made through handle should already be freed or
 * intentionally leaked first: destroying the instance does not return its
 * outstanding OS pages/arenas — call oris_purge() beforehand if reclaiming
 * that memory matters. handle must not be used again after this call. */
void oris_destroy(OrisAllocator *handle);

/* Allocates size bytes at the allocator's default alignment. size == 0
 * returns NULL. */
void *oris_alloc(OrisAllocator *handle, size_t size);

/* Allocates size bytes aligned to alignment. size == 0 returns NULL. */
void *oris_alloc_aligned(OrisAllocator *handle, size_t size, size_t alignment);

/* Allocates count * size bytes at the default alignment, zeroed. */
void *oris_calloc(OrisAllocator *handle, size_t count, size_t size);

/* Grows, shrinks, or moves ptr to size bytes at the default alignment.
 * ptr == NULL acts as oris_alloc(); size == 0 acts as oris_free() and
 * returns NULL. ptr, if non-NULL, must be a still-live allocation handle
 * produced. */
void *oris_realloc(OrisAllocator *handle, void *ptr, size_t size);

/* Grows, shrinks, or moves ptr to size bytes aligned to alignment.
 * ptr == NULL acts as oris_alloc_aligned(); size == 0 acts as oris_free()
 * and returns NULL. ptr, if non-NULL, must be a still-live allocation
 * handle produced. */
void *oris_realloc_aligned(OrisAllocator *handle, void *ptr, size_t size,
                            size_t alignment);

/* Grows or shrinks ptr in place to the extent possible, without ever moving
 * it, returning the resulting usable size. ptr == NULL returns 0. */
size_t oris_resize(OrisAllocator *handle, void *ptr, size_t size);

/* Queries the usable size of ptr's allocation. ptr == NULL returns 0. */
size_t oris_size(OrisAllocator *handle, void *ptr);

/* Frees ptr. ptr == NULL is a no-op. */
void oris_free(OrisAllocator *handle, void *ptr);

/* Frees ptr, given its original request size at the default alignment.
 * ptr == NULL is a no-op. orig_size must be ptr's size at the moment it was
 * allocated, not a size from any later oris_realloc()/oris_resize() call —
 * prefer oris_free() whenever ptr's allocation history isn't certain to be
 * realloc-free. */
void oris_free_with_size(OrisAllocator *handle, void *ptr, size_t orig_size);

/* Frees ptr, given its original request size and alignment. ptr == NULL is
 * a no-op. orig_size/old_alignment must be ptr's size/alignment at the
 * moment it was allocated — prefer oris_free() whenever ptr's allocation
 * history isn't certain to be realloc-free. */
void oris_free_with_size_aligned(OrisAllocator *handle, void *ptr,
                                  size_t orig_size, size_t old_alignment);

/* Returns every fully-unused page/arena to the OS. */
void oris_purge(OrisAllocator *handle);

/* Total bytes currently claimed from the OS across both allocation paths. */
size_t oris_allocated(OrisAllocator *handle);

#ifdef __cplusplus
} /* extern "C" */
#endif

#endif /* ORIS_H */
