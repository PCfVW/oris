/* SPDX-License-Identifier: MIT OR Apache-2.0 */

/*
 * smoke.c — a real (not toy) C caller against the oris_* C-ABI, linked in CI
 * against both liborisnik.* (Rust) and liborisnitsa.* (Zig) — see
 * .github/workflows/c-abi-ci.yml. Exercises the sequence both ports' own
 * capi.rs/capi.zig unit tests already cover (round-trip alloc/realloc/free,
 * aligned alloc, calloc), from the other side of the ABI boundary this time:
 * the header's prototypes, not either port's internal test harness. Any
 * mismatch between include/oris.h and what a library actually exports/expects
 * — argument order, null/zero semantics, calling convention — fails to link or
 * asserts here, not silently.
 *
 * Exit code 0 on success; a failed assert() aborts with a nonzero exit.
 */

#include "oris.h"

#include <assert.h>
#include <string.h>

int main(void) {
    OrisAllocator *h = oris_new();
    assert(h != NULL);

    /* Default-alignment round trip: alloc, write, verify size, free. */
    unsigned char *p = (unsigned char *)oris_alloc(h, 64);
    assert(p != NULL);
    memset(p, 0xAB, 64);
    assert(oris_size(h, p) >= 64);
    oris_free(h, p);

    /* Aligned alloc + free_with_size_aligned. */
    unsigned char *aligned = (unsigned char *)oris_alloc_aligned(h, 48, 128);
    assert(aligned != NULL);
    assert(((size_t)aligned % 128) == 0);
    oris_free_with_size_aligned(h, aligned, 48, 128);

    /* calloc must zero every byte. */
    unsigned char *zeroed = (unsigned char *)oris_calloc(h, 4, 16);
    assert(zeroed != NULL);
    for (size_t i = 0; i < 64; ++i) {
        assert(zeroed[i] == 0);
    }
    oris_free_with_size(h, zeroed, 64);

    /* realloc preserves the prefix and can grow across the bucket/tree split. */
    unsigned char *small = (unsigned char *)oris_alloc(h, 16);
    assert(small != NULL);
    memset(small, 0xCD, 16);
    unsigned char *grown = (unsigned char *)oris_realloc(h, small, 4096);
    assert(grown != NULL);
    for (size_t i = 0; i < 16; ++i) {
        assert(grown[i] == 0xCD);
    }
    oris_free(h, grown);

    /* resize grows/shrinks in place without moving, or reports the unchanged
     * size honestly — either is a valid, non-null-pointer-adjacent result. */
    unsigned char *resizable = (unsigned char *)oris_alloc(h, 4096);
    assert(resizable != NULL);
    size_t resized = oris_resize(h, resizable, 4096 + 64);
    assert(resized >= 4096);
    oris_free(h, resizable);

    /* purge reclaims every fully-unused page/arena. */
    oris_purge(h);
    assert(oris_allocated(h) == 0);

    /* Null handling: oris_destroy(NULL) must be a documented no-op. */
    oris_destroy(NULL);

    oris_destroy(h);
    return 0;
}
