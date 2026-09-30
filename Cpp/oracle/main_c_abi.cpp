// SPDX-License-Identifier: MIT OR Apache-2.0
//
// A mechanical port of Lazarov's own `hpha-errata/main.cpp` benchmark1() onto the
// oris_* C ABI (../../include/oris.h) — the audit's "Option A"
// (../../docs/audits/2026-08-29-pre-v0.2.0-audit.md#on-running-lazarovs-maincpp).
// `gAllocator.x(...)` calls become `oris_x(h, ...)` through an explicit handle
// (oris.h has no global-singleton form); the CRT/`_aligned_*` comparison arms and
// the timing loops are otherwise untouched. `benchmark2()` (operator-new/delete
// exposition) is dropped — it exercises no allocator surface, per the audit.
//
// This is a manual, one-off confidence check that 512 Ki live allocations at
// Lazarov's own r^8-skewed size distribution survive through a real port, not a
// test suite: like the original, it carries no assertions beyond the one added at
// the very end (`oris_purge` must reclaim everything). See this directory's
// README.md for how to build and run it against each port in turn — Windows/MSVC
// only, same as `oracle_trace.cpp`, and not wired into CI for the same reason.

#include "../../include/oris.h"

#include <assert.h>
#include <malloc.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

const unsigned N = 1024 * 512;
const size_t MIN_SIZE_LOG2 = 1;
const size_t MIN_SIZE = 1 << MIN_SIZE_LOG2;
const size_t MAX_SIZE_LOG2 = 12;
const size_t MAX_SIZE = 1 << MAX_SIZE_LOG2;
const size_t MAX_ALIGNMENT_LOG2 = 7;
const size_t MAX_ALIGNMENT = 1 << MAX_ALIGNMENT_LOG2;

struct test_record {
	void* ptr;
	size_t size;
	size_t alignment;
	size_t _padding;
} tr[N];

size_t rand_size() {
	float r = float(rand()) / RAND_MAX;
	return MIN_SIZE + (size_t)((MAX_SIZE - MIN_SIZE) * powf(r, 8.0f));
}

size_t rand_alignment() {
	float r = float(rand()) / RAND_MAX;
	return 1 << (size_t)(MAX_ALIGNMENT_LOG2 * r);
}

void benchmark1(OrisAllocator* h) {
	clock_t start, finish;

	printf("\t\t\t\t\t\tORIS\t\tDEFAULT\n");

	printf("TEST ALLOC/FREE:");
	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		tr[i].ptr = oris_alloc(h, size);
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		oris_free(h, tr[j].ptr);
		tr[j].ptr = tr[i].ptr;
	}
	finish = clock();
	printf("\t\t\t\t(%f)", (double)(finish - start) / CLOCKS_PER_SEC);

	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		tr[i].ptr = malloc(size);
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		free(tr[j].ptr);
		tr[j].ptr = tr[i].ptr;
	}
	finish = clock();
	printf("\t(%f)\n", (double)(finish - start) / CLOCKS_PER_SEC);

	printf("TEST ALLOC/FREE plus SIZE:");
	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		tr[i].ptr = oris_alloc(h, size);
		tr[i].size = size;
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		oris_free_with_size(h, tr[j].ptr, tr[j].size);
		tr[j].ptr = tr[i].ptr;
		tr[j].size = tr[i].size;
	}
	finish = clock();
	printf("\t\t\t(%f)", (double)(finish - start) / CLOCKS_PER_SEC);

	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		tr[i].ptr = malloc(size);
		tr[i].size = size;
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		free(tr[j].ptr);
		tr[j].ptr = tr[i].ptr;
		tr[j].size = tr[i].size;
	}
	finish = clock();
	printf("\t(%f)\n", (double)(finish - start) / CLOCKS_PER_SEC);

	printf("TEST ALLOC/FREE with ALIGNMENT:");
	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		size_t alignment = rand_alignment();
		tr[i].ptr = oris_alloc_aligned(h, size, alignment);
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		oris_free(h, tr[j].ptr);
		tr[j].ptr = tr[i].ptr;
	}
	finish = clock();
	printf("\t\t\t(%f)", (double)(finish - start) / CLOCKS_PER_SEC);

	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		size_t alignment = rand_alignment();
		tr[i].ptr = _aligned_malloc(size, alignment);
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		_aligned_free(tr[j].ptr);
		tr[j].ptr = tr[i].ptr;
	}
	finish = clock();
	printf("\t(%f)\n", (double)(finish - start) / CLOCKS_PER_SEC);

	printf("TEST ALLOC/FREE with ALIGNMENT plus SIZE:");
	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		size_t alignment = rand_alignment();
		tr[i].ptr = oris_alloc_aligned(h, size, alignment);
		tr[i].size = size;
		tr[i].alignment = alignment;
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		oris_free_with_size_aligned(h, tr[j].ptr, tr[j].size, tr[j].alignment);
		tr[j].ptr = tr[i].ptr;
		tr[j].size = tr[i].size;
		tr[j].alignment = tr[i].alignment;
	}
	finish = clock();
	printf("\t(%f)", (double)(finish - start) / CLOCKS_PER_SEC);

	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		size_t alignment = rand_alignment();
		tr[i].ptr = _aligned_malloc(size, alignment);
		tr[i].size = size;
		tr[i].alignment = alignment;
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		_aligned_free(tr[j].ptr);
		tr[j].ptr = tr[i].ptr;
		tr[j].size = tr[i].size;
		tr[j].alignment = tr[i].alignment;
	}
	finish = clock();
	printf("\t(%f)\n", (double)(finish - start) / CLOCKS_PER_SEC);

	printf("TEST REALLOC:");
	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		tr[i].ptr = oris_realloc(h, NULL, size);
	}
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		tr[i].ptr = oris_realloc(h, tr[i].ptr, size);
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		oris_realloc(h, tr[j].ptr, 0);
		tr[j].ptr = tr[i].ptr;
	}
	finish = clock();
	printf("\t\t\t\t\t(%f)", (double)(finish - start) / CLOCKS_PER_SEC);

	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		tr[i].ptr = realloc(NULL, size);
	}
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		tr[i].ptr = realloc(tr[i].ptr, size);
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		realloc(tr[j].ptr, 0);
		tr[j].ptr = tr[i].ptr;
	}
	finish = clock();
	printf("\t(%f)\n", (double)(finish - start) / CLOCKS_PER_SEC);

	printf("TEST REALLOC with ALIGNMENT:");
	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		size_t alignment = rand_alignment();
		tr[i].ptr = oris_realloc_aligned(h, NULL, size, alignment);
	}
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		size_t alignment = rand_alignment();
		tr[i].ptr = oris_realloc_aligned(h, tr[i].ptr, size, alignment);
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		// This is the one call the pre-v0.1.1 crate could not survive at all
		// (audit finding F5): HPHA accepts alignment == 0 as "no alignment
		// requested", and Lazarov's own benchmark relies on exactly that here.
		oris_realloc_aligned(h, tr[j].ptr, 0, 0);
		tr[j].ptr = tr[i].ptr;
	}
	finish = clock();
	printf("\t\t\t(%f)", (double)(finish - start) / CLOCKS_PER_SEC);

	srand(1234);
	start = clock();
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		size_t alignment = rand_alignment();
		tr[i].ptr = _aligned_realloc(NULL, size, alignment);
	}
	for (unsigned i = 0; i < N; i++) {
		size_t size = rand_size();
		size_t alignment = rand_alignment();
		tr[i].ptr = _aligned_realloc(tr[i].ptr, size, alignment);
	}
	for (unsigned i = 0; i < N; i++) {
		unsigned j = i + rand() % (N - i);
		_aligned_realloc(tr[j].ptr, 0, 0);
		tr[j].ptr = tr[i].ptr;
	}
	finish = clock();
	printf("\t(%f)\n", (double)(finish - start) / CLOCKS_PER_SEC);
}

int main() {
	OrisAllocator* h = oris_new();
	assert(h != NULL);

	benchmark1(h);

	// Not part of Lazarov's original — added because it turns "did the process
	// survive" into one further, cheap, concrete check: every one of the 512 Ki
	// allocations driven above must be reclaimable by oris_purge().
	oris_purge(h);
	printf("\nallocated after purge: %zu (expected 0)\n", oris_allocated(h));
	assert(oris_allocated(h) == 0);

	oris_destroy(h);
	return 0;
}
