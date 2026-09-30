// SPDX-License-Identifier: MIT OR Apache-2.0
//! `Orisnik` with `debug-allocator`, installed as this process's own
//! `#[global_allocator]`.
//!
//! What this pins:
//!
//! 1. **No deadlock against application backtraces.** [`std::backtrace::Backtrace`]
//!    capture takes a process-wide, non-reentrant lock inside std and *allocates* while
//!    holding it. If the allocator's own hooks also captured a backtrace, an application
//!    capture (a panic hook with `RUST_BACKTRACE=1`, an explicit `Backtrace::capture`)
//!    would allocate → enter the hook → block on the same lock, forever. This program
//!    force-captures a backtrace from user code with `Orisnik` as the allocator; it
//!    hung before an instance used through `GlobalAlloc` stopped recording callstacks.
//! 2. **The bookkeeping stays consistent through `GlobalAlloc`.** A full std workload
//!    (growth by realloc from the bucket path through the tree path, shrinking, hash-map
//!    rehashing, zeroed and over-aligned allocations) must leave `requested()` exactly
//!    where it started, and must have moved it while allocations were live (so the check
//!    cannot pass vacuously with the hooks doing nothing).
//! 3. **`check()` finds the healthy heap healthy.** After the workload, the record audit
//!    over every live allocation of the process itself must come back `Ok`.
//!
//! It does **not** exercise the `busy` re-entrancy flag: with callstack capture off in
//! global mode, no hook allocates, so there is no recursion to break. That flag is
//! defence in depth for hooks that do allocate (`write_report`'s formatting), and is tested
//! directly in `orisnik_debug.rs`.
//!
//! It is its own integration-test binary with `harness = false` because a global
//! allocator is process-wide (a unit-test binary's harness threads would break the
//! single-threaded contract) and this way `main` is the only thread. It is skipped under
//! Miri, where `os::map` would be the real syscall (Miri covers the hooks through the
//! unit tests, which use the heap-backed `test_vm` stand-in).

#[cfg(not(miri))]
mod scenario {
    use orisnik::Orisnik;
    use std::collections::HashMap;

    #[global_allocator]
    static ALLOCATOR: Orisnik = Orisnik::new();

    /// A workload that exercises every allocator entry point through std: plain and aligned
    /// allocation, growth by realloc (bucket path, bucket-to-tree crossover, tree path),
    /// shrinking, zeroed allocation, and freeing.
    fn mark(label: &str) {
        eprintln!("DIAG {label}: requested={}", ALLOCATOR.requested());
    }

    fn workload() -> usize {
        let mut checksum = 0_usize;
        mark("workload start");

        // `Vec` growth is a chain of reallocs from tiny (bucket path) to large (tree path).
        let mut growing: Vec<u64> = Vec::new();
        for i in 0..50_000_u64 {
            growing.push(i);
        }
        checksum += usize::try_from(growing.iter().copied().sum::<u64>()).unwrap_or(0);
        growing.truncate(10);
        growing.shrink_to_fit();
        checksum += growing.len();
        mark("after growing");

        // Many small, differently-sized allocations alive at once.
        let strings: Vec<String> = (0..2_000)
            .map(|i| format!("item-{i:04}-{}", "x".repeat(i % 40)))
            .collect();
        checksum += strings.iter().map(String::len).sum::<usize>();
        mark("after strings");

        // A hash map allocates and rehashes.
        let mut map: HashMap<usize, Vec<u8>> = HashMap::new();
        for i in 0..500 {
            map.insert(i, vec![0_u8; 1 + i % 300]);
        }
        checksum += map.values().map(Vec::len).sum::<usize>();
        mark("after map");

        // Zeroed and over-aligned allocations.
        let zeroed = vec![0_u32; 10_000];
        checksum += zeroed.len();
        let aligned: Box<[u8; 4096]> = Box::new([7; 4096]);
        checksum += aligned.iter().map(|byte| usize::from(*byte)).sum::<usize>();
        mark("after zeroed/aligned");

        // Application code capturing a backtrace: std holds its (non-reentrant) backtrace lock
        // while it allocates, and that allocation lands in *this* allocator. Before the
        // global-allocator rule (no callstack capture for an instance used through
        // `GlobalAlloc`), the hook tried to take the same lock and this line deadlocked — the
        // regression this test pins. A panic hook with `RUST_BACKTRACE=1` is the same pattern.
        let trace = std::backtrace::Backtrace::force_capture();
        checksum += usize::from(trace.status() == std::backtrace::BacktraceStatus::Captured);
        mark("after backtrace");

        mark("before drops");
        checksum
    }

    pub fn run() {
        // Warm up anything the runtime allocates lazily on first use (stdout's buffer), so
        // the measurements below see only the workload.
        println!("debug_global_allocator: start");

        let before = ALLOCATOR.requested();
        // While allocations are live the total must actually move: without this, a hook that
        // did nothing would satisfy the balance check below (0 == 0).
        let live = vec![0_u8; 100];
        assert!(
            ALLOCATOR.requested() >= before + live.len(),
            "the hooks must be counting live allocations"
        );
        drop(live);
        assert_eq!(ALLOCATOR.requested(), before, "and un-counting them");
        let first = workload();
        let after = ALLOCATOR.requested();
        mark("after workload returned");
        assert_eq!(
            before, after,
            "every byte the workload asked for must have been returned and un-counted"
        );

        // Run it again: the second pass reuses the first pass's memory and warmed caches, and
        // must balance just the same.
        let before = ALLOCATOR.requested();
        let second = workload();
        let after = ALLOCATOR.requested();
        assert_eq!(before, after, "second pass must balance too");
        // The public audit over a heap full of real std allocations (the runtime's own,
        // this test's, and whatever is still live): none may be reported corrupt.
        let audit = ALLOCATOR.check();
        assert!(
            audit.is_ok(),
            "check() must find a healthy heap healthy: {audit:?}"
        );
        assert_eq!(first, second, "the workload is deterministic");

        println!("debug_global_allocator: ok (checksum {first})");
    }
}

fn main() {
    #[cfg(not(miri))]
    scenario::run();
}
