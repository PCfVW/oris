// SPDX-License-Identifier: MIT OR Apache-2.0
//! The process's current resident set size, in bytes.
//!
//! Linux: `VmRSS` from `/proc/self/status`. Windows: the working set
//! (`GetProcessMemoryInfo`). macOS: `ru_maxrss` is a lifetime peak, which cannot be
//! sampled, so there it is reported as such (see `benchmarks/methodology.md`).

#[cfg(target_os = "linux")]
pub fn current() -> u64 {
    let status = std::fs::read_to_string("/proc/self/status").unwrap_or_default();
    status
        .lines()
        .find_map(|l| l.strip_prefix("VmRSS:"))
        .and_then(|v| v.trim().trim_end_matches("kB").trim().parse::<u64>().ok())
        .map_or(0, |kb| kb * 1024)
}

#[cfg(windows)]
pub fn current() -> u64 {
    use windows_sys::Win32::System::ProcessStatus::{
        GetProcessMemoryInfo, PROCESS_MEMORY_COUNTERS,
    };
    use windows_sys::Win32::System::Threading::GetCurrentProcess;
    // SAFETY: a zeroed PROCESS_MEMORY_COUNTERS is a valid out-parameter of the size given.
    unsafe {
        let mut counters: PROCESS_MEMORY_COUNTERS = std::mem::zeroed();
        let size = std::mem::size_of::<PROCESS_MEMORY_COUNTERS>() as u32;
        if GetProcessMemoryInfo(GetCurrentProcess(), &mut counters, size) == 0 {
            return 0;
        }
        counters.WorkingSetSize as u64
    }
}

#[cfg(not(any(target_os = "linux", windows)))]
pub fn current() -> u64 {
    // SAFETY: a zeroed rusage is a valid out-parameter.
    unsafe {
        let mut usage: libc::rusage = std::mem::zeroed();
        libc::getrusage(libc::RUSAGE_SELF, &mut usage);
        usage.ru_maxrss as u64 // bytes on macOS: a lifetime peak, not the current size
    }
}
