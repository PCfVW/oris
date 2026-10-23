// SPDX-License-Identifier: MIT OR Apache-2.0
//! The process's current resident set size, in bytes.
//!
//! Linux: `VmRSS` from `/proc/self/status`, read without allocating. Windows: the working set
//! (`GetProcessMemoryInfo`). macOS: `ru_maxrss` is a lifetime peak, which cannot be
//! sampled, so there it is reported as such (see `benchmarks/methodology.md`).

#[cfg(target_os = "linux")]
pub fn current() -> u64 {
    // No allocation: the harness's allocator never frees (see `bump.rs`), so a `String` per
    // sample would itself grow the resident set being measured.
    let mut buf = [0u8; 4096];
    // SAFETY: a NUL-terminated path; `buf` is valid for its length; the fd is closed below.
    let len = unsafe {
        let fd = libc::open(c"/proc/self/status".as_ptr(), libc::O_RDONLY);
        if fd < 0 {
            return 0;
        }
        let n = libc::read(fd, buf.as_mut_ptr().cast(), buf.len());
        libc::close(fd);
        n
    };
    let Ok(len) = usize::try_from(len) else {
        return 0;
    };
    let status = std::str::from_utf8(&buf[..len]).unwrap_or("");
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
