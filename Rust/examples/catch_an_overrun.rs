// SPDX-License-Identifier: MIT OR Apache-2.0
//! The debug allocator catching, on purpose, the two mistakes it exists for: a write past
//! the end of a block, and a block that is never freed.
//!
//! ```text
//! cargo run --example catch_an_overrun --features debug-allocator
//! ```
//!
//! Walkthrough: `docs/debug-allocator.md` in the repository root (not in the crates.io
//! package). Build it with the default `panic = "unwind"`: it catches the leak's panic, which
//! `panic = "abort"` would turn into an abort. The instance is boxed because an `Orisnik` must
//! not move after first use (its intrusive lists are bound to its address); a `Box` moves
//! freely because the `Orisnik` inside stays put.

// An example, not the allocator: `expect` is the honest way to say "the OS refused a page".
#![allow(clippy::expect_used)]

use orisnik::Orisnik;
use std::panic::{self, AssertUnwindSafe};

/// The message's first line: the diagnostic proper. The rest is the allocation callstack.
fn headline(message: &str) -> &str {
    message.lines().next().unwrap_or(message)
}

fn main() {
    let allocator = Box::new(Orisnik::new());

    // 1. A one-byte overrun. The allocator reserves a guard ramp just past every block.
    let block = allocator.alloc(24).expect("the OS refused a page");
    // SAFETY: one byte past the end of a 24-byte block is still inside the page the block
    // lives in, so the offset stays in bounds of the allocation the pointer came from.
    let past_the_end = unsafe { block.as_ptr().add(24) };
    // SAFETY: `past_the_end` is inside the allocator's own page: deliberately outside what was
    // asked for, in the guard ramp the debug allocator placed there.
    let guard_byte = unsafe { past_the_end.read() };
    // SAFETY: as above. This one-byte overrun is the bug the example demonstrates.
    unsafe { past_the_end.write(guard_byte ^ 0xFF) };

    // `check()` asks: is every live block intact? It reports instead of panicking.
    match allocator.check() {
        Ok(()) => println!("check(): all blocks intact"),
        Err(error) => println!("check() found: {}", headline(&error.to_string())),
    }

    // Undo the damage so the block can be freed. (Freeing it as it is would panic: every
    // `free` verifies the guard first.)
    // SAFETY: as above, restoring the byte the guard ramp had.
    unsafe { past_the_end.write(guard_byte) };
    println!("check() after repair: {:?}", allocator.check().is_ok());

    // 2. A report of what is live right now: totals and one line per block.
    let mut report = String::new();
    allocator
        .write_report(&mut report)
        .expect("String never fails");
    for line in report.lines().filter(|line| !line.starts_with(' ')) {
        println!("{line}");
    }

    // 3. A leak. Dropping the allocator with `block` still live prints the report to stderr
    // and then panics; the panic is caught here only to show its message.
    panic::set_hook(Box::new(|_| {}));
    let outcome = panic::catch_unwind(AssertUnwindSafe(move || drop(allocator)));
    let _ = panic::take_hook();
    match outcome {
        Ok(()) => println!("drop: no leak detected (unexpected)"),
        Err(payload) => {
            let message = payload
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| {
                    payload
                        .downcast_ref::<&str>()
                        .map(|text| (*text).to_owned())
                })
                .unwrap_or_default();
            println!("drop panicked: {message}");
        }
    }
}
