// SPDX-License-Identifier: MIT OR Apache-2.0
//! Reading a trace: the contract grammar of `examples/traces/GRAMMAR.md` §1.1, then the
//! semantic constraints of §1.3, so that nothing undefined is ever replayed.
//!
//! The parser is a straight line-by-line tokenizer: the grammar has no nesting, every
//! token is separated by spaces or tabs, and a line is one operation, a comment or blank.

use super::ReplayError;
use core::fmt;
use std::collections::HashMap;

/// The largest size (and `calloc` product) a trace may request: 2³⁰ (constraint C4).
pub(crate) const MAX_TRACE_SIZE: u64 = 1 << 30;

/// The largest alignment a trace may request: `PAGE_SIZE` (constraint C3).
pub(crate) const MAX_TRACE_ALIGNMENT: u64 = 1 << 16;

/// One trace operation. `h` is always the handle number (`hN`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Op {
    /// `alloc h S`
    Alloc { h: u64, size: u64 },
    /// `alloc_aligned h S A`
    AllocAligned { h: u64, size: u64, align: u64 },
    /// `calloc h N S`
    Calloc { h: u64, count: u64, size: u64 },
    /// `realloc h S`
    Realloc { h: u64, size: u64 },
    /// `realloc_aligned h S A`
    ReallocAligned { h: u64, size: u64, align: u64 },
    /// `resize h S`
    Resize { h: u64, size: u64 },
    /// `size h`
    Size { h: u64 },
    /// `free h`
    Free { h: u64 },
    /// `free_sized h S`
    FreeSized { h: u64, size: u64 },
    /// `free_sized_aligned h S A`
    FreeSizedAligned { h: u64, size: u64, align: u64 },
    /// `purge`
    Purge,
}

/// The canonical rendering (§1.4): keyword and arguments separated by single spaces.
impl fmt::Display for Op {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Op::Alloc { h, size } => write!(f, "alloc h{h} {size}"),
            Op::AllocAligned { h, size, align } => write!(f, "alloc_aligned h{h} {size} {align}"),
            Op::Calloc { h, count, size } => write!(f, "calloc h{h} {count} {size}"),
            Op::Realloc { h, size } => write!(f, "realloc h{h} {size}"),
            Op::ReallocAligned { h, size, align } => {
                write!(f, "realloc_aligned h{h} {size} {align}")
            }
            Op::Resize { h, size } => write!(f, "resize h{h} {size}"),
            Op::Size { h } => write!(f, "size h{h}"),
            Op::Free { h } => write!(f, "free h{h}"),
            Op::FreeSized { h, size } => write!(f, "free_sized h{h} {size}"),
            Op::FreeSizedAligned { h, size, align } => {
                write!(f, "free_sized_aligned h{h} {size} {align}")
            }
            Op::Purge => f.write_str("purge"),
        }
    }
}

/// A parsed operation and the 1-based line it came from.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Line {
    /// The operation.
    pub(crate) op: Op,
    /// Where it was read, for error messages.
    pub(crate) number: usize,
}

/// Parses `text` against the contract grammar and checks every semantic constraint.
///
/// # Errors
/// [`ReplayError::Syntax`] for the first line the grammar rejects, [`ReplayError::Semantic`]
/// for the first operation breaking a constraint.
pub(crate) fn parse(text: &str) -> Result<Vec<Line>, ReplayError> {
    let mut lines = text.split('\n').enumerate();
    let header = lines.next().map(|(_, line)| strip_cr(line));
    let header_ok = header.is_some_and(|line| {
        let mut tokens = tokens(line);
        tokens.next() == Some("oris-trace") && tokens.next() == Some("1") && tokens.next().is_none()
    });
    if !header_ok {
        return Err(syntax(1, "missing header `oris-trace 1`"));
    }
    let mut ops = Vec::new();
    // A final line without `eol` is accepted (GRAMMAR.md §1.5); `split` then yields it
    // last, while a well-terminated file yields an empty final piece, which is a blank.
    for (index, raw) in lines {
        let number = index + 1;
        let line = strip_cr(raw);
        let trimmed = line.trim_start_matches([' ', '\t']);
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let op = parse_op(line).map_err(|message| syntax(number, &message))?;
        ops.push(Line { op, number });
    }
    validate(&ops)?;
    Ok(ops)
}

fn strip_cr(line: &str) -> &str {
    line.strip_suffix('\r').unwrap_or(line)
}

fn tokens(line: &str) -> impl Iterator<Item = &str> {
    line.split([' ', '\t']).filter(|token| !token.is_empty())
}

fn syntax(line: usize, message: &str) -> ReplayError {
    ReplayError::Syntax {
        line,
        message: message.to_owned(),
    }
}

fn parse_op(line: &str) -> Result<Op, String> {
    let mut tokens = tokens(line);
    let keyword = tokens.next().unwrap_or_default();
    let args: Vec<&str> = tokens.collect();
    let arity = match keyword {
        "purge" => 0,
        "size" | "free" => 1,
        "alloc" | "realloc" | "resize" | "free_sized" => 2,
        "alloc_aligned" | "calloc" | "realloc_aligned" | "free_sized_aligned" => 3,
        _ => return Err(format!("unknown operation `{keyword}`")),
    };
    if args.len() != arity {
        return Err(format!(
            "`{keyword}` takes {arity} argument(s), found {}",
            args.len()
        ));
    }
    if keyword == "purge" {
        return Ok(Op::Purge);
    }
    let mut args = args.into_iter();
    let h = parse_handle(args.next().unwrap_or_default())?;
    let mut number = || parse_number(args.next().unwrap_or_default());
    Ok(match keyword {
        "alloc" => Op::Alloc { h, size: number()? },
        "alloc_aligned" => Op::AllocAligned {
            h,
            size: number()?,
            align: number()?,
        },
        "calloc" => Op::Calloc {
            h,
            count: number()?,
            size: number()?,
        },
        "realloc" => Op::Realloc { h, size: number()? },
        "realloc_aligned" => Op::ReallocAligned {
            h,
            size: number()?,
            align: number()?,
        },
        "resize" => Op::Resize { h, size: number()? },
        "size" => Op::Size { h },
        "free" => Op::Free { h },
        "free_sized" => Op::FreeSized { h, size: number()? },
        "free_sized_aligned" => Op::FreeSizedAligned {
            h,
            size: number()?,
            align: number()?,
        },
        _ => return Err(format!("unknown operation `{keyword}`")),
    })
}

fn parse_handle(token: &str) -> Result<u64, String> {
    let digits = token
        .strip_prefix('h')
        .ok_or_else(|| format!("expected a handle `hN`, found `{token}`"))?;
    parse_number(digits).map_err(|_| format!("expected a handle `hN`, found `{token}`"))
}

/// `"0" | nonzero_digit , { digit }`, fitting a `u64`.
fn parse_number(token: &str) -> Result<u64, String> {
    let well_formed = !token.is_empty()
        && token.bytes().all(|b| b.is_ascii_digit())
        && (token == "0" || !token.starts_with('0'));
    if !well_formed {
        return Err(format!("expected a number, found `{token}`"));
    }
    token
        .parse()
        .map_err(|_| format!("number `{token}` does not fit in 64 bits"))
}

/// What a bound handle was last bound by, for the sized-free rules C6/C7: the size and
/// alignment of its binding `alloc`/`calloc`/`alloc_aligned`, or `None` once a realloc or
/// resize has touched it.
type Binding = Option<(u64, u64)>;

/// Checks the semantic constraints C1–C8 (`GRAMMAR.md` §1.3) over the whole trace.
fn validate(ops: &[Line]) -> Result<(), ReplayError> {
    // Bound handles only; an absent key is an unbound handle.
    let mut bound: HashMap<u64, Binding> = HashMap::new();
    for line in ops {
        let fail = |rule: &str, message: String| ReplayError::Semantic {
            line: line.number,
            message: format!("{rule}: {message}"),
        };
        let size_ok = |size: u64| size <= MAX_TRACE_SIZE;
        let align_ok =
            |align: u64| align == 0 || (align.is_power_of_two() && align <= MAX_TRACE_ALIGNMENT);
        match line.op {
            Op::Alloc { h, size } | Op::AllocAligned { h, size, .. } => {
                if bound.contains_key(&h) {
                    return Err(fail("C1", format!("h{h} is already bound")));
                }
                if !size_ok(size) {
                    return Err(fail("C4", format!("size {size} exceeds 2^30")));
                }
                let align = if let Op::AllocAligned { align, .. } = line.op {
                    align
                } else {
                    0
                };
                if !align_ok(align) {
                    return Err(fail(
                        "C3",
                        format!("alignment {align} is not 0 or a power of two at most 65536"),
                    ));
                }
                bound.insert(h, Some((size, align)));
            }
            Op::Calloc { h, count, size } => {
                if bound.contains_key(&h) {
                    return Err(fail("C1", format!("h{h} is already bound")));
                }
                let product = count.checked_mul(size).filter(|&p| size_ok(p));
                let Some(product) = product else {
                    return Err(fail("C4", format!("{count} x {size} exceeds 2^30")));
                };
                bound.insert(h, Some((product, 0)));
            }
            Op::Realloc { h, size } | Op::ReallocAligned { h, size, .. } => {
                if !size_ok(size) {
                    return Err(fail("C4", format!("size {size} exceeds 2^30")));
                }
                if let Op::ReallocAligned { align, .. } = line.op {
                    if !align_ok(align) {
                        return Err(fail(
                            "C3",
                            format!("alignment {align} is not 0 or a power of two at most 65536"),
                        ));
                    }
                    if align > 256 && size <= 256 {
                        return Err(fail(
                            "C8",
                            format!(
                                "alignment {align} above 256 needs a size above 256, found {size}"
                            ),
                        ));
                    }
                }
                bound.insert(h, None);
            }
            Op::Resize { h, size } => {
                if !bound.contains_key(&h) {
                    return Err(fail("C2", format!("h{h} is not bound")));
                }
                if size == 0 {
                    return Err(fail("C5", "resize to 0".to_owned()));
                }
                if !size_ok(size) {
                    return Err(fail("C4", format!("size {size} exceeds 2^30")));
                }
                bound.insert(h, None);
            }
            Op::Size { h } => {
                if !bound.contains_key(&h) {
                    return Err(fail("C2", format!("h{h} is not bound")));
                }
            }
            Op::Free { h } => {
                if bound.remove(&h).is_none() {
                    return Err(fail("C2", format!("h{h} is not bound")));
                }
            }
            Op::FreeSized { h, size } => {
                let Some(binding) = bound.remove(&h) else {
                    return Err(fail("C2", format!("h{h} is not bound")));
                };
                let fits = size >= 1 && matches!(binding, Some((s, a)) if s == size && a <= 8);
                if !fits {
                    return Err(fail(
                        "C6",
                        format!(
                            "free_sized h{h} {size} does not directly follow an allocation of exactly {size} bytes at alignment 8 or less"
                        ),
                    ));
                }
            }
            Op::FreeSizedAligned { h, size, align } => {
                let Some(binding) = bound.remove(&h) else {
                    return Err(fail("C2", format!("h{h} is not bound")));
                };
                let fits = size >= 1 && align >= 1 && binding == Some((size, align));
                if !fits {
                    return Err(fail(
                        "C7",
                        format!(
                            "free_sized_aligned h{h} {size} {align} does not directly follow alloc_aligned h{h} {size} {align}"
                        ),
                    ));
                }
            }
            Op::Purge => {}
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ops(text: &str) -> Vec<Op> {
        parse(text)
            .expect("valid trace")
            .into_iter()
            .map(|l| l.op)
            .collect()
    }

    fn rejected(text: &str) -> String {
        parse(text).expect_err("trace must be rejected").to_string()
    }

    #[test]
    fn parses_every_operation_and_renders_it_canonically() {
        let text = "oris-trace 1\n# comment\n\nalloc h0 24\nalloc_aligned h1 100 64\n\
                    calloc h2 4 8\nrealloc h0 300\nrealloc_aligned h1 400 64\nresize h0 200\n\
                    size h0\nfree h0\nfree_sized h2 32\nfree h1\nalloc h3 7\nfree_sized h3 7\n\
                    alloc_aligned h4 300 512\nfree_sized_aligned h4 300 512\npurge\n";
        let rendered: Vec<String> = ops(text).iter().map(ToString::to_string).collect();
        let expected: Vec<&str> = text.lines().skip(3).collect();
        assert_eq!(rendered, expected);
    }

    #[test]
    fn accepts_tabs_runs_of_spaces_crlf_and_a_missing_final_eol() {
        let parsed = ops("oris-trace 1\r\n\t alloc \th0   24 \r\n  # indented comment\r\nfree h0");
        assert_eq!(parsed, [Op::Alloc { h: 0, size: 24 }, Op::Free { h: 0 }]);
    }

    #[test]
    fn rejects_bad_syntax_with_its_line_number() {
        assert!(rejected("").contains("line 1"));
        assert!(rejected("oris-trace 2\n").contains("header"));
        assert!(rejected("oris-trace 1\nalloc h0\n").contains("line 2"));
        assert!(rejected("oris-trace 1\nalloc h0 024\n").contains("`024`"));
        assert!(rejected("oris-trace 1\nalloc x0 24\n").contains("handle"));
        assert!(rejected("oris-trace 1\n\nmalloc h0 24\n").contains("line 3"));
        assert!(rejected("oris-trace 1\nalloc h0 18446744073709551616\n").contains("64 bits"));
        assert!(rejected("oris-trace 1\npurge now\n").contains("argument"));
    }

    #[test]
    fn enforces_every_semantic_constraint() {
        let cases = [
            ("alloc h0 8\nalloc h0 8", "C1"),
            ("free h0", "C2"),
            ("alloc h0 8\nfree h0\nfree h0", "C2"),
            ("alloc_aligned h0 8 3", "C3"),
            ("alloc_aligned h0 8 131072", "C3"),
            ("alloc h0 1073741825", "C4"),
            ("calloc h0 1073741824 2", "C4"),
            ("calloc h0 4294967296 4294967296", "C4"),
            ("alloc h0 8\nresize h0 0", "C5"),
            ("alloc h0 100\nrealloc h0 20\nfree_sized h0 20", "C6"),
            ("alloc h0 100\nfree_sized h0 64", "C6"),
            ("alloc h0 0\nfree_sized h0 0", "C6"),
            ("alloc_aligned h0 5 4096\nfree_sized h0 5", "C6"),
            ("alloc_aligned h0 64 16\nfree_sized_aligned h0 64 32", "C7"),
            ("alloc h0 64\nfree_sized_aligned h0 64 8", "C7"),
            ("realloc_aligned h0 100 512", "C8"),
        ];
        for (body, rule) in cases {
            let message = rejected(&format!("oris-trace 1\n{body}\n"));
            assert!(
                message.contains(rule),
                "{body:?}: expected {rule}, got {message}"
            );
        }
    }

    #[test]
    fn accepts_the_boundaries_of_every_constraint() {
        let text = "oris-trace 1\nalloc h0 1073741824\nfree h0\nalloc_aligned h1 8 65536\n\
                    free_sized_aligned h1 8 65536\nalloc_aligned h2 8 0\nfree_sized h2 8\n\
                    calloc h3 2 12\nfree_sized h3 24\nrealloc h4 10\nrealloc h4 0\nsize h4\n\
                    free h4\nrealloc_aligned h5 257 512\nresize h5 1\nfree h5\nalloc h0 0\nfree h0\n";
        assert_eq!(ops(text).len(), 17);
    }
}
