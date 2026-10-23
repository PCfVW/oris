// SPDX-License-Identifier: MIT OR Apache-2.0
//! `tracegen`: seeded, reproducible allocation traces for Oris (`examples/traces/GRAMMAR.md`).
//!
//! ```text
//! cargo run --release -- generate            # CI corpus + bench traces + checksums
//! cargo run --release -- verify              # nothing drifted
//! ```
//!
//! Run from this directory: the default paths are relative to it. See `README.md`.

mod builder;
mod config;
mod workloads;

use anyhow::{Context, Result, bail};
use clap::{Parser, Subcommand, ValueEnum};
use config::{Spec, Tier};
use sha2::{Digest, Sha256};
use std::fmt::Write as _;
use std::path::{Path, PathBuf};

#[derive(Parser)]
#[command(
    name = "tracegen",
    about = "Seeded, reproducible allocation traces for Oris",
    version
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Clone, Copy, PartialEq, Eq, ValueEnum)]
enum Which {
    Ci,
    Bench,
    All,
}

#[derive(Subcommand)]
enum Command {
    /// Generate the traces declared in the config file.
    Generate {
        /// Path to traces.toml.
        #[arg(long, default_value = "../../traces.toml")]
        config: PathBuf,
        /// Which tier to generate.
        #[arg(long, value_enum, default_value = "all")]
        tier: Which,
        /// Where CI-tier traces go (committed, with their records).
        #[arg(long, default_value = "../../../examples/traces/generated")]
        ci_out: PathBuf,
        /// Where bench-tier traces go (not committed).
        #[arg(long, default_value = "../../traces")]
        bench_out: PathBuf,
        /// The checksum file for bench-tier traces (committed).
        #[arg(long, default_value = "../../trace-checksums.txt")]
        checksums: PathBuf,
    },
    /// Check that nothing drifted: every committed CI trace is byte-identical to what the
    /// config generates, and every bench trace hashes to its committed checksum.
    Verify {
        #[arg(long, default_value = "../../traces.toml")]
        config: PathBuf,
        #[arg(long, default_value = "../../../examples/traces/generated")]
        ci_dir: PathBuf,
        #[arg(long, default_value = "../../trace-checksums.txt")]
        checksums: PathBuf,
    },
}

/// A `fmt::Write` that keeps nothing: validation replays a trace for its verdict only.
struct Discard;

impl std::fmt::Write for Discard {
    fn write_str(&mut self, _: &str) -> std::fmt::Result {
        Ok(())
    }
}

/// Generates `spec`'s trace and replays it through `orisnik`, so a trace the replayers
/// would reject is never written.
fn build_checked(spec: &Spec) -> Result<String> {
    let trace = workloads::build(spec)?;
    orisnik::letopis::replay(&trace, &mut Discard)
        .with_context(|| format!("{}: the generated trace does not replay", spec.name))?;
    Ok(trace)
}

fn sha256_hex(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .fold(String::new(), |mut s, b| {
            let _ = write!(s, "{b:02x}");
            s
        })
}

fn wanted(which: Which, tier: Tier) -> bool {
    matches!(
        (which, tier),
        (Which::All, _) | (Which::Ci, Tier::Ci) | (Which::Bench, Tier::Bench)
    )
}

fn write(path: &Path, text: &str) -> Result<()> {
    if let Some(dir) = path.parent() {
        std::fs::create_dir_all(dir)
            .with_context(|| format!("failed to create {}", dir.display()))?;
    }
    std::fs::write(path, text).with_context(|| format!("failed to write {}", path.display()))
}

fn main() -> Result<()> {
    match Cli::parse().command {
        Command::Generate {
            config,
            tier,
            ci_out,
            bench_out,
            checksums,
        } => {
            let cfg = config::load(&config)?;
            let mut sums = String::new();
            for spec in &cfg.trace {
                if !wanted(tier, spec.tier) {
                    continue;
                }
                let trace = build_checked(spec)?;
                let dir = match spec.tier {
                    Tier::Ci => &ci_out,
                    Tier::Bench => &bench_out,
                };
                let path = dir.join(format!("{}.trace", spec.name));
                write(&path, &trace)?;
                let sum = sha256_hex(trace.as_bytes());
                if spec.tier == Tier::Bench {
                    let _ = writeln!(sums, "{sum}  {}.trace", spec.name);
                }
                let ops = trace.lines().filter(|l| !l.starts_with('#')).count() - 1;
                println!("wrote {}: {ops} ops, sha256 {sum}", path.display());
            }
            if wanted(tier, Tier::Bench) {
                write(&checksums, &sums)?;
                println!("wrote {}", checksums.display());
            }
            Ok(())
        }
        Command::Verify {
            config,
            ci_dir,
            checksums,
        } => {
            let cfg = config::load(&config)?;
            let committed = std::fs::read_to_string(&checksums)
                .with_context(|| format!("failed to read {}", checksums.display()))?;
            let mut problems = Vec::new();
            for spec in &cfg.trace {
                let trace = build_checked(spec)?;
                let ok = match spec.tier {
                    Tier::Ci => {
                        let path = ci_dir.join(format!("{}.trace", spec.name));
                        let on_disk = std::fs::read_to_string(&path)
                            .with_context(|| format!("failed to read {}", path.display()))?;
                        on_disk == trace
                    }
                    Tier::Bench => {
                        let line = format!("{}  {}.trace", sha256_hex(trace.as_bytes()), spec.name);
                        committed.lines().any(|l| l == line)
                    }
                };
                println!("{}: {}", spec.name, if ok { "ok" } else { "DRIFT" });
                if !ok {
                    problems.push(spec.name.clone());
                }
            }
            if !problems.is_empty() {
                bail!(
                    "{} trace(s) differ from what the config generates: {} (regenerate with \
                     `tracegen generate`, then the records with the C++ oracle — see README.md)",
                    problems.len(),
                    problems.join(", ")
                );
            }
            Ok(())
        }
    }
}
