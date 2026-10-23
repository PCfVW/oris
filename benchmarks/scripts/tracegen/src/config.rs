// SPDX-License-Identifier: MIT OR Apache-2.0
//! `benchmarks/traces.toml`: one `[[trace]]` table per generated trace.

use crate::workloads::synthetic::Profile;
use anyhow::{Context, Result, bail};
use serde::Deserialize;
use std::collections::HashSet;
use std::path::Path;

/// The whole file.
#[derive(Deserialize)]
pub struct Config {
    /// Every trace, in file order.
    pub trace: Vec<Spec>,
}

/// One generated trace.
#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Spec {
    /// File stem: the trace is written to `<name>.trace`.
    pub name: String,
    /// Which generator.
    pub workload: Workload,
    /// For `synthetic` only: which profile.
    pub profile: Option<Profile>,
    /// The `ChaCha8Rng` seed.
    pub seed: u64,
    /// The minimum number of operations (a generator finishes the step it is in).
    pub ops: u64,
    /// Where the trace goes.
    pub tier: Tier,
}

impl Spec {
    /// `planner`, `parser`, or `synthetic/<profile>`, for the trace's header comment.
    pub fn workload_label(&self) -> String {
        match (self.workload, self.profile) {
            (Workload::Synthetic, Some(p)) => {
                format!("synthetic/{}", format!("{p:?}").to_lowercase())
            }
            (w, _) => format!("{w:?}").to_lowercase(),
        }
    }
}

/// The generators.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Workload {
    Planner,
    Parser,
    Synthetic,
}

/// What a trace is for.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Tier {
    /// Committed under `examples/traces/generated/` with its transition record, and
    /// replayed by every implementation in CI.
    Ci,
    /// Generated on demand for the benchmarks; only its SHA-256 is committed.
    Bench,
}

/// Reads and checks `path`.
pub fn load(path: &Path) -> Result<Config> {
    let text = std::fs::read_to_string(path)
        .with_context(|| format!("failed to read {}", path.display()))?;
    let config: Config =
        toml::from_str(&text).with_context(|| format!("failed to parse {}", path.display()))?;
    let mut names = HashSet::new();
    for spec in &config.trace {
        if !names.insert(spec.name.as_str()) {
            bail!("duplicate trace name `{}`", spec.name);
        }
        if (spec.workload == Workload::Synthetic) != spec.profile.is_some() {
            bail!(
                "{}: `profile` goes with `workload = \"synthetic\"`, and only with it",
                spec.name
            );
        }
    }
    Ok(config)
}
