// SPDX-License-Identifier: MIT OR Apache-2.0
//! The workload generators. Each writes operations into a [`TraceBuilder`] until it holds
//! the requested count, drawing every choice from one seeded `ChaCha8Rng`.

pub mod parser;
pub mod planner;
pub mod synthetic;

use crate::builder::TraceBuilder;
use crate::config::{Spec, Workload};
use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;

/// The trace `spec` describes: a pure function of the spec (and of this crate's pinned
/// `rand`/`rand_chacha` versions).
pub fn build(spec: &Spec) -> anyhow::Result<String> {
    let mut rng = ChaCha8Rng::seed_from_u64(spec.seed);
    let mut trace = TraceBuilder::new(&format!(
        "tracegen: {} (workload={}, seed={}, ops={})",
        spec.name,
        spec.workload_label(),
        spec.seed,
        spec.ops
    ));
    match spec.workload {
        Workload::Planner => planner::generate(&mut trace, &mut rng, spec.ops),
        Workload::Parser => parser::generate(&mut trace, &mut rng, spec.ops),
        Workload::Synthetic => {
            let profile = spec.profile.ok_or_else(|| {
                anyhow::anyhow!("{}: a synthetic trace needs a `profile`", spec.name)
            })?;
            synthetic::generate(&mut trace, &mut rng, spec.ops, profile);
        }
    }
    Ok(trace.finish())
}
