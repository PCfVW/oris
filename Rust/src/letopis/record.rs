// SPDX-License-Identifier: MIT OR Apache-2.0
//! Writing the transition record (`examples/traces/GRAMMAR.md` §2): normalizing every raw
//! address an [`Event`] carries into `m<id>+0x<offset>`, and rendering each event line.
//!
//! The normalizer replays the `map`/`unmap` events in order to know, at each moment,
//! which mappings are live and which id each one got — the same bookkeeping, in the same
//! order, as `orisnitsa`'s `letopis_record.zig` and the C++ oracle's `trace_replay.cpp`.

use super::ReplayError;
use super::event::{Event, MapKind};
use crate::rbtree::{EraseKind, InsertKind};
use core::fmt::Write;
use std::collections::BTreeMap;

/// A live mapping: its length and the id it was given.
#[derive(Clone, Copy)]
struct Mapping {
    bytes: usize,
    id: u64,
}

/// The live mappings of one replay, keyed by base address, and the run's totals.
#[derive(Default)]
pub(crate) struct Normalizer {
    /// Live mappings by base address.
    live: BTreeMap<usize, Mapping>,
    /// The id the next mapping gets.
    next_id: u64,
    /// Mappings made so far.
    pub(crate) maps: u64,
    /// Mappings returned so far.
    pub(crate) unmaps: u64,
    /// Rotations reported by `tree+`/`tree-` events so far.
    pub(crate) rotations: u64,
}

impl Normalizer {
    /// Renders `addr` as `m<id>+0x<offset>`.
    ///
    /// # Errors
    /// [`ReplayError::Unmapped`] if no live mapping contains `addr` — a hook reporting
    /// memory the allocator never mapped, which is a bug in the hooks, not in the trace.
    pub(crate) fn location(&self, addr: usize) -> Result<String, ReplayError> {
        let (id, offset) = self.resolve(addr)?;
        Ok(format!("m{id}+{offset:#x}"))
    }

    /// The id of the live mapping containing `addr`.
    fn mapping(&self, addr: usize) -> Result<u64, ReplayError> {
        self.resolve(addr).map(|(id, _)| id)
    }

    fn resolve(&self, addr: usize) -> Result<(u64, usize), ReplayError> {
        let (&base, mapping) = self
            .live
            .range(..=addr)
            .next_back()
            .ok_or(ReplayError::Unmapped { address: addr })?;
        let offset = addr - base;
        if offset >= mapping.bytes {
            return Err(ReplayError::Unmapped { address: addr });
        }
        Ok((mapping.id, offset))
    }

    /// Renders one event line (without its indentation), updating the live-mapping table
    /// and the totals as it goes.
    ///
    /// # Errors
    /// [`ReplayError::Unmapped`] if the event names memory no live mapping contains.
    pub(crate) fn event_line(&mut self, event: Event) -> Result<String, ReplayError> {
        let mut line = String::new();
        // `write!` into a `String` cannot fail; the results below are discarded for that
        // reason, not ignored by accident.
        match event {
            Event::Map { kind, base, bytes } => {
                let id = self.next_id;
                self.next_id += 1;
                self.maps += 1;
                self.live.insert(base, Mapping { bytes, id });
                let kind = match kind {
                    MapKind::Bucket => 'b',
                    MapKind::Tree => 't',
                };
                let _ = write!(line, "map {kind} m{id} {bytes}");
            }
            Event::Unmap { base, bytes } => {
                // An unmap names a whole mapping, by its base exactly.
                let id = self
                    .live
                    .remove(&base)
                    .ok_or(ReplayError::Unmapped { address: base })?
                    .id;
                self.unmaps += 1;
                let _ = write!(line, "unmap m{id} {bytes}");
            }
            Event::PageSpawn { bucket, page } => {
                let _ = write!(line, "page+ b{bucket} m{}", self.mapping(page)?);
            }
            Event::PageRelease { bucket, page } => {
                let _ = write!(line, "page- b{bucket} m{}", self.mapping(page)?);
            }
            Event::PageFull { bucket, page } => {
                let _ = write!(line, "page-full b{bucket} m{}", self.mapping(page)?);
            }
            Event::PageRefill { bucket, page } => {
                let _ = write!(line, "page-refill b{bucket} m{}", self.mapping(page)?);
            }
            Event::Split { block, size } => {
                let _ = write!(line, "split {} {size}", self.location(block)?);
            }
            Event::Shift { block, offset } => {
                let _ = write!(line, "shift {} {offset}", self.location(block)?);
            }
            Event::Merge { block } => {
                let _ = write!(line, "merge {}", self.location(block)?);
            }
            Event::TreeInsert {
                block,
                size,
                kind,
                rotations,
            } => {
                self.rotations += u64::from(rotations);
                let kind = match kind {
                    InsertKind::Chain => "chain",
                    InsertKind::Node => "node",
                };
                let block = self.location(block)?;
                let _ = write!(line, "tree+ {block} {size} {kind} rot={rotations}");
            }
            Event::TreeErase {
                block,
                size,
                kind,
                rotations,
            } => {
                self.rotations += u64::from(rotations);
                let kind = match kind {
                    EraseKind::Link => "link",
                    EraseKind::Promote => "promote",
                    EraseKind::Node => "node",
                };
                let block = self.location(block)?;
                let _ = write!(line, "tree- {block} {size} {kind} rot={rotations}");
            }
            Event::ListPush { block, size } => {
                let _ = write!(line, "list+ {} {size}", self.location(block)?);
            }
            Event::ListErase { block, size } => {
                let _ = write!(line, "list- {} {size}", self.location(block)?);
            }
            Event::Mr { block: Some(block) } => {
                let _ = write!(line, "mr {}", self.location(block)?);
            }
            Event::Mr { block: None } => line.push_str("mr -"),
        }
        Ok(line)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ids_follow_map_order_and_are_never_reused() {
        let mut norm = Normalizer::default();
        let map = |base, kind| Event::Map {
            kind,
            base,
            bytes: 0x1_0000,
        };
        assert_eq!(
            norm.event_line(map(0x30_0000, MapKind::Bucket))
                .ok()
                .as_deref(),
            Some("map b m0 65536")
        );
        assert_eq!(
            norm.event_line(map(0x10_0000, MapKind::Tree))
                .ok()
                .as_deref(),
            Some("map t m1 65536")
        );
        assert_eq!(norm.location(0x30_0018).ok().as_deref(), Some("m0+0x18"));
        assert_eq!(norm.location(0x10_0000).ok().as_deref(), Some("m1+0x0"));
        let unmap = Event::Unmap {
            base: 0x30_0000,
            bytes: 0x1_0000,
        };
        assert_eq!(
            norm.event_line(unmap).ok().as_deref(),
            Some("unmap m0 65536")
        );
        assert!(norm.location(0x30_0018).is_err());
        // The same base mapped again is a new mapping with a new id.
        assert_eq!(
            norm.event_line(map(0x30_0000, MapKind::Bucket))
                .ok()
                .as_deref(),
            Some("map b m2 65536")
        );
        assert!(
            norm.location(0x11_0000).is_err(),
            "one past the end is outside"
        );
        assert_eq!((norm.maps, norm.unmaps), (3, 1));
    }

    #[test]
    fn renders_every_event_kind() {
        let mut norm = Normalizer::default();
        let base = 0x7f00_0000;
        let _ = norm.event_line(Event::Map {
            kind: MapKind::Tree,
            base,
            bytes: 0x2_0000,
        });
        let cases = [
            (
                Event::PageSpawn {
                    bucket: 2,
                    page: base + 0xffe0,
                },
                "page+ b2 m0",
            ),
            (
                Event::PageRelease {
                    bucket: 31,
                    page: base,
                },
                "page- b31 m0",
            ),
            (
                Event::PageFull {
                    bucket: 0,
                    page: base,
                },
                "page-full b0 m0",
            ),
            (
                Event::PageRefill {
                    bucket: 1,
                    page: base,
                },
                "page-refill b1 m0",
            ),
            (
                Event::Split {
                    block: base + 0x20,
                    size: 1008,
                },
                "split m0+0x20 1008",
            ),
            (
                Event::Shift {
                    block: base + 0x40,
                    offset: 16,
                },
                "shift m0+0x40 16",
            ),
            (
                Event::Merge {
                    block: base + 0x1_0000,
                },
                "merge m0+0x10000",
            ),
            (
                Event::TreeInsert {
                    block: base + 0x20,
                    size: 300,
                    kind: InsertKind::Chain,
                    rotations: 0,
                },
                "tree+ m0+0x20 300 chain rot=0",
            ),
            (
                Event::TreeErase {
                    block: base + 0x20,
                    size: 300,
                    kind: EraseKind::Promote,
                    rotations: 2,
                },
                "tree- m0+0x20 300 promote rot=2",
            ),
            (
                Event::ListPush {
                    block: base + 0x30,
                    size: 48,
                },
                "list+ m0+0x30 48",
            ),
            (
                Event::ListErase {
                    block: base + 0x30,
                    size: 48,
                },
                "list- m0+0x30 48",
            ),
            (
                Event::Mr {
                    block: Some(base + 0x30),
                },
                "mr m0+0x30",
            ),
            (Event::Mr { block: None }, "mr -"),
        ];
        for (event, expected) in cases {
            assert_eq!(norm.event_line(event).ok().as_deref(), Some(expected));
        }
        assert_eq!(norm.rotations, 2);
    }
}
