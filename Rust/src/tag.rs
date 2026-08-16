// SPDX-License-Identifier: MIT OR Apache-2.0
//! Tagged-pointer helper for the intrusive red-black tree's parent link.
//!
//! Ports `Cpp/hpha.h`'s `ptr_bits<node_base, 2>` — HPHA's mechanism for storing a
//! red-black tree node's colour and which side of its parent it hangs from inside the
//! low two bits of the parent pointer itself, so the tree's per-node overhead stays at
//! exactly `children[2] + neighbours[2] + parent`, with no separate colour/side fields.
//!
//! The two bits are only ever meaningful while the pointer is non-dangling: every
//! red-black tree node has `align_of >= size_of::<usize>()` (it embeds a `usize` field
//! alongside its pointers), which is at least 4 on every platform this crate targets, so
//! bits 0 and 1 of a valid node address are always zero before tagging.

use core::marker::PhantomData;

const TAG_MASK: usize = 0b11;

/// Bit 0 of the tagged parent pointer: the node's red-black colour (see `rbtree::Colour`).
pub(crate) const BIT_COLOUR: usize = 0;
/// Bit 1 of the tagged parent pointer: which of the parent's two children this node is
/// (see `rbtree::Side`).
pub(crate) const BIT_SIDE: usize = 1;

/// A `*mut T` with two tag bits packed into its low bits.
///
/// **Nullable, unlike most pointers in this crate.** HPHA's `ptr_bits<node_base, 2>` —
/// which this ports — allows a null wrapped pointer (default-constructed, or explicitly
/// assigned `NULL`), and the red-black tree relies on that: a node chained onto an
/// equal-key group but not the group's tree-attached representative has a literal null
/// `mParent` (`node_base::link`'s `mParent = NULL`), which `node_base::head()` tests
/// directly. `TaggedPtr` therefore wraps `*mut T`, not `NonNull<T>` — the "`NonNull`
/// over raw pointers" rule in `Rust/CONVENTIONS.md` is for pointers that are *never*
/// null in valid allocator state; this one specifically is, by design, sometimes null.
///
/// This is embedded directly as the red-black tree node's `parent` field (`rbtree.rs`),
/// so its layout is part of that node's frozen on-heap ABI — hence `#[repr(transparent)]`
/// rather than the derive-default layout, matching `Rust/CONVENTIONS.md`'s "Repr and
/// Layout Lock" rule for intrusive node fields.
///
/// # Invariants
/// The wrapped pointer's low two bits are always the tag, never part of the address.
#[repr(transparent)]
#[allow(clippy::exhaustive_structs)]
// EXHAUSTIVE: single-field newtype whose one field is this type's entire on-heap
// representation (embedded in the RB-tree node's frozen ABI); not future-extensible.
pub(crate) struct TaggedPtr<T> {
    /// The pointee's address (possibly null) with the two low tag bits OR'd in. Never
    /// dereferenced directly — always cleared via [`TaggedPtr::ptr`] first.
    tagged: *mut T,
    /// Zero-sized; carries `T` in the type without occupying a field, so
    /// `#[repr(transparent)]` still sees exactly one non-ZST field (`tagged`).
    _marker: PhantomData<T>,
}

// Manual Clone/Copy: `#[derive(Clone, Copy)]` would add an implicit `T: Clone`/`T:
// Copy` bound (a well-known derive-macro conservatism), but `tagged: *mut T` is
// `Copy` regardless of `T` — raw pointers never need their pointee to be `Copy`. A
// derived impl here would make `TaggedPtr<NodeBase>` uncopyable, which is wrong (and
// broke the RB-tree's `const fn new()`, which needs to construct one).
impl<T> Clone for TaggedPtr<T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> Copy for TaggedPtr<T> {}

const _: () = assert!(size_of::<TaggedPtr<u8>>() == size_of::<usize>());

impl<T> TaggedPtr<T> {
    /// A `TaggedPtr` wrapping a null pointer with no tag bits set — the `const fn`
    /// path for building an as-yet-unlinked node's `parent` field (`ptr.map_addr` is
    /// not itself a `const fn`, so the general [`TaggedPtr::new`] below cannot be one;
    /// this special case needs no address arithmetic at all).
    #[must_use]
    pub(crate) const fn null() -> Self {
        Self {
            tagged: core::ptr::null_mut(),
            _marker: PhantomData,
        }
    }

    /// Builds a tagged pointer from an untagged, tag-bit-aligned `ptr` (possibly null)
    /// and initial `bits`.
    #[must_use]
    pub(crate) fn new(ptr: *mut T, bits: usize) -> Self {
        debug_assert_eq!(ptr.addr() & TAG_MASK, 0, "pointer not tag-bit aligned");
        debug_assert_eq!(bits & !TAG_MASK, 0, "bits outside the 2-bit tag");
        // TAG: bits [0..2) of ptr's address carry (colour, parent-side).
        // PROVENANCE: `tagged` derives from `ptr`; map_addr keeps `ptr`'s provenance,
        // only the low two address bits change.
        let tagged = ptr.map_addr(|addr| addr | bits);
        Self {
            tagged,
            _marker: PhantomData,
        }
    }

    /// The untagged pointer — null if this `TaggedPtr` wraps a null pointer.
    #[must_use]
    pub(crate) fn ptr(self) -> *mut T {
        // UNTAG: clear bits [0..2) to recover the aligned node address (or null).
        // PROVENANCE: result derives from `self.tagged`; map_addr keeps its
        // provenance, only the low two address bits change.
        self.tagged.map_addr(|addr| addr & !TAG_MASK)
    }

    /// Reads one tag bit (`bit` is [`BIT_COLOUR`] or [`BIT_SIDE`]).
    #[must_use]
    pub(crate) fn bit(self, bit: usize) -> bool {
        (self.tagged.addr() & (1 << bit)) != 0
    }

    /// Sets one tag bit, leaving the pointer and the other bit untouched.
    pub(crate) fn set_bit(&mut self, bit: usize) {
        // TAG: OR in one bit of the two-bit tag; the pointer value is untouched.
        // PROVENANCE: result derives from `self.tagged`; map_addr preserves provenance.
        self.tagged = self.tagged.map_addr(|addr| addr | (1 << bit));
    }

    /// Clears one tag bit, leaving the pointer and the other bit untouched.
    pub(crate) fn clear_bit(&mut self, bit: usize) {
        // UNTAG: clear one bit of the two-bit tag; the pointer value is untouched.
        // PROVENANCE: result derives from `self.tagged`; map_addr preserves provenance.
        self.tagged = self.tagged.map_addr(|addr| addr & !(1 << bit));
    }

    /// Replaces the pointer (possibly null), preserving the current tag bits.
    pub(crate) fn set_ptr(&mut self, ptr: *mut T) {
        debug_assert_eq!(ptr.addr() & TAG_MASK, 0, "pointer not tag-bit aligned");
        let bits = self.tagged.addr() & TAG_MASK;
        // TAG: reapply the preserved (colour, parent-side) bits onto the new pointer.
        // PROVENANCE: `self.tagged` now derives from `ptr`, not the old pointer;
        // map_addr keeps `ptr`'s provenance, only the low two address bits change.
        self.tagged = ptr.map_addr(|addr| addr | bits);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn aligned_ptr(addr: usize) -> *mut u8 {
        // PROVENANCE: test-only sentinel address with no real allocation behind it;
        // TaggedPtr never dereferences, it only packs/unpacks address bits, so an
        // exposed, provenance-free pointer is sound to exercise the bit math with.
        core::ptr::without_provenance_mut::<u8>(addr)
    }

    #[test]
    fn new_and_ptr_roundtrip_with_no_bits() {
        let p = aligned_ptr(0x1000);
        let t = TaggedPtr::new(p, 0);
        assert_eq!(t.ptr(), p);
        assert!(!t.bit(BIT_COLOUR));
        assert!(!t.bit(BIT_SIDE));
    }

    #[test]
    fn new_packs_initial_bits() {
        let p = aligned_ptr(0x2000);
        let t = TaggedPtr::new(p, 0b11);
        assert_eq!(t.ptr(), p);
        assert!(t.bit(BIT_COLOUR));
        assert!(t.bit(BIT_SIDE));
    }

    #[test]
    fn set_and_clear_bit_independent() {
        let p = aligned_ptr(0x3000);
        let mut t = TaggedPtr::new(p, 0);
        t.set_bit(BIT_COLOUR);
        assert!(t.bit(BIT_COLOUR));
        assert!(!t.bit(BIT_SIDE));
        t.set_bit(BIT_SIDE);
        assert!(t.bit(BIT_COLOUR));
        assert!(t.bit(BIT_SIDE));
        t.clear_bit(BIT_COLOUR);
        assert!(!t.bit(BIT_COLOUR));
        assert!(t.bit(BIT_SIDE));
        assert_eq!(t.ptr(), p);
    }

    #[test]
    fn set_ptr_preserves_tag_bits() {
        let p1 = aligned_ptr(0x4000);
        let p2 = aligned_ptr(0x5000);
        let mut t = TaggedPtr::new(p1, BIT_SIDE_MASK);
        t.set_ptr(p2);
        assert_eq!(t.ptr(), p2);
        assert!(!t.bit(BIT_COLOUR));
        assert!(t.bit(BIT_SIDE));
    }

    #[test]
    fn null_pointer_roundtrips_with_bits() {
        // The whole reason TaggedPtr wraps *mut T instead of NonNull<T> — see the
        // type's doc comment: a red-black tree node's tagged parent link is null when
        // the node is chained but not its equal-key group's tree-attached member.
        let mut t = TaggedPtr::<u8>::new(core::ptr::null_mut(), 0);
        assert!(t.ptr().is_null());
        t.set_bit(BIT_COLOUR);
        assert!(t.ptr().is_null());
        assert!(t.bit(BIT_COLOUR));
    }

    const BIT_SIDE_MASK: usize = 1 << BIT_SIDE;
}
