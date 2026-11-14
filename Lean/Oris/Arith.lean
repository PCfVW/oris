-- SPDX-License-Identifier: MIT OR Apache-2.0
/-!
# Tier 0 — the size arithmetic of `orisnik`

Models, on 64-bit machine words (`BitVec 64`, i.e. Rust's `usize` on the 64-bit targets the
crate is restricted to by `block.rs`'s compile-time assertion `usize::BITS == 64`), the size
arithmetic of the tree path's normalization and growth and of the bucket size classes:

| Lean | Rust |
|---|---|
| `roundUp` | `align.rs` `round_up` |
| `normalizeSize`, `MAX_ALLOCATION` | `tree.rs` `normalize_size`, `MAX_ALLOCATION` |
| `growSize` | `tree.rs` `Tree::grow` (its two size lines) |
| `bucketSpacing`, `bucketSpacingAligned`, `bucketSpacingInverse` | `bucket.rs` `bucket_spacing_function`, `_aligned`, `_inverse` |
| `clampSmall`, `isSmall` | `bucket.rs` `clamp_small_allocation`, `is_small_allocation` |
| `hphaMask`, `hphaRoundUp` | `Cpp/hpha.h` `round_up` and its mask `-(int)a` |

`alloc_aligned`'s guard is stated directly on its expression (`alloc_aligned_guard`). Not
modelled yet: `extract_aligned`'s alignment offsets and the split threshold
(`SPLIT_REMAINDER_MIN`), which belong with the memory-management tier.

Each definition transcribes the Rust expression operator for operator. Rust's `+`/`-` on `usize`
panic on overflow in debug builds and wrap in release builds; `BitVec` wraps. So every theorem
about a transcribed computation that adds or subtracts comes in two halves: *the operation does
not overflow* (so debug builds never panic and the wrapped value is the mathematical one), and
*the mathematical value is what the caller needs*. (The rest, such as `hphaMask_eq` or
`bucketSpacing_inverse`, are plain equations.)

Layout constants: `BLOCK_HEADER = 16` and `FREE_NODE = 40` are the values of the Rust's
compile-time assertions `size_of::<BlockHeader>() == 2 * size_of::<usize>()` (`block.rs`) and
`size_of::<NodeBase>() == 5 * size_of::<usize>()` (`rbtree.rs`; `FreeNode` is `#[repr(C)]` with
`NodeBase` as its only field) on 64-bit `usize`; `PAGE_SIZE = 65536` is `os.rs`'s constant
`PAGE_SIZE`, fixed at 64 KiB on every platform.
-/

namespace Oris.Arith

/-- Rust's `usize` on the crate's 64-bit-only targets. -/
abbrev Usize := BitVec 64

/-- `size_of::<BlockHeader>()`. -/
def BLOCK_HEADER : Usize := 16
/-- `size_of::<FreeNode>()` = `size_of::<NodeBase>()` = `MIN_BLOCK_SIZE`. -/
def FREE_NODE : Usize := 40
/-- `os::PAGE_SIZE`. -/
def PAGE_SIZE : Usize := 65536

/-- `align.rs` `round_up`: `(value + (align - 1)) & !(align - 1)`. -/
def roundUp (value align : Usize) : Usize := (value + (align - 1)) &&& ~~~(align - 1)

/-! ## `round_up` -/

/-- The mask `!(2^k - 1)` keeps exactly the multiple of `2^k` below `x`. -/
theorem and_not_two_pow_sub_one (x : Usize) (k : Nat) (hk : k < 64) :
    (x &&& ~~~(BitVec.ofNat 64 (2^k - 1))).toNat = x.toNat / 2^k * 2^k := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  simp only [BitVec.toNat_and, BitVec.toNat_not, Nat.testBit_and, BitVec.toNat_ofNat]
  have hpk : 2^k ≤ 2^63 := Nat.pow_le_pow_right (by decide) (by omega)
  have h1 : (2^k - 1) % 2^64 = 2^k - 1 := Nat.mod_eq_of_lt (by omega)
  have h64 : (2:Nat)^64 = 2^(64-k) * 2^k := by rw [← Nat.pow_add]; congr 1; omega
  have h2 : 2^64 - 1 - (2^k - 1) = (2^(64-k) - 1) * 2^k := by
    rw [h64, Nat.sub_mul, Nat.one_mul]
    have : 1 ≤ 2^k := Nat.one_le_two_pow
    have : 2^k ≤ 2^(64-k) * 2^k := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    omega
  rw [h1, h2, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases hki : k ≤ i
  · have e : i - k + k = i := by omega
    rw [e]
    by_cases hi : i < 64
    · simp [hki, show i - k < 64 - k by omega]
    · have : x.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [hki]

/-- `round_up` computes the mathematical round-up whenever its one addition does not overflow
(which is also exactly when a debug build does not panic). -/
theorem roundUp_toNat (v : Usize) (k : Nat) (hk : k < 64) (h : v.toNat + (2^k - 1) < 2^64) :
    (roundUp v (BitVec.ofNat 64 (2^k))).toNat = (v.toNat + (2^k - 1)) / 2^k * 2^k := by
  have hpk : 2^k ≤ 2^63 := Nat.pow_le_pow_right (by decide) (by omega)
  have hpos : 0 < 2^k := Nat.two_pow_pos k
  have hsub : BitVec.ofNat 64 (2^k) - 1 = BitVec.ofNat 64 (2^k - 1) := by
    apply BitVec.eq_of_toNat_eq
    have h1 : (1 : Usize).toNat = 1 := rfl
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
    rw [Nat.mod_eq_of_lt (by omega : 2^k < 2^64), Nat.mod_eq_of_lt (by omega : 2^k - 1 < 2^64)]
    omega
  unfold roundUp
  rw [hsub, and_not_two_pow_sub_one _ k hk]
  congr 2
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : 2^k - 1 < 2^64)]
  exact Nat.mod_eq_of_lt h

/-- What every caller of `round_up` relies on: the result is a multiple of the alignment, at
least the input, and less than one alignment step above it. -/
theorem roundUp_spec (v : Usize) (k : Nat) (hk : k < 64) (h : v.toNat + (2^k - 1) < 2^64) :
    let r := (roundUp v (BitVec.ofNat 64 (2^k))).toNat
    r % 2^k = 0 ∧ v.toNat ≤ r ∧ r < v.toNat + 2^k := by
  intro r
  have e : r = (v.toNat + (2^k - 1)) / 2^k * 2^k := roundUp_toNat v k hk h
  have hpos : 0 < 2^k := Nat.two_pow_pos k
  have h1 := Nat.div_mul_le_self (v.toNat + (2^k - 1)) (2^k)
  have h2 := Nat.lt_div_mul_add (a := v.toNat + (2^k - 1)) hpos
  refine ⟨by rw [e]; exact Nat.mul_mod_left _ _, by omega, by omega⟩

/-! ## `round_up` agrees with HPHA's -/

/-- HPHA's mask, `-(int)a` converted to `size_t`: the negation happens in 32-bit `int`, and the
conversion to the 64-bit `size_t` sign-extends. -/
def hphaMask (a : Usize) : Usize := (-(a.truncate 32)).signExtend 64

/-- For every power-of-two alignment up to `2^30`, HPHA's mask is the port's `!(a - 1)`, so
`round_up` is a faithful port there. (At `a = 2^31` HPHA's `(int)a` is `INT_MIN` and `-INT_MIN`
is undefined behaviour in C++; the port's mask stays correct up to `2^63`.) -/
theorem hphaMask_eq : ∀ k : Fin 31,
    hphaMask (BitVec.ofNat 64 (2^k.val)) = ~~~(BitVec.ofNat 64 (2^k.val) - 1) := by
  decide

/-- `Cpp/hpha.h` `round_up`, with its own mask: `(x + (a-1)) & -(int)a`. -/
def hphaRoundUp (x a : Usize) : Usize := (x + (a - 1)) &&& hphaMask a

/-! ## `normalize_size` and `MAX_ALLOCATION` -/

/-- `tree.rs` `MAX_ALLOCATION`:
`usize::MAX - PAGE_SIZE - 3 * size_of::<BlockHeader>() - size_of::<BlockHeader>()`. -/
def MAX_ALLOCATION : Usize := BitVec.allOnes 64 - PAGE_SIZE - 3 * BLOCK_HEADER - BLOCK_HEADER

theorem MAX_ALLOCATION_toNat : MAX_ALLOCATION.toNat = 2^64 - 1 - 65536 - 48 - 16 := by decide

/-- `tree.rs` `normalize_size`. -/
def normalizeSize (size : Usize) : Option Usize :=
  if size > MAX_ALLOCATION then none
  else
    let size := if size < FREE_NODE then FREE_NODE else size
    some (roundUp size BLOCK_HEADER)

/-- The clamped size `normalize_size` hands to `round_up`, as a natural number. -/
private theorem clamp_toNat (size : Usize) :
    (if size < FREE_NODE then FREE_NODE else size).toNat = max size.toNat 40 := by
  have : FREE_NODE.toNat = 40 := by decide
  split <;> rename_i h <;> rw [BitVec.lt_def] at h <;> omega

/-- **ERRATA E1, port side.** Every request at or below `MAX_ALLOCATION` normalizes without
overflow to a block size that is a multiple of 16, at least the request, at least
`MIN_BLOCK_SIZE` (room for a `FreeNode` once free), and at most 15 bytes of rounding above the
clamped request. Every request above it is rejected. -/
theorem normalizeSize_spec (size : Usize) :
    (size.toNat ≤ MAX_ALLOCATION.toNat →
      ∃ n, normalizeSize size = some n ∧
        max size.toNat 40 + 15 < 2^64 ∧
        n.toNat % 16 = 0 ∧ size.toNat ≤ n.toNat ∧ 40 ≤ n.toNat ∧
        n.toNat < max size.toNat 40 + 16) ∧
    (MAX_ALLOCATION.toNat < size.toNat → normalizeSize size = none) := by
  rw [MAX_ALLOCATION_toNat]
  constructor
  · intro h
    have hnot : ¬ size > MAX_ALLOCATION := by
      rw [gt_iff_lt, BitVec.lt_def, MAX_ALLOCATION_toNat]; omega
    refine ⟨_, by simp only [normalizeSize, hnot]; rfl, ?_⟩
    have hc := clamp_toNat size
    have hb : BLOCK_HEADER = BitVec.ofNat 64 (2^4) := by decide
    have hfit : (if size < FREE_NODE then FREE_NODE else size).toNat + (2^4 - 1) < 2^64 := by
      rw [hc]; omega
    obtain ⟨m, ge, lt⟩ := roundUp_spec _ 4 (by decide) hfit
    rw [hb]
    rw [hc] at ge lt
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩
  · intro h
    have : size > MAX_ALLOCATION := by rw [gt_iff_lt, BitVec.lt_def, MAX_ALLOCATION_toNat]; omega
    simp [normalizeSize, this]

/-- **ERRATA E1, HPHA side.** HPHA's unchecked normalization of `SIZE_MAX`
(`if (size < sizeof(free_node)) ...; size = round_up(size, sizeof(block_header))`), computed with
HPHA's own `round_up` and mask, wraps to a block size of **zero**, exactly as the register says. -/
theorem hpha_normalize_SIZE_MAX :
    hphaRoundUp (BitVec.allOnes 64) BLOCK_HEADER = 0 := by decide

/-! ## `Tree::grow` -/

/-- `tree.rs` `Tree::grow`'s arena size: `round_up(size + 3 * size_of::<BlockHeader>(),
PAGE_SIZE)`. -/
def growSize (size : Usize) : Usize := roundUp (size + 3 * BLOCK_HEADER) PAGE_SIZE

/-- `grow` never overflows for any size the tree path can hand it, and maps a whole number of
pages with room for the block plus its two fences and fake header. "Any size the tree path can
hand it" covers both callers: `alloc` passes a normalized size (below `MAX_ALLOCATION + 16`, by
`normalizeSize_spec`; `alloc_sizes_no_overflow` composes the two), and `alloc_aligned` passes
`size + alignment` only after checking `size ≤ MAX_ALLOCATION - alignment` (see
`alloc_aligned_guard`). -/
theorem growSize_spec (size : Usize) (h : size.toNat ≤ MAX_ALLOCATION.toNat + 16) :
    size.toNat + 48 + (2^16 - 1) < 2^64 ∧
    (growSize size).toNat % 65536 = 0 ∧
    size.toNat + 48 ≤ (growSize size).toNat ∧
    (growSize size).toNat < size.toNat + 48 + 65536 := by
  rw [MAX_ALLOCATION_toNat] at h
  have hadd : (size + 3 * BLOCK_HEADER).toNat = size.toNat + 48 := by
    have : (3 * BLOCK_HEADER).toNat = 48 := by decide
    rw [BitVec.toNat_add, this]; omega
  have hp : PAGE_SIZE = BitVec.ofNat 64 (2^16) := by decide
  have hfit : (size + 3 * BLOCK_HEADER).toNat + (2^16 - 1) < 2^64 := by rw [hadd]; omega
  obtain ⟨m, ge, lt⟩ := roundUp_spec _ 16 (by decide) hfit
  unfold growSize
  rw [hp]
  rw [hadd] at ge lt
  exact ⟨by omega, by omega, ge, lt⟩

/-- **The whole `Tree::alloc` size path is overflow-free.** For every request the tree path
accepts, `normalize_size` and then `grow` run without overflowing (so a debug build never panics on
them), and `grow` maps whole pages with room for the block, its two fences and its fake header. -/
theorem alloc_sizes_no_overflow (size : Usize) (h : size.toNat ≤ MAX_ALLOCATION.toNat) :
    ∃ n, normalizeSize size = some n ∧
      n.toNat + 48 + (2^16 - 1) < 2^64 ∧
      (growSize n).toNat % 65536 = 0 ∧ n.toNat + 48 ≤ (growSize n).toNat := by
  obtain ⟨n, hn, -, -, -, -, hlt⟩ := (normalizeSize_spec size).1 h
  have hb : n.toNat ≤ MAX_ALLOCATION.toNat + 16 := by
    rw [MAX_ALLOCATION_toNat] at h ⊢; omega
  obtain ⟨h1, h2, h3, -⟩ := growSize_spec n hb
  exact ⟨n, hn, h1, h2, h3⟩

/-- `alloc_aligned`'s guard `alignment > MAX_ALLOCATION || size > MAX_ALLOCATION - alignment`:
the subtraction cannot underflow (the left disjunct short-circuits first), and when the guard
passes, `size + alignment` neither overflows nor exceeds what `grow` and `extract_aligned`'s
`size + alignment` upper bound can take. -/
theorem alloc_aligned_guard (size alignment : Usize)
    (h1 : ¬ alignment > MAX_ALLOCATION) (h2 : ¬ size > MAX_ALLOCATION - alignment) :
    (MAX_ALLOCATION - alignment).toNat = MAX_ALLOCATION.toNat - alignment.toNat ∧
    (size + alignment).toNat = size.toNat + alignment.toNat ∧
    size.toNat + alignment.toNat ≤ MAX_ALLOCATION.toNat := by
  rw [gt_iff_lt, BitVec.lt_def] at h1 h2
  have hsub : (MAX_ALLOCATION - alignment).toNat = MAX_ALLOCATION.toNat - alignment.toNat := by
    rw [BitVec.toNat_sub]; rw [MAX_ALLOCATION_toNat] at h1 ⊢; omega
  rw [hsub] at h2
  refine ⟨hsub, ?_, by omega⟩
  rw [BitVec.toNat_add]; rw [MAX_ALLOCATION_toNat] at h2; omega

/-! ## The bucket size classes (`bucket.rs`) -/

/-- `bucket.rs` `bucket_spacing_function`: `((size + (MIN_ALLOCATION - 1)) >> 3) - 1`. -/
def bucketSpacing (size : Usize) : Usize := ((size + (8 - 1)) >>> 3) - 1
/-- `bucket.rs` `bucket_spacing_function_aligned`: `(size >> 3) - 1`. -/
def bucketSpacingAligned (size : Usize) : Usize := (size >>> 3) - 1
/-- `bucket.rs` `bucket_spacing_function_inverse`: `(index + 1) << 3`. -/
def bucketSpacingInverse (index : Usize) : Usize := (index + 1) <<< 3
/-- `bucket.rs` `clamp_small_allocation`. -/
def clampSmall (size : Usize) : Usize := if size < 8 then 8 else size

/-- Rust's `usize::saturating_add`. -/
def saturatingAdd (a b : Usize) : Usize :=
  if a.toNat + b.toNat < 2^64 then a + b else BitVec.allOnes 64

/-- `bucket.rs` `is_small_allocation`, for a guard size `guard` (`MEMORY_GUARD_SIZE`: 16 with
`debug-allocator`, 0 without). -/
def isSmall (guard size : Usize) : Bool := saturatingAdd size guard ≤ 256

private theorem bucketSpacing_toNat (s : Usize) (h1 : 1 ≤ s.toNat) (h2 : s.toNat ≤ 256) :
    (bucketSpacing s).toNat = (s.toNat + 7) / 8 - 1 := by
  unfold bucketSpacing
  have a : (1 : Usize).toNat = 1 := rfl
  have b : (8 : Usize).toNat = 8 := rfl
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, BitVec.toNat_add,
    Nat.shiftRight_eq_div_pow, a, b]
  omega

private theorem bucketSpacingInverse_toNat (i : Usize) (h : i.toNat < 32) :
    (bucketSpacingInverse i).toNat = (i.toNat + 1) * 8 := by
  unfold bucketSpacingInverse
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]
  simp; omega

/-- Every small request maps to one of the 32 buckets, and that bucket's element size is the
**smallest** size class that fits it: at least the request, less than one class (8 bytes) above
it. -/
theorem bucketSpacing_spec (s : Usize) (h1 : 1 ≤ s.toNat) (h2 : s.toNat ≤ 256) :
    (bucketSpacing s).toNat < 32 ∧
    s.toNat ≤ (bucketSpacingInverse (bucketSpacing s)).toNat ∧
    (bucketSpacingInverse (bucketSpacing s)).toNat < s.toNat + 8 := by
  have e := bucketSpacing_toNat s h1 h2
  have hi : (bucketSpacing s).toNat < 32 := by omega
  rw [bucketSpacingInverse_toNat _ hi, e]
  omega

/-- The inverse really is an inverse: bucket `i`'s element size maps back to bucket `i`, and
every element size lies in `[8, 256]`. -/
theorem bucketSpacing_inverse (i : Usize) (h : i.toNat < 32) :
    bucketSpacing (bucketSpacingInverse i) = i ∧
    8 ≤ (bucketSpacingInverse i).toNat ∧ (bucketSpacingInverse i).toNat ≤ 256 := by
  have e := bucketSpacingInverse_toNat i h
  refine ⟨?_, by omega, by omega⟩
  apply BitVec.eq_of_toNat_eq
  rw [bucketSpacing_toNat _ (by omega) (by omega), e]
  omega

/-- On multiples of 8 the cheaper aligned form computes the same bucket. -/
theorem bucketSpacingAligned_eq (s : Usize) (h1 : 1 ≤ s.toNat) (h2 : s.toNat ≤ 256)
    (h8 : s.toNat % 8 = 0) : bucketSpacingAligned s = bucketSpacing s := by
  apply BitVec.eq_of_toNat_eq
  rw [bucketSpacing_toNat s h1 h2]
  unfold bucketSpacingAligned
  simp only [BitVec.toNat_sub, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp; omega

/-- Clamping makes every small request (including 0) a valid `bucket_spacing_function` input. -/
theorem clampSmall_spec (s : Usize) (h : s.toNat ≤ 256) :
    1 ≤ (clampSmall s).toNat ∧ (clampSmall s).toNat ≤ 256 ∧ s.toNat ≤ (clampSmall s).toNat := by
  unfold clampSmall
  split <;> rename_i hs <;> rw [BitVec.lt_def] at hs <;> simp at hs ⊢ <;> omega

/-- `is_small_allocation` is exactly the mathematical test `size + guard ≤ 256`: the saturating
add means no huge request can wrap around and be misrouted to a bucket. -/
theorem isSmall_iff (guard size : Usize) :
    isSmall guard size = true ↔ size.toNat + guard.toNat ≤ 256 := by
  unfold isSmall saturatingAdd
  split
  · rename_i h; simp only [decide_eq_true_eq, BitVec.le_def, BitVec.toNat_add]
    rw [Nat.mod_eq_of_lt h]; simp
  · rename_i h; simp only [decide_eq_true_eq, BitVec.le_def]; simp; omega

end Oris.Arith
