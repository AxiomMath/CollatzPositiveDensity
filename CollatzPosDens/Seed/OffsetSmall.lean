/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.NormNum
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Wb
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.OffsetBound

/-!
# Offsets of first-crossing words are small

For a word `w ∈ 𝒲(b, u, K)` the offset satisfies `off(w) < 2^b`. Indeed `|w| ≤ h_b` and
`5 h_b ≤ 8 b`, so `off(w) < (3/2)^{|w|} ≤ (3/2)^{h_b}`, and
`((3/2)^{h_b})^5 ≤ (3/2)^{8b} = (6561/256)^b ≤ 32^b = (2^b)^5`.

## Main results

* `CollatzPosDens.offsetSmall_three_halves_pow_hb_le_two_pow`: `(3/2)^{h_b} ≤ 2^b`.
* `CollatzPosDens.offsetSmall_of_length_le_hb`: `off(w) < 2^b` whenever `|w| ≤ h_b`.
* `CollatzPosDens.off_lt_two_pow_of_mem_firstCrossing`: `off(w) < 2^b` for
  `w ∈ 𝒲(b, u, K)`.

## Implementation notes

The source assumes `b ≥ 1`; the bound holds for every `b : ℕ`, since only `|w| ≤ h_b` is used
and the offset bound `off(w) < (3/2)^{|w|}` holds for every word. The non-strict comparison
`(3/2)^{h_b} ≤ 2^b` therefore suffices, the strictness coming from the offset bound.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `(3/2)^{h_b} ≤ 2^b`, since `5 h_b ≤ 8 b` and `(3/2)^8 ≤ 2^5`. -/
theorem offsetSmall_three_halves_pow_hb_le_two_pow (b : ℕ) :
    (3 / 2 : ℚ) ^ hb b ≤ 2 ^ b := by
  have h5 : 5 * hb b ≤ 8 * b := by
    have := five_mul_wb_le b
    rw [hb_def]
    omega
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity)
    (by norm_num : (5 : ℕ) ≠ 0)).1 ?_
  calc ((3 / 2 : ℚ) ^ hb b) ^ 5 = (3 / 2 : ℚ) ^ (5 * hb b) := by rw [← pow_mul, mul_comm]
    _ ≤ (3 / 2 : ℚ) ^ (8 * b) := pow_le_pow_right₀ (by norm_num) h5
    _ = ((3 / 2 : ℚ) ^ 8) ^ b := pow_mul _ _ _
    _ ≤ ((2 : ℚ) ^ 5) ^ b := pow_le_pow_left₀ (by norm_num) (by norm_num) b
    _ = ((2 : ℚ) ^ b) ^ 5 := by rw [← pow_mul, ← pow_mul, mul_comm]

/-- A word of length at most `h_b` has offset less than `2^b`. -/
theorem offsetSmall_of_length_le_hb {b : ℕ} {w : Word} (hw : w.length ≤ hb b) :
    off w < 2 ^ b :=
  calc off w < (3 / 2 : ℚ) ^ w.length := off_lt_three_halves_pow w
    _ ≤ (3 / 2 : ℚ) ^ hb b := pow_le_pow_right₀ (by norm_num) hw
    _ ≤ 2 ^ b := offsetSmall_three_halves_pow_hb_le_two_pow b

/-- The offset of a first-crossing word `w ∈ 𝒲(b, u, K)` is less than `2^b`. -/
@[collatz_pos_dens "lem_s05_offset_small"]
theorem off_lt_two_pow_of_mem_firstCrossing {b : ℕ} {u : ℤ} {K : ℕ} {w : Word}
    (hw : w ∈ firstCrossing b u K) : off w < 2 ^ b :=
  offsetSmall_of_length_le_hb (length_le_hb_of_mem_firstCrossing hw)

end CollatzPosDens
