/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Ring

/-!
# Boundary weights

For `t ∈ ℕ` and `j ∈ ℤ` the boundary weight is
`e_t(j) = (1/8) binom(t - 1, 2j - 1) 2^{-t}` when `t ≥ 1` and `j ≥ 1`, and `e_t(j) = 0`
otherwise.

## Main definitions

* `CollatzPosDens.boundaryWeight t j`: the boundary weight `e_t(j)`.

## Main results

* `CollatzPosDens.boundaryWeight_of_pos`, `CollatzPosDens.boundaryWeight_of_not`:
  the two cases of the definition.
* `CollatzPosDens.boundaryWeight_zero_left`, `CollatzPosDens.boundaryWeight_of_nonpos`:
  vanishing at `t = 0` and at `j ≤ 0`.
* `CollatzPosDens.boundaryWeight_succ_natCast_succ`: the value at `t + 1`, `j + 1` with
  `t, j ∈ ℕ`.
* `CollatzPosDens.boundaryWeight_eq_div_sixteen`: the form
  `e_t(j) = (1/16) binom(t - 1, 2j - 1) 2^{-(t-1)}` for `t, j ≥ 1`.
* `CollatzPosDens.boundaryWeight_nonneg`: the weights are nonnegative.

## Implementation notes

The weight takes values in `ℝ` and its index lies in `ℤ`; the lower entry `2j - 1` of the
binomial coefficient is read in `ℕ` as `2 j.toNat - 1`, which agrees with `2j - 1` whenever
`j ≥ 1`, the only case in which it is used.

## References

* [Mazur, *Collatz positive density*], §6.5.
-/

@[expose] public section

namespace CollatzPosDens

/-- The boundary weight `e_t(j) = (1/8) binom(t - 1, 2j - 1) 2^{-t}` for `t ≥ 1`, `j ≥ 1`, and `0`
otherwise. -/
@[collatz_pos_dens "def_rn_cross_e"]
noncomputable def boundaryWeight (t : ℕ) (j : ℤ) : ℝ :=
  if 1 ≤ t ∧ 1 ≤ j then ((t - 1).choose (2 * j.toNat - 1) : ℝ) / 8 / 2 ^ t else 0

/-- For `t ≥ 1` and `j ≥ 1`, `e_t(j) = (1/8) binom(t - 1, 2j - 1) 2^{-t}`. -/
theorem boundaryWeight_of_pos {t : ℕ} {j : ℤ} (ht : 1 ≤ t) (hj : 1 ≤ j) :
    boundaryWeight t j = ((t - 1).choose (2 * j.toNat - 1) : ℝ) / 8 / 2 ^ t := by
  simp [boundaryWeight, ht, hj]

/-- The boundary weight `e_t(j)` vanishes unless `t ≥ 1` and `j ≥ 1`. -/
theorem boundaryWeight_of_not {t : ℕ} {j : ℤ} (h : ¬(1 ≤ t ∧ 1 ≤ j)) :
    boundaryWeight t j = 0 := by
  simp only [boundaryWeight, ite_eq_right_iff]
  exact fun h' => absurd h' h

/-- The boundary weight `e_0(j)` vanishes. -/
@[simp]
theorem boundaryWeight_zero_left (j : ℤ) : boundaryWeight 0 j = 0 :=
  boundaryWeight_of_not (by omega)

/-- The boundary weight `e_t(j)` vanishes for `j ≤ 0`. -/
theorem boundaryWeight_of_nonpos (t : ℕ) {j : ℤ} (hj : j ≤ 0) : boundaryWeight t j = 0 :=
  boundaryWeight_of_not (by omega)

/-- For `t, j ∈ ℕ`, `e_{t+1}(j+1) = (1/8) binom(t, 2j + 1) 2^{-(t+1)}`. -/
@[simp]
theorem boundaryWeight_succ_natCast_succ (t j : ℕ) :
    boundaryWeight (t + 1) ((j : ℤ) + 1) = (t.choose (2 * j + 1) : ℝ) / 8 / 2 ^ (t + 1) := by
  rw [boundaryWeight_of_pos (by omega) (by omega)]
  have h : ((j : ℤ) + 1).toNat = j + 1 := by omega
  rw [h, show 2 * (j + 1) - 1 = 2 * j + 1 by omega, Nat.add_sub_cancel]

/-- For `t ≥ 1` and `j ≥ 1`, `e_t(j) = (1/16) binom(t - 1, 2j - 1) 2^{-(t-1)}`. -/
theorem boundaryWeight_eq_div_sixteen {t : ℕ} {j : ℤ} (ht : 1 ≤ t) (hj : 1 ≤ j) :
    boundaryWeight t j = ((t - 1).choose (2 * j.toNat - 1) : ℝ) / 16 / 2 ^ (t - 1) := by
  rw [boundaryWeight_of_pos ht hj]
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ, div_div, div_div]
  congr 1
  ring

/-- The boundary weight `e_t(j)` is nonnegative. -/
theorem boundaryWeight_nonneg (t : ℕ) (j : ℤ) : 0 ≤ boundaryWeight t j := by
  unfold boundaryWeight
  split_ifs
  · exact div_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num)) (pow_nonneg zero_le_two _)
  · exact le_rfl

end CollatzPosDens
