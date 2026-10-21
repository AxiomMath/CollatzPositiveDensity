/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChOldReward
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.Transfer.S02Z
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The paid reward

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For an integer `c` and a point `p`,
the *paid reward* `R_c(p)` enlarges the baseline paid reward `R^old_c(p)` by the logarithmic
cancellation of the raw factor `φ_c(p)`, clipped below at `2^{-16}`: if `3 ≤ c ≤ 16` and
`j(p) ≤ ⌊n/2⌋`, then
`R_c(p) = max (R^old_c(p), -(1/z_*) log max (φ_c(p), 2^{-16}))`,
and otherwise `R_c(p) = R^old_c(p)`.

## Main definitions

* `CollatzPosDens.chPaidReward n ξ ε c p`: the paid reward `R_c(p)`.

## Main results

* `CollatzPosDens.chPaidReward_of_mem`, `CollatzPosDens.chPaidReward_of_not_mem`: the two cases.
* `CollatzPosDens.chOldReward_le_chPaidReward`: `R^old_c(p) ≤ R_c(p)`.
* `CollatzPosDens.chPaidReward_nonneg`: `R_c(p) ≥ 0`.
* `CollatzPosDens.chPaidReward_eq_zero_of_lt_bkJ`: `R_c(p) = 0` when `j(p) > ⌊n/2⌋`.

## Implementation notes

The reward is defined for every `p : ℤ × ℤ`, as the baseline reward and the raw factor are.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- The paid reward `R_c(p)`: the maximum of the baseline reward `R^old_c(p)` and
`-(1/z_*) log max (φ_c(p), 2^{-16})` when `3 ≤ c ≤ 16` and `j(p) ≤ ⌊n/2⌋`, and `R^old_c(p)`
otherwise. -/
@[collatz_pos_dens "def_ch_paid_reward"]
noncomputable def chPaidReward (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (c : ℤ) (p : ℤ × ℤ) : ℝ :=
  if 3 ≤ c ∧ c ≤ 16 ∧ bkJ p ≤ ((n / 2 : ℕ) : ℤ) then
    max (chOldReward n ξ ε c p)
      (-(1 / (zStar : ℝ)) * Real.log (max (chRawFactor n ξ c p) ((2 : ℝ) ^ (-16 : ℤ))))
  else chOldReward n ξ ε c p

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ} {p : ℤ × ℤ}

/-- The paid reward when `3 ≤ c ≤ 16` and `j(p) ≤ ⌊n/2⌋`. -/
theorem chPaidReward_of_mem (h₁ : 3 ≤ c) (h₂ : c ≤ 16) (hp : bkJ p ≤ ((n / 2 : ℕ) : ℤ)) :
    chPaidReward n ξ ε c p = max (chOldReward n ξ ε c p)
      (-(1 / (zStar : ℝ)) * Real.log (max (chRawFactor n ξ c p) ((2 : ℝ) ^ (-16 : ℤ)))) := by
  simp only [chPaidReward, h₁, h₂, hp, and_self, ite_true]

/-- The paid reward equals the baseline reward outside `3 ≤ c ≤ 16`, `j(p) ≤ ⌊n/2⌋`. -/
theorem chPaidReward_of_not_mem (h : ¬ (3 ≤ c ∧ c ≤ 16 ∧ bkJ p ≤ ((n / 2 : ℕ) : ℤ))) :
    chPaidReward n ξ ε c p = chOldReward n ξ ε c p := by
  simp only [chPaidReward, h, ite_false]

/-- The paid reward dominates the baseline paid reward. -/
theorem chOldReward_le_chPaidReward : chOldReward n ξ ε c p ≤ chPaidReward n ξ ε c p := by
  unfold chPaidReward
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- The logarithmic term `-(1/z_*) log max (φ_c(p), 2^{-16})` is nonnegative. -/
theorem neg_one_div_zStar_mul_log_max_chRawFactor_nonneg :
    0 ≤ -(1 / (zStar : ℝ)) * Real.log (max (chRawFactor n ξ c p) ((2 : ℝ) ^ (-16 : ℤ))) := by
  have hz : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
  have hlog : Real.log (max (chRawFactor n ξ c p) ((2 : ℝ) ^ (-16 : ℤ))) ≤ 0 :=
    Real.log_nonpos (le_max_of_le_right (by positivity))
      (max_le (chRawFactor_le_one n ξ c p) (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)))
  have : 0 ≤ 1 / (zStar : ℝ) := by positivity
  rw [neg_mul]
  exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos this hlog)

/-- The paid reward is nonnegative. -/
theorem chPaidReward_nonneg : 0 ≤ chPaidReward n ξ ε c p :=
  chOldReward_nonneg.trans chOldReward_le_chPaidReward

/-- `R_c(p) = 0` when `j(p) > ⌊n/2⌋`. -/
theorem chPaidReward_eq_zero_of_lt_bkJ (hp : ((n / 2 : ℕ) : ℤ) < bkJ p) :
    chPaidReward n ξ ε c p = 0 := by
  rw [chPaidReward_of_not_mem (by omega), chOldReward_eq_zero_of_lt_bkJ hp]

end CollatzPosDens
