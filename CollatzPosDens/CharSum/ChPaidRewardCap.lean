/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidReward
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The paid reward caps the clipped raw factor

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. If `3 ≤ c ≤ 16` and `j(p) ≤ ⌊n/2⌋`,
then the paid reward `R_c(p)` is at least `-(1/z_*) log Q` with `Q = max (φ_c(p), 2^{-16}) > 0`;
since `z_* > 0`, exponentiating gives `e^{-z_* R_c(p)} ≤ Q`.

## Main results

* `CollatzPosDens.exp_neg_zStar_mul_chPaidReward_le`:
  `e^{-z_* R_c(p)} ≤ max (φ_c(p), 2^{-16})`.

## Implementation notes

The statement holds for every `p : ℤ × ℤ`, not only for points of `𝒫`, since the paid reward
is defined on all of `ℤ × ℤ`.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `3 ≤ c ≤ 16` and `j(p) ≤ ⌊n/2⌋`, `e^{-z_* R_c(p)} ≤ max (φ_c(p), 2^{-16})`. -/
@[collatz_pos_dens "lem_ch_paid_reward_cap"]
theorem exp_neg_zStar_mul_chPaidReward_le {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ}
    {p : ℤ × ℤ} (h₁ : 3 ≤ c) (h₂ : c ≤ 16) (hp : bkJ p ≤ ((n / 2 : ℕ) : ℤ)) :
    Real.exp (-(zStar : ℝ) * chPaidReward n ξ ε c p) ≤
      max (chRawFactor n ξ c p) ((2 : ℝ) ^ (-16 : ℤ)) := by
  set Q := max (chRawFactor n ξ c p) ((2 : ℝ) ^ (-16 : ℤ)) with hQ
  have hQpos : 0 < Q := lt_max_of_lt_right (by positivity)
  have hz : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
  have hR : -(1 / (zStar : ℝ)) * Real.log Q ≤ chPaidReward n ξ ε c p := by
    rw [chPaidReward_of_mem h₁ h₂ hp]
    exact le_max_right _ _
  have hle : -(zStar : ℝ) * chPaidReward n ξ ε c p ≤ Real.log Q := by
    have h := mul_le_mul_of_nonneg_left hR hz.le
    have : (zStar : ℝ) * (-(1 / (zStar : ℝ)) * Real.log Q) = -Real.log Q := by
      field_simp
    rw [this] at h
    linarith
  calc Real.exp (-(zStar : ℝ) * chPaidReward n ξ ε c p) ≤ Real.exp (Real.log Q) :=
        Real.exp_le_exp.2 hle
    _ = Q := Real.exp_log hQpos

end CollatzPosDens
