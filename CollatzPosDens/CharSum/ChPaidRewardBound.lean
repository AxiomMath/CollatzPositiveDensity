/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidReward
public import CollatzPosDens.CharSum.ChOldRewardBound

/-!
# The raw factor is bounded by the paid reward

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε ≥ ε_*`. For every integer `c` and every
point `p ∈ 𝒫`, the raw factor satisfies `φ_c(p) ≤ exp(-z_* R_c(p))`.

The baseline bound `φ_c(p) ≤ exp(-z_* R^old_c(p))` covers the case `R_c(p) = R^old_c(p)`.
Otherwise `R_c(p)` is the maximum of `R^old_c(p)` and `-(1/z_*) log Q` with
`Q = max (φ_c(p), 2^{-16}) > 0`, and `φ_c(p) ≤ Q = exp(-z_* (-(1/z_*) log Q))`; since
`x ↦ exp(-z_* x)` is decreasing, `φ_c(p)` is bounded by the exponential at the maximum.

## Main results

* `CollatzPosDens.chRawFactor_le_exp_neg_chPaidReward`: `φ_c(p) ≤ exp(-z_* R_c(p))`.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The raw factor is bounded by the paid reward.** If `ε ≥ ε_*`, then for every integer `c`
and `p ∈ 𝒫`, `φ_c(p) ≤ exp(-z_* R_c(p))`. -/
@[collatz_pos_dens "lem_ch_paid_reward_bound"]
theorem chRawFactor_le_exp_neg_chPaidReward {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    (hε : (epsStar : ℝ) ≤ ε) (c : ℤ) {p : ℤ × ℤ} (hp : p ∈ bkPoints) :
    chRawFactor n ξ c p ≤ Real.exp (-((zStar : ℝ) * chPaidReward n ξ ε c p)) := by
  have hold := chRawFactor_le_exp_neg_chOldReward (n := n) (ξ := ξ) hε c hp
  by_cases hc : 3 ≤ c ∧ c ≤ 16 ∧ bkJ p ≤ ((n / 2 : ℕ) : ℤ)
  · obtain ⟨h₁, h₂, h₃⟩ := hc
    rw [chPaidReward_of_mem h₁ h₂ h₃]
    have hz : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
    set Q := max (chRawFactor n ξ c p) ((2 : ℝ) ^ (-16 : ℤ))
    have hQ : 0 < Q := lt_max_of_lt_right (by positivity)
    have hlog : chRawFactor n ξ c p ≤
        Real.exp (-((zStar : ℝ) * (-(1 / (zStar : ℝ)) * Real.log Q))) := by
      rw [show -((zStar : ℝ) * (-(1 / (zStar : ℝ)) * Real.log Q)) = Real.log Q by
        field_simp, Real.exp_log hQ]
      exact le_max_left _ _
    rcases le_total (chOldReward n ξ ε c p) (-(1 / (zStar : ℝ)) * Real.log Q) with h | h
    · rwa [max_eq_right h]
    · rwa [max_eq_left h]
  · rwa [chPaidReward_of_not_mem hc]

end CollatzPosDens
