/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidRewardCap
public import CollatzPosDens.CharSum.ChPaidRewardNonneg
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.StoppingTrace.TrCapFactor

/-!
# The paid factor is at most the capped factor

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and let `J = ⌊n/2⌋`. For every
integer `c` and every point `p` with `j(p) ≤ J`, the paid factor is bounded by the capped
packet factor at the angle of `p`:
`exp(-z_* R_c(p)) ≤ Φ^cap_c(ϑ(p))`.

For `3 ≤ c ≤ 16` this is the bound `exp(-z_* R_c(p)) ≤ max (φ_c(p), 2^{-16})`, since the raw
factor is `φ_c(p) = Φ_{c-1}(ϑ(p))`; otherwise `R_c(p) ≥ 0` and `z_* > 0` give
`exp(-z_* R_c(p)) ≤ 1 = Φ^cap_c(ϑ(p))`.

## Main results

* `CollatzPosDens.exp_neg_zStar_mul_chPaidReward_le_trCapFactor`:
  `exp(-z_* R_c(p)) ≤ Φ^cap_c(ϑ(p))`.

## Implementation notes

The statement holds for every `p : ℤ × ℤ`, not only for points of `𝒫`, and for every
threshold `ε`, since the paid reward and the angle are defined in that generality.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every integer `c` and every point `p` with `j(p) ≤ ⌊n/2⌋`,
`exp(-z_* R_c(p)) ≤ Φ^cap_c(ϑ(p))`. -/
@[collatz_pos_dens "lem_c3_cap_reward"]
theorem exp_neg_zStar_mul_chPaidReward_le_trCapFactor {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {c : ℤ} {p : ℤ × ℤ} (hp : bkJ p ≤ ((n / 2 : ℕ) : ℤ)) :
    Real.exp (-(zStar : ℝ) * chPaidReward n ξ ε c p) ≤ trCapFactor c (bkTheta n ξ p) := by
  by_cases hc : 3 ≤ c ∧ c ≤ 16
  · rw [trCapFactor_of_mem hc.1 hc.2, ← chRawFactor_of_two_le n ξ (by omega)]
    exact exp_neg_zStar_mul_chPaidReward_le hc.1 hc.2 hp
  · rw [trCapFactor_of_not_mem hc, Real.exp_le_one_iff]
    have hz : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
    nlinarith [zero_le_chPaidReward n ξ ε c p]

end CollatzPosDens
