/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChOddPackets
public import CollatzPosDens.StoppingTrace.TrCapFactor

/-!
# A capped packet factor from a bound on its pair sum

Writing `w_a = exp(2πi (2^a - 1) θ)`, the square of the packet sum is
`|∑_{a<t} w_a|^2 = t + 2 ∑_{0 ≤ i < j < t} cos(2π(2^j - 2^i)θ)`. Hence an upper bound `S` on the
pair sum of cosines with `t + 2S ≤ u^2` and `u ≥ 0` gives `Φ_t(θ) ≤ u / t`.
For the capped packet factor with `3 ≤ c ≤ 16` and `t = c - 1`, this yields
`Φ^cap_c(θ) ≤ min {1, max {u / (c - 1), 2^{-16}}}`.

## Main results

* `CollatzPosDens.chPacketFn_le_of_pairSum_le`: `Φ_t(θ) ≤ u / t` from a bound on the pair sum.
* `CollatzPosDens.trCapFactor_le_of_pairSum_le`: the bound
  `Φ^cap_c(θ) ≤ min {1, max {u / (c - 1), 2^{-16}}}`.
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- If `∑_{0 ≤ i < j < t} cos(2π(2^j - 2^i)θ) ≤ S`, `t + 2S ≤ u^2` and `0 ≤ u`, then
`Φ_t(θ) ≤ u / t`. -/
theorem chPacketFn_le_of_pairSum_le {t : ℕ} {θ S u : ℝ} (hu : 0 ≤ u)
    (hS : ∑ j ∈ range t, ∑ i ∈ range j,
      Real.cos (2 * π * (((2 : ℝ) ^ j - 2 ^ i) * θ)) ≤ S)
    (hSu : (t : ℝ) + 2 * S ≤ u ^ 2) :
    chPacketFn t θ ≤ u / t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [chPacketFn]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hsq : ((t : ℝ) * chPacketFn t θ) ^ 2 ≤ u ^ 2 := by
    rw [mul_pow, chPacketFn_sq, mul_div_cancel₀ _ (by positivity), chPacketPairSum]
    linarith
  rw [le_div_iff₀ htR, mul_comm]
  exact (abs_le_of_sq_le_sq' hsq hu).2

/-- **A capped factor from a bound on its pair sum.** Let `3 ≤ c ≤ 16`, `0 ≤ u`,
`∑_{0 ≤ i < j ≤ c - 2} cos(2π(2^j - 2^i)θ) ≤ S` and `c - 1 + 2S ≤ u^2`. Then
`Φ^cap_c(θ) ≤ min {1, max {u / (c - 1), 2^{-16}}}`. -/
@[collatz_pos_dens "lem_tr_cap_pair_bound"]
theorem trCapFactor_le_of_pairSum_le {c : ℤ} (hc₁ : 3 ≤ c) (hc₂ : c ≤ 16) {θ S u : ℝ}
    (hu : 0 ≤ u)
    (hS : ∑ j ∈ range (c - 1).toNat, ∑ i ∈ range j,
      Real.cos (2 * π * (((2 : ℝ) ^ j - 2 ^ i) * θ)) ≤ S)
    (hSu : ((c : ℝ) - 1) + 2 * S ≤ u ^ 2) :
    trCapFactor c θ ≤ min 1 (max (u / ((c : ℝ) - 1)) ((2 : ℝ) ^ (-16 : ℤ))) := by
  have ht : (((c - 1).toNat : ℕ) : ℝ) = (c : ℝ) - 1 := by
    have : (((c - 1).toNat : ℕ) : ℤ) = c - 1 := Int.toNat_of_nonneg (by omega)
    exact_mod_cast this
  have hΦ := chPacketFn_le_of_pairSum_le (t := (c - 1).toNat) hu hS (by rw [ht]; exact hSu)
  rw [ht] at hΦ
  refine le_min (trCapFactor_le_one c θ) ?_
  rw [trCapFactor_of_mem hc₁ hc₂]
  exact max_le_max hΦ le_rfl

end CollatzPosDens
