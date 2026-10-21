/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapLipschitz

/-!
# A capped factor near a point

Let `3 ≤ c ≤ 16` and put `t = c - 1`. Multiplying the packet sum of `Φ_t(θ₀)` by the unit
`e^{2πiθ₀}` does not change its modulus, and `(2^a - 1)θ₀ + θ₀ = 2^a θ₀`, so
`Φ_t(θ₀) = (1/t) |∑_{a<t} e^{2πi 2^a θ₀}|`. Hence a bound `s` on the latter sum gives
`Φ^cap_c(θ₀) ≤ max {s/t, 2^{-16}}`, and the Lipschitz bound for `Φ^cap_c` transports it to every
`θ`:
`Φ^cap_c(θ) ≤ min {1, max {s/(c-1), 2^{-16}} + ℓ_c |θ - θ₀|}`.

## Main results

* `CollatzPosDens.chPacketFn_eq_norm_sum_exp_two_pow`:
  `Φ_t(θ) = (1/t) |∑_{a<t} e^{2πi 2^a θ}|`.
* `CollatzPosDens.trCapFactor_le_min_of_norm_sum_le`: the bound on `Φ^cap_c(θ)` near a point
  `θ₀` at which the sum `∑_{j=0}^{c-2} e^{2πi 2^j θ₀}` is bounded by `s`.
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- The packet function in the shifted form `Φ_t(θ) = (1/t) |∑_{a<t} e^{2πi 2^a θ}|`. -/
theorem chPacketFn_eq_norm_sum_exp_two_pow (t : ℕ) (θ : ℝ) :
    chPacketFn t θ = (1 / (t : ℝ)) *
      ‖∑ a ∈ Finset.range t, Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a * θ : ℝ) : ℂ))‖ := by
  rw [chPacketFn_def]
  congr 1
  have : ∑ a ∈ Finset.range t, Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a * θ : ℝ) : ℂ)) =
      Complex.exp (((2 * π * θ : ℝ) : ℂ) * Complex.I) *
        ∑ a ∈ Finset.range t,
          Complex.exp (2 * π * Complex.I * ((((2 : ℝ) ^ a - 1) * θ : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- **A capped factor near a point**: if `3 ≤ c ≤ 16` and
`|∑_{j=0}^{c-2} e^{2πi 2^j θ₀}| ≤ s`, then
`Φ^cap_c(θ) ≤ min {1, max {s/(c-1), 2^{-16}} + ℓ_c |θ - θ₀|}`. -/
@[collatz_pos_dens "lem_tr_cap_cell_bound"]
theorem trCapFactor_le_min_of_norm_sum_le {c : ℤ} (h₁ : 3 ≤ c) (h₂ : c ≤ 16) (θ θ₀ s : ℝ)
    (hs : ‖∑ j ∈ Finset.range (c.toNat - 1),
      Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ j * θ₀ : ℝ) : ℂ))‖ ≤ s) :
    trCapFactor c θ ≤
      min 1 (max (s / ((c : ℝ) - 1)) ((2 : ℝ) ^ (-16 : ℤ)) + (trLipConst c : ℝ) * |θ - θ₀|) := by
  refine le_min (trCapFactor_le_one c θ) ?_
  have ht : (c - 1).toNat = c.toNat - 1 := by omega
  have htR : ((c.toNat - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
    have : ((c.toNat - 1 : ℕ) : ℤ) = c - 1 := by omega
    exact_mod_cast this
  have htpos : (0 : ℝ) < (c : ℝ) - 1 := by
    have : (3 : ℝ) ≤ c := by exact_mod_cast h₁
    linarith
  have h0 : trCapFactor c θ₀ ≤ max (s / ((c : ℝ) - 1)) ((2 : ℝ) ^ (-16 : ℤ)) := by
    rw [trCapFactor_of_mem h₁ h₂, ht]
    refine max_le_max ?_ le_rfl
    rw [chPacketFn_eq_norm_sum_exp_two_pow, htR, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hs htpos.le
  have hlip := abs_trCapFactor_sub_le c θ θ₀
  have := (abs_le.mp hlip).2
  linarith

end CollatzPosDens
