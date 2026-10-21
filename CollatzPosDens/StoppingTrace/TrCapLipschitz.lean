/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapFactor
public import CollatzPosDens.StoppingTrace.TrLipConst
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The capped factors are Lipschitz

For every integer `c`, the capped packet factor `Φ^cap_c` is Lipschitz with constant `ℓ_c`:
`|Φ^cap_c(θ) - Φ^cap_c(θ')| ≤ ℓ_c |θ - θ'|` for all real `θ, θ'`.

Outside `3 ≤ c ≤ 16` both values are `1` and `ℓ_c = 0`. For `3 ≤ c ≤ 16` put `t = c - 1`,
`a_j = 2^j - 1` and `a_* = a_{⌊(c-2)/2⌋}`. Multiplying the packet sum by the unit
`e^{-2πi a_* θ}` does not change its modulus, so the reverse triangle inequality and
`|e^{ix} - e^{iy}| ≤ |x - y|` give
`|Φ_t(θ) - Φ_t(θ')| ≤ (2π / t) ∑_{j<t} |a_j - a_*| |θ - θ'|`, and `2π < 44/7`. Finally
`x ↦ max {x, k}` is `1`-Lipschitz.

## Main results

* `CollatzPosDens.norm_exp_two_pi_I_sub_le`: `‖e^{2πix} - e^{2πiy}‖ ≤ 2π |x - y|`.
* `CollatzPosDens.abs_chPacketFn_sub_le`: for every real centre `b`,
  `|Φ_t(θ) - Φ_t(θ')| ≤ (2π / t) ∑_{j<t} |2^j - 1 - b| |θ - θ'|`.
* `CollatzPosDens.abs_trCapFactor_sub_le`: `|Φ^cap_c(θ) - Φ^cap_c(θ')| ≤ ℓ_c |θ - θ'|`.
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- The map `x ↦ e^{2πix}` is `2π`-Lipschitz. -/
theorem norm_exp_two_pi_I_sub_le (x y : ℝ) :
    ‖Complex.exp (2 * π * Complex.I * (x : ℂ)) - Complex.exp (2 * π * Complex.I * (y : ℂ))‖ ≤
      2 * π * |x - y| := by
  have h : Complex.exp (2 * π * Complex.I * (x : ℂ)) - Complex.exp (2 * π * Complex.I * (y : ℂ)) =
      Complex.exp (2 * π * Complex.I * (y : ℂ)) *
        (Complex.exp (Complex.I * ((2 * π * (x - y) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hy : ‖Complex.exp (2 * π * Complex.I * (y : ℂ))‖ = 1 := by
    have : 2 * π * Complex.I * (y : ℂ) = ((2 * π * y : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  rw [h, norm_mul, hy, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-- The packet function is Lipschitz, with a constant computed about an arbitrary real centre
`b`: `|Φ_t(θ) - Φ_t(θ')| ≤ (2π / t) ∑_{j<t} |2^j - 1 - b| |θ - θ'|`. -/
theorem abs_chPacketFn_sub_le (t : ℕ) (b θ θ' : ℝ) :
    |chPacketFn t θ - chPacketFn t θ'| ≤
      2 * π / t * (∑ j ∈ Finset.range t, |((2 : ℝ) ^ j - 1) - b|) * |θ - θ'| := by
  set g : ℝ → ℂ := fun θ =>
    ∑ j ∈ Finset.range t, Complex.exp (2 * π * Complex.I * ((((2 : ℝ) ^ j - 1 - b) * θ : ℝ) : ℂ))
    with hg
  have key : ∀ θ : ℝ, chPacketFn t θ = (1 / (t : ℝ)) * ‖g θ‖ := by
    intro θ
    rw [chPacketFn_def]
    congr 1
    have : ∑ a ∈ Finset.range t,
        Complex.exp (2 * π * Complex.I * ((((2 : ℝ) ^ a - 1) * θ : ℝ) : ℂ)) =
          Complex.exp (((2 * π * (b * θ) : ℝ) : ℂ) * Complex.I) * g θ := by
      rw [hg, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  rw [key, key, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
  have hsum : ‖g θ - g θ'‖ ≤
      ∑ j ∈ Finset.range t, 2 * π * (|((2 : ℝ) ^ j - 1) - b| * |θ - θ'|) := by
    rw [hg]
    simp only
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_exp_two_pi_I_sub_le _ _).trans (le_of_eq ?_)
    rw [← mul_sub, abs_mul]
  have h1 : |‖g θ‖ - ‖g θ'‖| ≤ ‖g θ - g θ'‖ := abs_norm_sub_norm_le _ _
  calc 1 / (t : ℝ) * |‖g θ‖ - ‖g θ'‖|
      ≤ 1 / (t : ℝ) * ∑ j ∈ Finset.range t, 2 * π * (|((2 : ℝ) ^ j - 1) - b| * |θ - θ'|) :=
        mul_le_mul_of_nonneg_left (h1.trans hsum) (by positivity)
    _ = 2 * π / t * (∑ j ∈ Finset.range t, |((2 : ℝ) ^ j - 1) - b|) * |θ - θ'| := by
        rw [← Finset.mul_sum, ← Finset.sum_mul]
        ring

/-- **The capped factors are Lipschitz**: for every integer `c` and all real `θ, θ'`,
`|Φ^cap_c(θ) - Φ^cap_c(θ')| ≤ ℓ_c |θ - θ'|`. -/
@[collatz_pos_dens "lem_tr_cap_lipschitz"]
theorem abs_trCapFactor_sub_le (c : ℤ) (θ θ' : ℝ) :
    |trCapFactor c θ - trCapFactor c θ'| ≤ (trLipConst c : ℝ) * |θ - θ'| := by
  by_cases hc : 3 ≤ c ∧ c ≤ 16
  · obtain ⟨h₁, h₂⟩ := hc
    rw [trCapFactor_of_mem h₁ h₂, trCapFactor_of_mem h₁ h₂, trLipConst_of_mem h₁ h₂]
    have ht : (c - 1).toNat = c.toNat - 1 := by omega
    have htR : ((c.toNat - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by
      have : ((c.toNat - 1 : ℕ) : ℤ) = c - 1 := by omega
      exact_mod_cast this
    have htpos : (0 : ℝ) < (c : ℝ) - 1 := by
      have : (3 : ℝ) ≤ c := by exact_mod_cast h₁
      linarith
    rw [ht]
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    refine (abs_chPacketFn_sub_le (c.toNat - 1) ((2 : ℝ) ^ ((c.toNat - 2) / 2) - 1) θ θ').trans ?_
    rw [htR]
    push_cast
    have hS : (0 : ℝ) ≤ ∑ j ∈ Finset.range (c.toNat - 1),
        |((2 : ℝ) ^ j - 1) - ((2 : ℝ) ^ ((c.toNat - 2) / 2) - 1)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    have hpi : 2 * π / ((c : ℝ) - 1) ≤ 44 / (7 * ((c : ℝ) - 1)) := by
      rw [div_le_div_iff₀ htpos (by positivity)]
      have := Real.pi_lt_d4
      nlinarith
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpi hS) (abs_nonneg _)
  · rw [trCapFactor_of_not_mem hc, trCapFactor_of_not_mem hc, trLipConst_of_not_mem hc]
    simp

end CollatzPosDens
