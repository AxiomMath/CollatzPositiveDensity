/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.CharSum.ChPacketFn
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Smallness of `Φ_2` near half-odd integers

The packet function of length two is `Φ_2(θ) = ½ |1 + e^{2πiθ}| = |cos πθ|`, since
`1 + e^{2ix} = 2 cos x · e^{ix}`. Consequently `Φ_2` vanishes at the half-odd integers
`b / 2` (`b` odd), and near them it is small: for every odd integer `b` and real `β`,
`Φ_2((b + β) / 2) = |sin (πβ / 2)| ≤ (π / 2) |β| ≤ (11 / 7) |β|`.

## Main results

* `CollatzPosDens.chPacketFn_two`: `Φ_2(θ) = |cos πθ|`.
* `CollatzPosDens.chPacketFn_two_odd_add_div_two`: `Φ_2((b + β) / 2) = |sin (πβ / 2)|` for odd `b`.
* `CollatzPosDens.chPacketFn_two_odd_add_div_two_le`: `Φ_2((b + β) / 2) ≤ (11 / 7) |β|`
  for odd `b`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The packet function of length two is `Φ_2(θ) = |cos πθ|`. -/
theorem chPacketFn_two (θ : ℝ) : chPacketFn 2 θ = |Real.cos (π * θ)| := by
  have key : Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ 0 - 1) * θ : ℝ)) +
      Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ 1 - 1) * θ : ℝ)) =
      Complex.exp (((π * θ : ℝ) : ℂ) * Complex.I) * (2 * ((Real.cos (π * θ) : ℝ) : ℂ)) := by
    rw [Complex.ofReal_cos, Complex.cos, mul_div_cancel₀ _ two_ne_zero, mul_add,
      ← Complex.exp_add, ← Complex.exp_add]
    norm_num
    rw [add_comm (1 : ℂ)]
    congr 2
    ring
  rw [chPacketFn_def, Finset.sum_range_succ, Finset.sum_range_one, key, norm_mul,
    Complex.norm_exp_ofReal_mul_I, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_ofNat]
  ring

/-- For odd `b`, `Φ_2((b + β) / 2) = |sin (πβ / 2)|`. -/
theorem chPacketFn_two_odd_add_div_two {b : ℤ} (hb : Odd b) (β : ℝ) :
    chPacketFn 2 ((b + β) / 2) = |Real.sin (π * β / 2)| := by
  obtain ⟨k, rfl⟩ := hb
  have h : π * ((((2 * k + 1 : ℤ) : ℝ) + β) / 2) = (π * β / 2 + π / 2) + k * π := by
    push_cast; ring
  rw [chPacketFn_two, h, Real.cos_add_int_mul_pi, Real.cos_add_pi_div_two, abs_mul,
    abs_neg, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]

/-- **Smallness of `Φ_2` near half-odd integers.** For every odd integer `b` and every real
`β`, `Φ_2((b + β) / 2) ≤ (11 / 7) |β|`. -/
@[collatz_pos_dens "lem_tr_phi2_small"]
theorem chPacketFn_two_odd_add_div_two_le {b : ℤ} (hb : Odd b) (β : ℝ) :
    chPacketFn 2 ((b + β) / 2) ≤ 11 / 7 * |β| := by
  rw [chPacketFn_two_odd_add_div_two hb]
  refine Real.abs_sin_le_abs.trans ?_
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
  nlinarith [abs_nonneg β, Real.pi_lt_d4]

end CollatzPosDens
