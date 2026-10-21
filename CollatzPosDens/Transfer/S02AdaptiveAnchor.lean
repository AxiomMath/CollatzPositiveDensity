/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The adaptive anchor constant `b_an`

The adaptive anchor constant is the rational number
$$b_{\mathrm{an}} := \frac{25000000000}{17328679514} = \frac{12500000000}{8664339757},$$
the reciprocal of `u = 17328679514/25000000000 = 0.69314718056`. Since `u` exceeds `log 2`
(by about `5.4 · 10⁻¹⁴`), the constant satisfies `0 < b_an < 1 / log 2`.

The upper bound is proved from the partial sum of the exponential series: for `x ≥ 0`,
`∑_{j=0}^{25} x^j / j! ≤ e^x` (`Real.sum_le_exp_of_nonneg`), and at `x = u` the left-hand side
exceeds `2` by `1.09 · 10⁻¹³` in exact rational arithmetic. Hence `e^u > 2`, i.e. `u > log 2`.

## Main definitions

* `CollatzPosDens.bAn`: the adaptive anchor constant `b_an = 12500000000/8664339757 : ℚ`.

## Main results

* `CollatzPosDens.bAn_eq`: the value of `b_an`.
* `CollatzPosDens.bAn_eq_inv`: `b_an = (17328679514/25000000000)⁻¹`.
* `CollatzPosDens.log_two_lt_inv_bAn`: `log 2 < 1 / b_an`.
* `CollatzPosDens.bAn_pos_and_lt`: `0 < b_an < 1 / log 2`.
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- The adaptive anchor constant `b_an := 25000000000/17328679514 ∈ ℚ`, that is
`12500000000/8664339757`. -/
@[collatz_pos_dens "def_s02_adaptive_anchor"]
def bAn : ℚ := 12500000000 / 8664339757

/-- The value of the adaptive anchor constant. -/
@[simp]
theorem bAn_eq : bAn = 12500000000 / 8664339757 := rfl

/-- The adaptive anchor constant is the reciprocal of `u = 17328679514/25000000000`. -/
theorem bAn_eq_inv : bAn = (17328679514 / 25000000000 : ℚ)⁻¹ := by
  norm_num [bAn_eq]

/-- The adaptive anchor constant is positive. -/
theorem bAn_pos : 0 < bAn := by norm_num

/-- The reciprocal `u = 17328679514/25000000000` of `b_an` exceeds `log 2`: the degree-25
partial sum of the exponential series at `u` already exceeds `2`. -/
theorem log_two_lt_inv_bAn : log 2 < ((bAn : ℚ) : ℝ)⁻¹ := by
  set u : ℚ := 17328679514 / 25000000000 with hu
  have hq : (2 : ℚ) < ∑ i ∈ range 26, u ^ i / (i.factorial : ℚ) := by
    norm_num [hu, Finset.sum_range_succ, Nat.factorial]
  have hr : (2 : ℝ) < ∑ i ∈ range 26, (u : ℝ) ^ i / (i.factorial : ℝ) := by
    exact_mod_cast hq
  have hexp : (2 : ℝ) < exp (u : ℝ) :=
    hr.trans_le (Real.sum_le_exp_of_nonneg (by positivity) 26)
  rw [bAn_eq_inv, Rat.cast_inv, inv_inv, ← hu]
  exact (log_lt_iff_lt_exp (by norm_num)).2 hexp

/-- The adaptive anchor constant satisfies `0 < b_an < 1 / log 2`. -/
@[collatz_pos_dens "lem_s02_adaptive_anchor"]
theorem bAn_pos_and_lt : 0 < (bAn : ℝ) ∧ (bAn : ℝ) < 1 / log 2 := by
  have h0 : (0 : ℝ) < bAn := by exact_mod_cast bAn_pos
  refine ⟨h0, ?_⟩
  have hl : 0 < log 2 := log_pos (by norm_num)
  have := log_two_lt_inv_bAn
  rw [lt_div_iff₀ hl]
  calc (bAn : ℝ) * log 2 < bAn * (bAn : ℝ)⁻¹ := mul_lt_mul_of_pos_left this h0
    _ = 1 := mul_inv_cancel₀ h0.ne'

end CollatzPosDens
