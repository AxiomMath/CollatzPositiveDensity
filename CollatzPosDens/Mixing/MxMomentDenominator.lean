/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxLog2Bounds
public import CollatzPosDens.Transfer.Log3Bounds

/-!
# A lower bound for the moment denominator `2^{1+σ} - 1 - 3^σ`

Let `σ = 65535 / 65536`. This file proves the numerical inequality
$$2^{-20} < 2^{1+\sigma} - 1 - 3^{\sigma}.$$
Writing `t = 1 - σ = 2^{-16}`, the right-hand side is `f(t) = 4 · 2^{-t} - 3 · 3^{-t} - 1`,
and the inequality is `f(t) > t / 16`.

## Main results

* `CollatzPosDens.two_pow_neg_twenty_lt_momentDenominator`:
  `2^{-20} < 2^{1 + 65535/65536} - 1 - 3^{65535/65536}`.

## Implementation notes

Rather than applying the mean value theorem to `f(t) - t / 16` on `[0, 1/128]`, the two
exponentials are bounded directly at the single point `t = 2^{-16}` using `1 + u ≤ exp u`: one
has `2^{-t} = exp(-t log 2) ≥ 1 - t log 2` and `3^{-t} = 1 / exp(t log 3) ≤ 1 / (1 + t log 3)`.
The resulting rational inequality in `log 2` and `log 3` follows from `0.693 < log 2 < 0.694`
and `79/50 ≤ log₂ 3 ≤ 317/200`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- With `σ = 65535/65536`, the moment denominator `2^{1+σ} - 1 - 3^σ` exceeds `2^{-20}`. -/
@[collatz_pos_dens "lem_mx_moment_denominator"]
theorem two_pow_neg_twenty_lt_momentDenominator :
    (2 : ℝ) ^ (-20 : ℤ) <
      (2 : ℝ) ^ (1 + 65535 / 65536 : ℝ) - 1 - (3 : ℝ) ^ (65535 / 65536 : ℝ) := by
  obtain ⟨ha₁, ha₂⟩ := log_two_bounds
  obtain ⟨hb₁, hb₂⟩ := logb_two_three_bounds
  set t : ℝ := 1 / 65536 with ht
  have h2 : (2 : ℝ) ^ (1 + 65535 / 65536 : ℝ) = 4 * exp (-(t * log 2)) := by
    rw [rpow_def_of_pos (by norm_num), ← exp_log (by norm_num : (0 : ℝ) < 4), ← exp_add,
      show (4 : ℝ) = 2 ^ 2 by norm_num, log_pow]
    congr 1; rw [ht]; push_cast; ring
  have h3 : (3 : ℝ) ^ (65535 / 65536 : ℝ) = 3 / exp (t * log 3) := by
    rw [rpow_def_of_pos (by norm_num), eq_div_iff (exp_pos _).ne', ← exp_add]
    conv_rhs => rw [← exp_log (by norm_num : (0 : ℝ) < 3)]
    congr 1; rw [ht]; ring
  have hlog3 : log 3 = logb 2 3 * log 2 := by
    rw [logb, div_mul_cancel₀ _ (log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  set a := log 2
  set b := log 3
  have hb₁' : 79 / 50 * 0.693 < b := by rw [hlog3]; nlinarith
  have hb₂' : b < 317 / 200 * 0.694 := by rw [hlog3]; nlinarith
  have e2 : 1 - t * a ≤ exp (-(t * a)) := by linarith [add_one_le_exp (-(t * a))]
  have e3 : 1 + t * b ≤ exp (t * b) := by linarith [add_one_le_exp (t * b)]
  have htb : 0 < 1 + t * b := by rw [ht]; nlinarith
  have e3' : 3 / exp (t * b) ≤ 3 / (1 + t * b) := div_le_div_of_nonneg_left (by norm_num) htb e3
  rw [h2, h3]
  clear_value t a b
  have hq : 3 / (1 + t * b) < 3 - 4 * t * a - t / 16 := by
    rw [div_lt_iff₀ htb, ht]; nlinarith
  have h20 : (2 : ℝ) ^ (-20 : ℤ) = t / 16 := by rw [ht]; norm_num
  rw [h20]
  nlinarith

end CollatzPosDens
