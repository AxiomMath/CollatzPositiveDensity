/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A root dominates the logarithm

For every real `x ≥ 2^131072` we have `1280 log x < x^{1/2048}`.

Put `δ = 1/4096`, so that `x^{1/2048} = x^δ · x^δ` and `x^δ ≥ (2^131072)^δ = 2^32`. The
elementary bound `log x ≤ x^δ / δ = 4096 x^δ` gives
`1280 log x ≤ 1280 · 4096 · x^δ < 2^32 · x^δ ≤ x^δ · x^δ = x^{1/2048}`.

## Main results

* `CollatzPosDens.mul_log_lt_rpow_of_two_pow_131072_le`: `1280 log x < x^{1/2048}` for
  `x ≥ 2^131072`.

## Implementation notes

Mazur's proof compares `x^δ / log x` with its value at `x₀ = 2^131072` by the mean value
theorem, using numerical bounds on `log 2`. Here the general inequality `log x ≤ x^δ / δ`
replaces that monotonicity argument: since `1280 / δ = 1280 · 4096 < 2^32 ≤ x^δ`, no bound on
`log 2` is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §13.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- A root dominates the logarithm: for every real `x ≥ 2^131072`, `1280 log x < x^{1/2048}`. -/
@[collatz_pos_dens "lem_mx_root_vs_log"]
theorem mul_log_lt_rpow_of_two_pow_131072_le {x : ℝ} (hx : (2 : ℝ) ^ 131072 ≤ x) :
    1280 * Real.log x < x ^ ((1 : ℝ) / 2048) := by
  have h0 : (0 : ℝ) < (2 : ℝ) ^ 131072 := by positivity
  have hx0 : 0 < x := h0.trans_le hx
  set δ : ℝ := 1 / 4096 with hδ
  have hδ0 : 0 < δ := by norm_num [hδ]
  have hbase : ((2 : ℝ) ^ 131072) ^ δ = 2 ^ 32 := by
    have : (2 : ℝ) ^ 131072 = ((2 : ℝ) ^ 32) ^ (4096 : ℕ) := by rw [← pow_mul]
    rw [this, hδ, one_div]
    rw [show (4096 : ℝ) = ((4096 : ℕ) : ℝ) by norm_num]
    exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
  have hroot : (2 : ℝ) ^ 32 ≤ x ^ δ := by
    rw [← hbase]
    exact Real.rpow_le_rpow h0.le hx hδ0.le
  have hpos : 0 < x ^ δ := Real.rpow_pos_of_pos hx0 δ
  have hlog : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div hx0.le hδ0
  have hsplit : x ^ ((1 : ℝ) / 2048) = x ^ δ * x ^ δ := by
    rw [← Real.rpow_add hx0, hδ]; norm_num
  rw [hsplit]
  have hdiv : x ^ δ / δ = 4096 * x ^ δ := by rw [hδ]; field_simp
  rw [hdiv] at hlog
  calc 1280 * Real.log x ≤ 1280 * (4096 * x ^ δ) := by gcongr
    _ < 2 ^ 32 * x ^ δ := by nlinarith
    _ ≤ x ^ δ * x ^ δ := by gcongr

end CollatzPosDens
