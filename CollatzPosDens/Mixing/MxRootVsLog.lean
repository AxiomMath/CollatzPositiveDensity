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

For every real `x ≥ 2^80000` we have `1280 log x < x^{1/2048}`.

Put `ε = 1/5120`, so that `x^{1/2048} = x^ε · x^{3/10240}` and
`x^{3/10240} ≥ (2^80000)^{3/10240} = 2^{375/16} ≥ 2^23`. The elementary bound
`log x ≤ x^ε / ε = 5120 x^ε` gives
`1280 log x ≤ 1280 · 5120 · x^ε < 2^23 · x^ε ≤ x^{3/10240} · x^ε = x^{1/2048}`.

## Main results

* `CollatzPosDens.mul_log_lt_rpow_of_two_pow_80000_le`: `1280 log x < x^{1/2048}` for
  `x ≥ 2^80000`.

## Implementation notes

The source compares `x^δ / log x` (`δ = 1/4096`) with its value at `x₀ = 2^80000` by the mean
value theorem, using the numerical bounds on `log 2`. Here the general inequality
`log x ≤ x^ε / ε` with `ε = 1/5120` replaces that monotonicity argument: since
`1280 / ε = 6553600 < 2^23 ≤ x^{1/2048 - ε}`, no bound on `log 2` is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A root dominates the logarithm: for every real `x ≥ 2^80000`, `1280 log x < x^{1/2048}`. -/
@[collatz_pos_dens "lem_mx_root_vs_log"]
theorem mul_log_lt_rpow_of_two_pow_80000_le {x : ℝ} (hx : (2 : ℝ) ^ 80000 ≤ x) :
    1280 * Real.log x < x ^ ((1 : ℝ) / 2048) := by
  have h0 : (0 : ℝ) < (2 : ℝ) ^ 80000 := by positivity
  have hx0 : 0 < x := h0.trans_le hx
  set ε : ℝ := 1 / 5120 with hε
  have hbase : (2 : ℝ) ^ (23 : ℝ) ≤ ((2 : ℝ) ^ 80000) ^ ((3 : ℝ) / 10240) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hroot : (2 : ℝ) ^ 23 ≤ x ^ ((3 : ℝ) / 10240) := by
    exact_mod_cast hbase.trans (Real.rpow_le_rpow h0.le hx (by norm_num))
  have hpos : 0 < x ^ ε := Real.rpow_pos_of_pos hx0 ε
  have hlog : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hx0.le (by norm_num [hε])
  rw [show x ^ ((1 : ℝ) / 2048) = x ^ ((3 : ℝ) / 10240) * x ^ ε by
    rw [← Real.rpow_add hx0, hε]
    norm_num]
  have hdiv : x ^ ε / ε = 5120 * x ^ ε := by rw [hε]; field_simp
  rw [hdiv] at hlog
  calc 1280 * Real.log x ≤ 1280 * (5120 * x ^ ε) := by gcongr
    _ < 2 ^ 23 * x ^ ε := by nlinarith
    _ ≤ x ^ ((3 : ℝ) / 10240) * x ^ ε := by gcongr

end CollatzPosDens
