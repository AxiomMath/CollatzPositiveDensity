/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06CountLog

/-!
# The root of the clipping level of the count

For every integer `t ≥ 1`,
$$\sqrt{n_{\mathrm{ct}}(t) \log n_{\mathrm{ct}}(t)} < 2^{117}\, t^{5000/18693}\,
  (1 + \log t)^{28693/37386},$$
with positive real powers, where `n_ct(t)` is the clipping level `CollatzPosDens.countLevel`.
With `a = a_mx(o) = 18693/10000`, `h = 1 + log t` and `x = x_ct(t)`, one has
`n_ct(t) ≤ 2x`, `log n_ct(t) ≤ 2^8 h` and `x = 2^{420/a} t^{1/a} h^{1/a}`, so
`n log n ≤ 2^{9 + 420/a} t^{1/a} h^{1 + 1/a}`; taking square roots, `1/(2a) = 5000/18693`,
`1/2 + 1/(2a) = 28693/37386` and `9/2 + 210/a < 117`.

## Main results

* `CollatzPosDens.sqrt_countLevel_mul_log_lt`: the displayed inequality, for `t ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `t ≥ 1`, the clipping level `n = countLevel t` satisfies
`√(n log n) < 2^{117} t^{5000/18693} (1 + log t)^{28693/37386}`, with real powers. -/
@[collatz_pos_dens "lem_s06_count_root"]
theorem sqrt_countLevel_mul_log_lt {t : ℕ} (ht : 1 ≤ t) :
    √((countLevel t : ℝ) * Real.log (countLevel t)) <
      2 ^ 117 * (t : ℝ) ^ (5000 / 18693 : ℝ) * (1 + Real.log t) ^ (28693 / 37386 : ℝ) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hh0 : 0 < 1 + Real.log t := by linarith [Real.log_natCast_nonneg t]
  have hL0 := log_countLevel_pos ht
  have hLle := log_countLevel_le ht
  have hn2 := countLevel_le_two_mul ht
  have hx0 := countX_pos ht
  have hn0 : (0 : ℝ) ≤ countLevel t := Nat.cast_nonneg _
  have hx : countX t = (2 ^ 420 : ℝ) ^ (10000 / 18693 : ℝ) * (t : ℝ) ^ (10000 / 18693 : ℝ) *
      (1 + Real.log t) ^ (10000 / 18693 : ℝ) := by
    rw [countX_def, amix_cast_o, Real.mul_rpow (by positivity) hh0.le,
      Real.mul_rpow (by positivity) ht0.le]
    norm_num
  have h420 : (2 ^ 420 : ℝ) ^ (10000 / 18693 : ℝ) < 2 ^ 225 := by
    rw [← Real.rpow_natCast 2 420, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast 2 225]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  set T : ℝ := (t : ℝ) ^ (10000 / 18693 : ℝ) * (1 + Real.log t) ^ (10000 / 18693 : ℝ) with hT
  have hT0 : 0 < T := by positivity
  have hxT : countX t < 2 ^ 225 * T := by
    rw [hx, mul_assoc, ← hT]
    exact mul_lt_mul_of_pos_right h420 hT0
  have hsq : (2 ^ 117 * (t : ℝ) ^ (5000 / 18693 : ℝ) * (1 + Real.log t) ^ (28693 / 37386 : ℝ))
      ^ 2 = 2 ^ 234 * T * (1 + Real.log t) := by
    rw [mul_pow, mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast (_ ^ (5000 / 18693 : ℝ)),
      ← Real.rpow_natCast (_ ^ (28693 / 37386 : ℝ)), ← Real.rpow_mul ht0.le,
      ← Real.rpow_mul hh0.le, hT,
      show ((28693 / 37386 : ℝ) * ((2 : ℕ) : ℝ)) = 10000 / 18693 + 1 by norm_num,
      Real.rpow_add hh0, Real.rpow_one]
    norm_num
    ring
  rw [Real.sqrt_lt' (by positivity), hsq]
  calc (countLevel t : ℝ) * Real.log (countLevel t) ≤ (2 * countX t) * (256 * (1 + Real.log t)) :=
        mul_le_mul hn2 hLle hL0.le (by positivity)
    _ = 2 ^ 9 * (1 + Real.log t) * countX t := by ring
    _ < 2 ^ 9 * (1 + Real.log t) * (2 ^ 225 * T) := mul_lt_mul_of_pos_left hxT (by positivity)
    _ = 2 ^ 234 * T * (1 + Real.log t) := by ring

end CollatzPosDens
