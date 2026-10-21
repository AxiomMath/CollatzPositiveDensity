/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06CountLevel
public import CollatzPosDens.Transfer.MxGate

/-!
# The clipping level of the count is above the gate

For every integer `t ≥ 1`, the clipping level `n_ct(t)` of `CollatzPosDens.countLevel` is at
least the mixing gate level `n₀ = 2^80` of `CollatzPosDens.mxGateLevel`. Indeed, with
`a = a_mx(o) = 18693/10000`, the base `2^{420} t (1 + log t)` is at least `2^{420}`, so
`n_ct(t) ≥ x_ct(t) ≥ 2^{420/a} ≥ 2^{80}`, as `420/a = 4200000/18693 > 80`.

## Main results

* `CollatzPosDens.two_pow_le_countX`: `2^80 ≤ x_ct(t)` for `t ≥ 1`.
* `CollatzPosDens.mxGateLevel_le_countLevel`: `n₀ ≤ n_ct(t)` for `t ≥ 1`.
* `CollatzPosDens.two_pow_le_countLevel`: `2^80 ≤ n_ct(t)` as real numbers, for `t ≥ 1`.
* `CollatzPosDens.log_countLevel_pos`: `0 < log n_ct(t)` for `t ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipping base is at least `2^80` for `t ≥ 1`. -/
theorem two_pow_le_countX {t : ℕ} (ht : 1 ≤ t) : (2 : ℝ) ^ 80 ≤ countX t := by
  have ha : (0 : ℝ) < amix .o := by rw [amix_cast_o]; norm_num
  rw [← Real.rpow_le_rpow_iff (by positivity) (countX_nonneg t) ha, countX_rpow_amix]
  refine le_trans ?_ (two_pow_le_countX_base ht)
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  rw [amix_cast_o]; norm_num

/-- The clipping level of the count is above the gate: `n₀ ≤ n_ct(t)` for `t ≥ 1`. -/
@[collatz_pos_dens "lem_s06_count_gate"]
theorem mxGateLevel_le_countLevel {t : ℕ} (ht : 1 ≤ t) : mxGateLevel ≤ countLevel t := by
  have h := (two_pow_le_countX ht).trans (countX_le_countLevel t)
  rw [mxGateLevel_def]
  exact_mod_cast h

/-- The clipping level is at least `2^80` as a real number, for `t ≥ 1`. -/
theorem two_pow_le_countLevel {t : ℕ} (ht : 1 ≤ t) : (2 : ℝ) ^ 80 ≤ countLevel t :=
  (two_pow_le_countX ht).trans (countX_le_countLevel t)

/-- The logarithm of the clipping level is positive for `t ≥ 1`. -/
theorem log_countLevel_pos {t : ℕ} (ht : 1 ≤ t) : 0 < Real.log (countLevel t) :=
  Real.log_pos (lt_of_lt_of_le (by norm_num) (two_pow_le_countLevel ht))

end CollatzPosDens
