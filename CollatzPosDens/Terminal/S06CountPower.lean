/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr

/-!
# A logarithmic power below a small power

For every real `t ≥ 1`,
$$(1 + \log t)^{28693/37386} < 2^8\, t^{1079/205623},$$
with positive real powers. Writing `y = log t ≥ 0`, the left side is at most `1 + y` since the
exponent is at most `1`, while `t^δ = e^{δ y} ≥ 1 + δ y ≥ δ (1 + y)` for `δ = 1079/205623 ≤ 1`;
hence `(1 + y)^r ≤ t^δ / δ < 2^8 t^δ`.

## Main results

* `CollatzPosDens.one_add_log_rpow_lt`: `(1 + log t)^{28693/37386} < 2^8 t^{1079/205623}`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- A logarithmic power below a small power: for `t ≥ 1`,
`(1 + log t)^{28693/37386} < 2^8 t^{1079/205623}` (positive real powers). -/
@[collatz_pos_dens "lem_s06_count_power"]
theorem one_add_log_rpow_lt {t : ℝ} (ht : 1 ≤ t) :
    (1 + Real.log t) ^ (28693 / 37386 : ℝ) < 2 ^ 8 * t ^ (1079 / 205623 : ℝ) := by
  have hy : 0 ≤ Real.log t := Real.log_nonneg ht
  have h1 : (1 + Real.log t) ^ (28693 / 37386 : ℝ) ≤ 1 + Real.log t := by
    calc (1 + Real.log t) ^ (28693 / 37386 : ℝ) ≤ (1 + Real.log t) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = 1 + Real.log t := Real.rpow_one _
  have h2 : 1 + 1079 / 205623 * Real.log t ≤ t ^ (1079 / 205623 : ℝ) := by
    rw [Real.rpow_def_of_pos (by linarith), mul_comm]
    linarith [Real.add_one_le_exp (Real.log t * (1079 / 205623))]
  linarith

end CollatzPosDens
