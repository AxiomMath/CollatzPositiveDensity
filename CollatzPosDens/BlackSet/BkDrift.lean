/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope

/-!
# The drift `δ₀ = α - 1 / 4`

The real constant `δ₀ := α - 1 / 4`, where `α = log 2 / log 9` is the slope of the black set.
Since `9 < 2 ^ 4` and `2 ^ 3 < 9`, we have `1 / 4 < α < 1 / 3`, so `0 < δ₀ < 1 / 12`.

## Main definitions

* `CollatzPosDens.drift`: the constant `α - 1 / 4`.

## Main results

* `CollatzPosDens.drift_pos`: `0 < δ₀`.
* `CollatzPosDens.drift_lt_one_div_twelve`: `δ₀ < 1 / 12`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The drift `δ₀ := α - 1 / 4`, where `α = log 2 / log 9` is `alpha`. -/
@[collatz_pos_dens "def_bk_drift"]
noncomputable def drift : ℝ := alpha - 1 / 4

/-- `drift` equals `alpha - 1 / 4`. -/
lemma drift_def : drift = alpha - 1 / 4 := rfl

/-- `1 / 4 < α`, since `9 < 2 ^ 4`. -/
lemma one_div_four_lt_alpha : 1 / 4 < alpha := by
  rw [alpha_def, lt_div_iff₀ (Real.log_pos (by norm_num))]
  have : Real.log 9 < Real.log (2 ^ 4) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at this
  push_cast at this
  linarith

/-- The drift is positive. -/
lemma drift_pos : 0 < drift := by
  rw [drift_def]
  linarith [one_div_four_lt_alpha]

/-- The drift is less than `1 / 12`, since `α < 1 / 3`. -/
lemma drift_lt_one_div_twelve : drift < 1 / 12 := by
  rw [drift_def]
  linarith [alpha_lt_one_div_three]

end CollatzPosDens
