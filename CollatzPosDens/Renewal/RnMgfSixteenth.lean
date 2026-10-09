/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnMgf
public import CollatzPosDens.Renewal.RnMgfFinite

/-!
# The exponential moment `M₄₅` at `t = 1/16`

We show `M₄₅(1/16) ≤ 5/4`. Put `x = e^{1/16}`. From `e^{-1/16} ≥ 1 - 1/16` we get
`x ≤ 16/15`, hence `11 x < 16`, so the closed form `M₄₅(1/16) = 5x / (16 - 11x)` applies.
The map `x ↦ 5x / (16 - 11x)` is increasing on `(0, 16/11)` and equals `5/4` at `x = 16/15`.

## Main results

* `CollatzPosDens.mgfNu45_one_div_sixteen_le`: `M₄₅(1/16) ≤ 5/4` in `ℝ≥0∞`.
* `CollatzPosDens.mgfNu45_one_div_sixteen_toReal_le`: the same bound for the real value.

## Implementation notes

`M₄₅` is valued in `ℝ≥0∞`, so the bound is stated there; since the bound is finite it
implies `M₄₅(1/16) < ∞`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.3.
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

private lemma exp_one_div_sixteen_le : exp (1 / 16 : ℝ) ≤ 16 / 15 :=
  (exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)).trans_eq (by norm_num)

/-- `M₄₅(1/16) ≤ 5/4` in `ℝ≥0∞`. -/
@[collatz_pos_dens "lem_rn_mgf_sixteenth"]
theorem mgfNu45_one_div_sixteen_le : mgfNu45 (1 / 16) ≤ 5 / 4 := by
  have hx := exp_one_div_sixteen_le
  have h11 : 11 * exp (1 / 16 : ℝ) < 16 := by linarith
  rw [mgfNu45_eq_div h11]
  calc ENNReal.ofReal (5 * exp (1 / 16 : ℝ) / (16 - 11 * exp (1 / 16 : ℝ)))
      ≤ ENNReal.ofReal (5 / 4) :=
        ENNReal.ofReal_le_ofReal ((div_le_iff₀ (by linarith)).2 (by linarith))
    _ = 5 / 4 := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num

/-- The real value of `M₄₅(1/16)` is at most `5/4`. -/
theorem mgfNu45_one_div_sixteen_toReal_le : (mgfNu45 (1 / 16)).toReal ≤ 5 / 4 :=
  (ENNReal.toReal_mono (ENNReal.div_ne_top (by simp) (by simp))
    mgfNu45_one_div_sixteen_le).trans_eq (by norm_num)

end CollatzPosDens
