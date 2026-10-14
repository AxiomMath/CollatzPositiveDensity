/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.F
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The physical exponent `B_ph`

The physical exponent of the recipe is the real number
$$B_{\mathrm{ph}} := 23 + \log_2 F,$$
where `F = 3 (C + 1)` is the error prefactor. It enters the generation threshold `N_*` and the
terminal threshold `N_t` through ceilings.

## Main definitions

* `CollatzPosDens.physicalExponent`: the physical exponent `B_ph = 23 + log₂ F ∈ ℝ`.

## Main results

* `CollatzPosDens.physicalExponent_def`: the defining formula of `B_ph`.
* `CollatzPosDens.physicalExponent_eq`: `B_ph = 23 + log₂ 3 + log₂ (C + 1)`.
* `CollatzPosDens.physicalExponent_gt`: `23 < B_ph`, hence `physicalExponent_pos`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The physical exponent `B_ph := 23 + log₂ F ∈ ℝ`, where `F` is the error prefactor. -/
@[collatz_pos_dens "def_ph_Bphys"]
noncomputable def physicalExponent : ℝ := 23 + Real.logb 2 errorPrefactor

/-- The defining formula of the physical exponent. -/
theorem physicalExponent_def : physicalExponent = 23 + Real.logb 2 errorPrefactor := rfl

/-- `B_ph = 23 + log₂ 3 + log₂ (C + 1)`, unfolding `F = 3 (C + 1)`. -/
theorem physicalExponent_eq :
    physicalExponent = 23 + Real.logb 2 3 + Real.logb 2 (mixingConst + 1) := by
  rw [physicalExponent_def, errorPrefactor_def,
    Real.logb_mul (by norm_num) (by linarith [mixingConst_pos])]
  ring

/-- `23 < B_ph`, since `1 < F`. -/
theorem physicalExponent_gt : 23 < physicalExponent := by
  linarith [Real.logb_pos (b := 2) (x := errorPrefactor) (by norm_num)
    (by linarith [lt_errorPrefactor]), physicalExponent_def]

/-- The physical exponent is positive. -/
theorem physicalExponent_pos : 0 < physicalExponent := by
  linarith [physicalExponent_gt]

end CollatzPosDens
