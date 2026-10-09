/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CM
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Mconst
public import CollatzPosDens.Recipe.Tower
public import CollatzPosDens.Recipe.PhConductor
public import CollatzPosDens.Recipe.PhDensityChain
public import CollatzPosDens.Recipe.PhEndpoint
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A tower bound for the inverse density constant

The inverse of the density constant is below a tower of three twos topped by `140214`:
`1 / c_M < tow_3(140214)`.

Write `Y₁ = log₂ (1/c_M)`, `Y₂ = log₂ Y₁` and `Y₃ = log₂ Y₂`. Chaining the density chain
`Y₃ < log₂ q_* + 1`, the conductor bound `log₂ q_* + 1 < 16 + N_* δ` and the real endpoint
`16 + N_* δ < 140214` gives `Y₃ < 140214`. Since `1/c_M ≥ 2^33`, we have `Y₁ ≥ 33` and `Y₂ > 0`,
so exponentiating three times (`log₂ y < a ⟹ y < 2^a` for `y > 0`) yields
`Y₂ < tow_1(140214)`, `Y₁ < tow_2(140214)` and `1/c_M < tow_3(140214)`.

## Main results

* `CollatzPosDens.inv_densityConst_lt_tower`: `1 / c_M < tow_3(140214)`.

## Implementation notes

The tower is compared in `ℝ` through its cast; it is only ever unfolded one level at a time by
`tower_succ`, so no tower value is evaluated.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The inverse of the density constant `densityConst` is below the tower of height three over
`140214`: `1 / c_M < tow_3(140214)`. -/
@[collatz_pos_dens "lem_invc_tower"]
theorem inv_densityConst_lt_tower : 1 / densityConst < (tower 3 140214 : ℝ) := by
  have hY3 : logb 2 (logb 2 (logb 2 densityConst⁻¹)) < (tower 0 140214 : ℝ) := by
    rw [tower_zero]
    have h1 := logb_logb_logb_inv_densityConst_lt
    have h2 := logb_conductor_add_one_lt
    have h3 := sixteen_add_generationThreshold_mul_logGrowthRate_lt
    push_cast
    linarith
  have hY1 : (33 : ℝ) ≤ logb 2 densityConst⁻¹ := by
    have h := logb_le_logb_of_le (b := 2) (by norm_num) (by positivity)
      two_pow_33_le_inv_densityConst
    rw [logb_pow, logb_self_eq_one (by norm_num)] at h
    push_cast at h
    linarith
  have hY2 : 0 < logb 2 (logb 2 densityConst⁻¹) :=
    logb_pos (by norm_num) (by linarith)
  have hc : 0 < densityConst⁻¹ := inv_pos.2 densityConst_pos
  rw [one_div]
  exact lt_tower_succ_of_logb_lt hc <| lt_tower_succ_of_logb_lt (by linarith) <|
    lt_tower_succ_of_logb_lt hY2 hY3

end CollatzPosDens
