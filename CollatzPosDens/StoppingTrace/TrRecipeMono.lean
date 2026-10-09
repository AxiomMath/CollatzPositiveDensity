/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RecipeMap
public import CollatzPosDens.Transfer.HDef
public import CollatzPosDens.Transfer.Beta

/-!
# Monotonicity of the recipe map

The recipe map `recipeMap q = q + windowLength q + T_* + 1` is monotone: for `q ≤ q'` the scale
schedule satisfies `betaStar q ≤ betaStar q'`, hence the window length
`windowLength q = ⌈4 betaStar q / 35⌉ + 8192` satisfies `windowLength q ≤ windowLength q'`, and
therefore `recipeMap q ≤ recipeMap q'`.

## Main results

* `CollatzPosDens.recipeMap_le_recipeMap`: for `q ≤ q'` in `ℕ`, `recipeMap q ≤ recipeMap q'`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The recipe map is monotone: for `q ≤ q'` in `ℕ`, `recipeMap q ≤ recipeMap q'`. -/
@[collatz_pos_dens "lem_tr_recipe_mono"]
theorem recipeMap_le_recipeMap {q q' : ℕ} (h : q ≤ q') : recipeMap q ≤ recipeMap q' := by
  have hβ := betaStar_monotone h
  have hh : windowLength q ≤ windowLength q' := by
    rw [windowLength_eq_div, windowLength_eq_div]
    omega
  rw [recipeMap_def, recipeMap_def]
  omega

end CollatzPosDens
