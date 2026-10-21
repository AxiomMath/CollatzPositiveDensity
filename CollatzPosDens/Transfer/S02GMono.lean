/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RecipeMap
public import CollatzPosDens.Transfer.S02HMono

/-!
# Monotonicity of the recipe map `𝔤`

For every Fourier index `ι`, the recipe map `𝔤_ι(u) = u + h_*(ι, u) + T_*(ι) + 1` is
nondecreasing in `u`: both summands `u` and the window length `h_*(ι, u)` are nondecreasing, and
`T_*(ι) + 1` is constant.

## Main results

* `CollatzPosDens.recipeMap_le_of_le`: `𝔤_ι(u) ≤ 𝔤_ι(u')` whenever `u ≤ u'`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The recipe map is nondecreasing: for every index `ι`, `𝔤_ι(u) ≤ 𝔤_ι(u')` whenever
`u ≤ u'`. -/
@[collatz_pos_dens "lem_s02_g_mono"]
theorem recipeMap_le_of_le (ι : FIndex) {u u' : ℕ} (h : u ≤ u') :
    recipeMap ι u ≤ recipeMap ι u' := by
  rw [recipeMap_def, recipeMap_def]
  have := windowLength_le_of_le ι h
  omega

end CollatzPosDens
