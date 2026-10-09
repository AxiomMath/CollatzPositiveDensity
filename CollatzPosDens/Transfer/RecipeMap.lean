/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Tstar
public import CollatzPosDens.Transfer.HDef
public import Mathlib.Order.Monotone.Basic

/-!
# The recipe map `𝔤`

The recipe map is `𝔤 : ℕ → ℕ`, `𝔤(q) := q + h_*(q) + T_* + 1`, where `h_*` is the window length
and `T_* = 101` is the low-count threshold. Since `h_*` is monotone and `h_*(q) ≥ 8192`, the map
`𝔤` is strictly increasing and strictly inflationary, with `𝔤(q) ≥ q + 8192 + 102`.

## Main definitions

* `CollatzPosDens.recipeMap`: the recipe map `𝔤`.

## Main results

* `CollatzPosDens.recipeMap_def`: `𝔤(q) = q + h_*(q) + T_* + 1`.
* `CollatzPosDens.recipeMap_eq`: `𝔤(q) = q + h_*(q) + 102`.
* `CollatzPosDens.recipeMap_strictMono`: `𝔤` is strictly increasing.
* `CollatzPosDens.recipeMap_monotone`: `𝔤` is monotone.
* `CollatzPosDens.lt_recipeMap`: `q < 𝔤(q)`.
* `CollatzPosDens.add_le_recipeMap`: `q + 8192 + 102 ≤ 𝔤(q)`.
* `CollatzPosDens.tStar_lt_recipeMap`: `T_* < 𝔤(q)`.

## Implementation notes

`h_*` is defined through a real ceiling, so `𝔤` is `noncomputable`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The recipe map `𝔤(q) := q + h_*(q) + T_* + 1`. -/
@[collatz_pos_dens "def_recipe_map"]
noncomputable def recipeMap (q : ℕ) : ℕ := q + windowLength q + tStar + 1

/-- `𝔤(q) = q + h_*(q) + T_* + 1`. -/
theorem recipeMap_def (q : ℕ) : recipeMap q = q + windowLength q + tStar + 1 := rfl

/-- `𝔤(q) = q + h_*(q) + 102`. -/
theorem recipeMap_eq (q : ℕ) : recipeMap q = q + windowLength q + 102 := by
  rw [recipeMap_def, add_assoc, tStar_add_one]

/-- `q + 8192 + 102 ≤ 𝔤(q)`. -/
theorem add_le_recipeMap (q : ℕ) : q + 8192 + 102 ≤ recipeMap q := by
  rw [recipeMap_eq]; have := le_windowLength q; omega

/-- The recipe map is strictly inflationary. -/
theorem lt_recipeMap (q : ℕ) : q < recipeMap q := by
  have := add_le_recipeMap q; omega

/-- The recipe map is strictly increasing. -/
theorem recipeMap_strictMono : StrictMono recipeMap := by
  intro a b hab
  rw [recipeMap_def, recipeMap_def]
  have := windowLength_monotone hab.le
  omega

/-- The recipe map is monotone. -/
theorem recipeMap_monotone : Monotone recipeMap := recipeMap_strictMono.monotone

/-- `T_* < 𝔤(q)` for every `q`. -/
theorem tStar_lt_recipeMap (q : ℕ) : tStar < recipeMap q := by
  rw [recipeMap_def]; omega

end CollatzPosDens
