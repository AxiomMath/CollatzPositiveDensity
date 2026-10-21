/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Tstar
public import CollatzPosDens.Transfer.S02HDef
public import Mathlib.Order.Monotone.Basic

/-!
# The recipe map `𝔤`

For a Fourier index `ι`, the recipe map is `𝔤_ι : ℕ → ℕ`, `𝔤_ι(q) := q + h_*(ι, q) + T_*(ι) + 1`,
where `h_*` is the window length and `T_*(ι)` is the low-count threshold (`T_*(o) = 192`,
`T_*(b) = 168`). Its iterates `p_i(ι) = 𝔤_ι^i(p_init(ι))` are the schedule positions. Since
`h_*(ι, ·)` is monotone and `h_*(ι, q) ≥ H_*(ι)`, the map `𝔤_ι` is strictly increasing and strictly
inflationary, with `𝔤_ι(q) ≥ q + H_*(ι) + T_*(ι) + 1`.

## Main definitions

* `CollatzPosDens.recipeMap`: the recipe map `𝔤_ι`.

## Main results

* `CollatzPosDens.recipeMap_def`: `𝔤_ι(q) = q + h_*(ι, q) + T_*(ι) + 1`.
* `CollatzPosDens.recipeMap_strictMono`: `𝔤_ι` is strictly increasing.
* `CollatzPosDens.recipeMap_monotone`: `𝔤_ι` is monotone.
* `CollatzPosDens.lt_recipeMap`: `q < 𝔤_ι(q)`.
* `CollatzPosDens.recipeMap_o_eq`, `CollatzPosDens.recipeMap_b_eq`: `𝔤_o(q) = q + h_*(o, q) + 193`
  and `𝔤_b(q) = q + h_*(b, q) + 169`.
* `CollatzPosDens.add_le_recipeMap`: `q + H_*(ι) + T_*(ι) + 1 ≤ 𝔤_ι(q)`.
* `CollatzPosDens.tStar_lt_recipeMap`: `T_*(ι) < 𝔤_ι(q)`.

## Implementation notes

`h_*` is defined through a real ceiling, so `𝔤_ι` is `noncomputable`; it should be used through
`recipeMap_def`, `recipeMap_strictMono` and `add_le_recipeMap`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The recipe map `𝔤_ι(q) := q + h_*(ι, q) + T_*(ι) + 1`. -/
@[collatz_pos_dens "def_recipe_map"]
noncomputable def recipeMap (ι : FIndex) (q : ℕ) : ℕ := q + windowLength ι q + tStar ι + 1

/-- `𝔤_ι(q) = q + h_*(ι, q) + T_*(ι) + 1`. -/
theorem recipeMap_def (ι : FIndex) (q : ℕ) :
    recipeMap ι q = q + windowLength ι q + tStar ι + 1 := rfl

/-- `𝔤_o(q) = q + h_*(o, q) + 193`. -/
theorem recipeMap_o_eq (q : ℕ) : recipeMap .o q = q + windowLength .o q + 193 := by
  rw [recipeMap_def, add_assoc, tStar_o_succ]

/-- `𝔤_b(q) = q + h_*(b, q) + 169`. -/
theorem recipeMap_b_eq (q : ℕ) : recipeMap .b q = q + windowLength .b q + 169 := by
  rw [recipeMap_def, add_assoc, tStar_b_succ]

/-- `q + H_*(ι) + T_*(ι) + 1 ≤ 𝔤_ι(q)`. -/
theorem add_le_recipeMap (ι : FIndex) (q : ℕ) :
    q + Hstar ι + tStar ι + 1 ≤ recipeMap ι q := by
  have := le_windowLength ι q
  rw [recipeMap_def]
  omega

/-- The recipe map is strictly inflationary. -/
theorem lt_recipeMap (ι : FIndex) (q : ℕ) : q < recipeMap ι q := by
  rw [recipeMap_def]
  omega

/-- The recipe map is strictly increasing. -/
theorem recipeMap_strictMono (ι : FIndex) : StrictMono (recipeMap ι) := by
  intro a b hab
  rw [recipeMap_def, recipeMap_def]
  have := windowLength_monotone ι hab.le
  omega

/-- The recipe map is monotone. -/
theorem recipeMap_monotone (ι : FIndex) : Monotone (recipeMap ι) :=
  (recipeMap_strictMono ι).monotone

/-- `T_*(ι) < 𝔤_ι(q)` for every `q`. -/
theorem tStar_lt_recipeMap (ι : FIndex) (q : ℕ) : tStar ι < recipeMap ι q := by
  rw [recipeMap_def]
  omega

end CollatzPosDens
