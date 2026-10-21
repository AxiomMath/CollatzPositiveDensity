/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageHold
public import CollatzPosDens.Transfer.RecipeMap
public import CollatzPosDens.Transfer.S02GMono

/-!
# The stage deadline map

For a Fourier index `ι`, a gap threshold `G ≥ 0` and a run length `d ≥ 1`, write
`h = h^st_G(ι)` for the clearance time after a small gap and `𝔤_ι` for the recipe map. The
*stage deadline map* is
```
𝔣^{G,d}_ι(u) := max(u + d h, 𝔤_ι(u + (d - 1) h)) ∈ ℕ.
```
A stage begun by time `u` makes at most `d - 1` departures from points of gap less than `G`,
each followed by a stop within `h` steps, and then one more departure, followed by a stop within
`h` steps (small gap) or by time `𝔤_ι` of the departure time (large gap); so it is complete by
time `𝔣^{G,d}_ι(u)`.

## Main definitions

* `CollatzPosDens.trStageMap ι G d u`: the stage deadline map `𝔣^{G,d}_ι(u)`.

## Main results

* `CollatzPosDens.add_mul_le_trStageMap`: `u + d h ≤ 𝔣^{G,d}_ι(u)`.
* `CollatzPosDens.recipeMap_le_trStageMap`: `𝔤_ι(u + (d - 1) h) ≤ 𝔣^{G,d}_ι(u)`.
* `CollatzPosDens.trStageMap_monotone`: `𝔣^{G,d}_ι` is monotone.

## Implementation notes

The integers `G ≥ 0` and `d ≥ 1` are natural numbers; the map is defined for every `d ∈ ℕ`,
with truncated subtraction in `d - 1`, which is the true difference when `d ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The stage deadline map
`𝔣^{G,d}_ι(u) := max(u + d h^st_G(ι), 𝔤_ι(u + (d - 1) h^st_G(ι)))`. -/
@[collatz_pos_dens "def_c3_stage_map"]
noncomputable def trStageMap (ι : FIndex) (G d u : ℕ) : ℕ :=
  max (u + d * trStageHold ι G) (recipeMap ι (u + (d - 1) * trStageHold ι G))

/-- `𝔣^{G,d}_ι(u) = max(u + d h^st_G(ι), 𝔤_ι(u + (d - 1) h^st_G(ι)))`. -/
theorem trStageMap_def (ι : FIndex) (G d u : ℕ) :
    trStageMap ι G d u =
      max (u + d * trStageHold ι G) (recipeMap ι (u + (d - 1) * trStageHold ι G)) := rfl

/-- `u + d h^st_G(ι) ≤ 𝔣^{G,d}_ι(u)`. -/
theorem add_mul_le_trStageMap (ι : FIndex) (G d u : ℕ) :
    u + d * trStageHold ι G ≤ trStageMap ι G d u :=
  le_max_left _ _

/-- `𝔤_ι(u + (d - 1) h^st_G(ι)) ≤ 𝔣^{G,d}_ι(u)`. -/
theorem recipeMap_le_trStageMap (ι : FIndex) (G d u : ℕ) :
    recipeMap ι (u + (d - 1) * trStageHold ι G) ≤ trStageMap ι G d u :=
  le_max_right _ _

/-- The stage deadline map is strictly inflationary: `u < 𝔣^{G,d}_ι(u)`. -/
theorem lt_trStageMap (ι : FIndex) (G d u : ℕ) : u < trStageMap ι G d u :=
  (Nat.le_add_right u _).trans_lt
    ((lt_recipeMap ι _).trans_le (recipeMap_le_trStageMap ι G d u))

/-- The stage deadline map is monotone. -/
theorem trStageMap_monotone (ι : FIndex) (G d : ℕ) : Monotone (trStageMap ι G d) := by
  intro u u' h
  exact max_le_max (by omega) (recipeMap_le_of_le ι (by omega))

end CollatzPosDens
