/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.PhQstarValue

/-!
# A lower bound for the conductor

The conductor `q_*` of the recipe, an explicit 49-digit integer, satisfies `352 ≤ q_*`.

## Main results

* `CollatzPosDens.three_hundred_fifty_two_le_conductor`: `352 ≤ q_*`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §15.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The conductor `q_*` is at least `352`. -/
@[collatz_pos_dens "lem_ph_qstar_floor"]
theorem three_hundred_fifty_two_le_conductor : 352 ≤ conductor := by
  rw [conductor_value]
  norm_num

end CollatzPosDens
