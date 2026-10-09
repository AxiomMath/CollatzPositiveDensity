/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Notation

/-!
# The low-count threshold `T_*`

The low-count threshold is the natural number `T_* = 101`, the maximal number of white points
tolerated along a stopping trace up to time `P_* - 1`. It enters the recipe map
`CollatzPosDens.recipeMap q = q + h_*(q) + T_* + 1`, and satisfies `T_* + 1 = 102 ≤ 1024 = p_init`.

## Main definitions

* `CollatzPosDens.tStar`: the natural number `T_* = 101`.

## Main results

* `CollatzPosDens.tStar_def`: `T_* = 101`.
* `CollatzPosDens.tStar_add_one`: `T_* + 1 = 102`.
* `CollatzPosDens.tStar_pos`: `0 < T_*`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The low-count threshold `T_* = 101`, the maximal number of white points tolerated along
a stopping trace. -/
@[collatz_pos_dens "def_Tstar"]
def tStar : ℕ := 101

/-- The low-count threshold equals `101`. -/
theorem tStar_def : tStar = 101 := rfl

/-- `T_* + 1 = 102`. -/
theorem tStar_add_one : tStar + 1 = 102 := rfl

/-- The low-count threshold is positive. -/
theorem tStar_pos : 0 < tStar := by
  rw [tStar_def]; decide

end CollatzPosDens
