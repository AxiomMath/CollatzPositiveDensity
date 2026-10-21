/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex

/-!
# The initial schedule time `p_init(ι)`

For each index `ι : CollatzPosDens.FIndex`, the initial schedule time `p_init(ι)` is the natural
number with `p_init(o) = 193` and `p_init(b) = 169`. The schedule times are the iterates
`p_i = 𝔤_ι^i(p_init(ι))` of the map `𝔤_ι = CollatzPosDens.recipeMap ι`, and the first window
starts at `y_0 = p_init(ι) + 1`.

## Main definitions

* `CollatzPosDens.pInit`: the natural number `p_init(ι)`.

## Main results

* `CollatzPosDens.pInit_o`, `CollatzPosDens.pInit_b`: `p_init(o) = 193` and `p_init(b) = 169`.
* `CollatzPosDens.pInit_o_add_one`, `CollatzPosDens.pInit_b_add_one`: `p_init(o) + 1 = 194` and
  `p_init(b) + 1 = 170`.
* `CollatzPosDens.pInit_pos`: `0 < p_init(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The initial schedule time `p_init(ι)`, equal to `193` for `ι = o` and `169` for `ι = b`. -/
@[collatz_pos_dens "def_s02_pinit"]
def pInit : FIndex → ℕ
  | .o => 193
  | .b => 169

/-- The initial schedule time at the original index equals `193`. -/
@[simp] theorem pInit_o : pInit .o = 193 := rfl

/-- The initial schedule time at the bootstrap index equals `169`. -/
@[simp] theorem pInit_b : pInit .b = 169 := rfl

/-- The successor of the initial schedule time at the original index is `194`. -/
theorem pInit_o_add_one : pInit .o + 1 = 194 := rfl

/-- The successor of the initial schedule time at the bootstrap index is `170`. -/
theorem pInit_b_add_one : pInit .b + 1 = 170 := rfl

/-- The initial schedule time is positive. -/
theorem pInit_pos (ι : FIndex) : 0 < pInit ι := by
  cases ι <;> decide

end CollatzPosDens
