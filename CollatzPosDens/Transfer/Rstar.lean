/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex

/-!
# The number of schedule intervals

For each Fourier parameter index `ι ∈ {o, b}`, the constant `r_*(ι)` is the number of intervals
in a schedule of times `p_0 < p_1 < ⋯ < p_{r_*(ι)}`, so that `r_*(ι) + 1` trace times are used.
Its values are `r_*(o) = 10` and `r_*(b) = 3`.

## Main definitions

* `CollatzPosDens.rStar`: the natural number `r_*(ι)`.

## Main results

* `CollatzPosDens.rStar_o`, `CollatzPosDens.rStar_b`: `r_*(o) = 10` and `r_*(b) = 3`.
* `CollatzPosDens.rStar_pos`: `0 < r_*(ι)`.

## Implementation notes

The constant is a closed numeral at each index, so it is defined by cases on `ι`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The number of schedule intervals `r_*(ι)`, equal to `10` for `ι = o` and `3` for `ι = b`;
`r_*(ι) + 1` is the number of trace times used. -/
@[collatz_pos_dens "def_Rstar"]
def rStar : FIndex → ℕ
  | .o => 10
  | .b => 3

/-- The constant `r_*(o)` equals `10`. -/
@[simp] theorem rStar_o : rStar .o = 10 := rfl

/-- The constant `r_*(b)` equals `3`. -/
@[simp] theorem rStar_b : rStar .b = 3 := rfl

/-- The constant `r_*(ι)` is positive. -/
theorem rStar_pos (ι : FIndex) : 0 < rStar ι := by
  cases ι <;> decide

/-- The constant `r_*(ι)` is at least `1`. -/
theorem one_le_rStar (ι : FIndex) : 1 ≤ rStar ι := rStar_pos ι

/-- In natural-number subtraction, `r_*(o) - 1 = 9`. -/
theorem rStar_o_sub_one : rStar .o - 1 = 9 := rfl

/-- In natural-number subtraction, `r_*(b) - 1 = 2`. -/
theorem rStar_b_sub_one : rStar .b - 1 = 2 := rfl

end CollatzPosDens
