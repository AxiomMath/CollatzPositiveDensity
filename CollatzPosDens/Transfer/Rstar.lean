/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Tactic.NormNum

/-!
# The number of schedule updates

We define the natural-number constant `r_* = 580`, the number of updates applied to a schedule
of times starting at `p_init = 1024`.

## Main definitions

* `CollatzPosDens.rStar`: the natural number `r_* = 580`.

## Main results

* `CollatzPosDens.rStar_def`: `r_* = 580`.
* `CollatzPosDens.rStar_pos`: `0 < r_*`.
* `CollatzPosDens.rStar_sub_one`: `r_* - 1 = 579`.

## Implementation notes

The constant is a small closed numeral, so it is an ordinary definition that `rfl` and
`decide` can unfold; facts about it follow from `rStar_def` by `norm_num` or `omega`.

## References

* [Mazur, §3.6]
-/

@[expose] public section

namespace CollatzPosDens

/-- The number of schedule updates `r_* = 580`. -/
@[collatz_pos_dens "def_Rstar"]
def rStar : ℕ := 580

/-- The constant `r_*` equals `580`. -/
theorem rStar_def : rStar = 580 := rfl

/-- The constant `r_*` is positive. -/
theorem rStar_pos : 0 < rStar := by
  rw [rStar_def]; norm_num

/-- In natural-number subtraction, `r_* - 1 = 579`. -/
theorem rStar_sub_one : rStar - 1 = 579 := by
  rw [rStar_def]

end CollatzPosDens
