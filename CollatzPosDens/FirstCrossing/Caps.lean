/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Monotone.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import CollatzPosDens.Attr

/-!
# The overshoot caps `K_j`

For a natural number `j`, the overshoot cap at scale `j` is
$$K_j = 29 + \lfloor j / 56 \rfloor.$$
It is a slowly growing sequence of natural numbers that starts at `K_0 = 29` and increases by
one every fifty-six scales. Since `⌊j/56⌋ ≥ (j - 55)/56`, it satisfies the lower bound
`29 + j/56 ≤ K_j + 1`.

## Main definitions

* `CollatzPosDens.cap`: the cap `K_j`.

## Main results

* `CollatzPosDens.twentyNine_le_cap`: every cap is at least `29`.
* `CollatzPosDens.cap_pos`: every cap is positive.
* `CollatzPosDens.cap_mono`: the caps are monotone in `j`.
* `CollatzPosDens.cap_add_fiftySix`: `K_{j+56} = K_j + 1`.
* `CollatzPosDens.add_le_fiftySix_mul_cap_add_one`: `56 * 29 + j ≤ 56 * (K_j + 1)`, i.e.
  `29 + j / 56 ≤ K_j + 1` in rational arithmetic.

## Implementation notes

The floor of a quotient of natural numbers is natural-number division. The lower bound is stated
with the denominator cleared, as an inequality of natural numbers.

## References

* [Mazur, *Collatz positive density*], §14.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The overshoot cap at scale `j`: `K_j = 29 + ⌊j / 56⌋`. -/
@[collatz_pos_dens "def_caps"]
def cap (j : ℕ) : ℕ := 29 + j / 56

/-- Every cap is at least `29`. -/
theorem twentyNine_le_cap (j : ℕ) : 29 ≤ cap j := Nat.le_add_right _ _

/-- Every cap is positive. -/
theorem cap_pos (j : ℕ) : 0 < cap j := Nat.lt_of_lt_of_le (by decide) (twentyNine_le_cap j)

/-- The caps are monotone in the scale. -/
theorem cap_mono : Monotone cap := fun _ _ h =>
  Nat.add_le_add_left (Nat.div_le_div_right h) _

/-- The cap increases by exactly one every fifty-six scales. -/
theorem cap_add_fiftySix (j : ℕ) : cap (j + 56) = cap j + 1 := by
  unfold cap
  omega

/-- **Lower bound for the caps**, with denominators cleared: `56 * 29 + j ≤ 56 * (K_j + 1)`,
i.e. `29 + j / 56 ≤ K_j + 1` in exact division. -/
@[collatz_pos_dens "lem_fc_cap_lower"]
theorem add_le_fiftySix_mul_cap_add_one (j : ℕ) : 56 * 29 + j ≤ 56 * (cap j + 1) := by
  unfold cap
  omega

end CollatzPosDens
