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
$$K_j = 16 + \lfloor j / 32 \rfloor,$$
a slowly growing sequence of natural numbers that starts at `16` and increases by one every
thirty-two scales.

## Main definitions

* `CollatzPosDens.cap`: the cap `K_j = 16 + j / 32`.

## Main results

* `CollatzPosDens.cap_def`: the defining formula.
* `CollatzPosDens.sixteen_le_cap`: every cap is at least `16`.
* `CollatzPosDens.cap_pos`: every cap is positive.
* `CollatzPosDens.cap_mono`: the caps are monotone in `j`.
* `CollatzPosDens.cap_of_lt`: `K_j = 16` for `j < 32`.
* `CollatzPosDens.cap_zero`: `K_0 = 16`.
* `CollatzPosDens.cap_add_thirtyTwo`: `K_{j+32} = K_j + 1`.
* `CollatzPosDens.add_le_thirtyTwo_mul_cap_add_one`: `32 * 16 + j ≤ 32 * (K_j + 1)`, i.e.
  `16 + j / 32 ≤ K_j + 1` in rational arithmetic.

## Implementation notes

The floor `⌊j/32⌋` of a natural number is natural-number division `j / 32`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The overshoot cap at scale `j`: `K_j = 16 + ⌊j / 32⌋`. -/
@[collatz_pos_dens "def_caps"]
def cap (j : ℕ) : ℕ := 16 + j / 32

/-- The defining formula of the cap `K_j`. -/
theorem cap_def (j : ℕ) : cap j = 16 + j / 32 := rfl

/-- Every cap is at least `16`. -/
theorem sixteen_le_cap (j : ℕ) : 16 ≤ cap j := Nat.le_add_right _ _

/-- Every cap is positive. -/
theorem cap_pos (j : ℕ) : 0 < cap j := by unfold cap; omega

/-- The caps are monotone in the scale. -/
theorem cap_mono : Monotone cap := fun _ _ h => Nat.add_le_add_left (Nat.div_le_div_right h) _

/-- The cap at scale `j < 32` is `16`. -/
theorem cap_of_lt {j : ℕ} (hj : j < 32) : cap j = 16 := by
  simp [cap, Nat.div_eq_of_lt hj]

/-- The cap at scale `0` is `16`. -/
@[simp] theorem cap_zero : cap 0 = 16 := rfl

/-- The cap increases by exactly one every thirty-two scales. -/
theorem cap_add_thirtyTwo (j : ℕ) : cap (j + 32) = cap j + 1 := by
  simp only [cap, Nat.add_div_right j (by omega : 0 < 32)]
  omega

/-- With denominators cleared, `16 + j / 32 ≤ K_j + 1` in exact division:
`32 * 16 + j ≤ 32 * (K_j + 1)`. -/
theorem add_le_thirtyTwo_mul_cap_add_one (j : ℕ) : 32 * 16 + j ≤ 32 * (cap j + 1) := by
  unfold cap; omega

end CollatzPosDens
