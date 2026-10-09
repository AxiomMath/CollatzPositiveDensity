/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.FirstCrossing.Wb
public import CollatzPosDens.FirstCrossing.Eb

/-!
# The shift radius `r_b`

For a natural number `b` this file defines the shift radius
$$r_b = 2 w_b - \mathsf{B}(w_b) - 2 e_b \in \mathbb{Z},$$
where `w_b = ⌊3b/5⌋`, `B(j) = ⌈j log₂ 3⌉` and `e_b` is the scale increment. Since
`B(w_b) + 2 e_b` may exceed `2 w_b` (for instance `r_0 = -2`), the radius is valued in `ℤ`.

## Main definitions

* `CollatzPosDens.rb`: the shift radius `r_b = 2 w_b - B(w_b) - 2 e_b`.

## Main results

* `CollatzPosDens.rb_def`: the unfolding of `r_b`.
* `CollatzPosDens.rb_add_ceilLog3_add_eb`: `r_b + B(w_b) + 2 e_b = 2 w_b`.
* `CollatzPosDens.rb_zero`: `r_0 = -2`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §15.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The **shift radius** `r_b = 2 w_b - B(w_b) - 2 e_b ∈ ℤ` of a natural number `b`. -/
@[collatz_pos_dens "def_rb"]
noncomputable def rb (b : ℕ) : ℤ :=
  2 * (wb b : ℤ) - ceilLog3 (wb b) - 2 * eb b

/-- `r_b` equals `2 w_b - B(w_b) - 2 e_b`, as an equation in `ℤ`. -/
theorem rb_def (b : ℕ) : rb b = 2 * (wb b : ℤ) - ceilLog3 (wb b) - 2 * eb b := rfl

/-- The defining relation `r_b + B(w_b) + 2 e_b = 2 w_b`. -/
theorem rb_add_ceilLog3_add_eb (b : ℕ) :
    rb b + ceilLog3 (wb b) + 2 * eb b = 2 * (wb b : ℤ) := by
  rw [rb_def]; ring

/-- `r_0 = -2`. -/
@[simp]
theorem rb_zero : rb 0 = -2 := by
  simp [rb_def, wb_def, ceilLog3, eb_of_le_twelve]

end CollatzPosDens
