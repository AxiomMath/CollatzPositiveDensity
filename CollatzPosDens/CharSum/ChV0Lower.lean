/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChV0
public import CollatzPosDens.CharSum.ChPiLower

/-!
# The rational angle `v∘` lies below the colour angle

The rational point `v∘ = (6283 / 2000) · ε_* = 232703471 / 2000000000` satisfies
`0 < v∘ < π ε_*`: it is positive, and since `6283 / 2000 < π` and `ε_* > 0`, multiplying
by `ε_*` gives `v∘ < π ε_*`.

## Main results

* `CollatzPosDens.chV0_pos_lt`: `0 < v∘ ∧ v∘ < π ε_*`, with `v∘` and `ε_*` cast to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `0 < v∘ < π ε_*`. -/
@[collatz_pos_dens "lem_ch_v0_lower"]
theorem chV0_pos_lt : 0 < (chV0 : ℝ) ∧ (chV0 : ℝ) < Real.pi * (epsStar : ℝ) := by
  refine ⟨by exact_mod_cast chV0_pos, ?_⟩
  have heps : (0 : ℝ) < epsStar := by exact_mod_cast epsStar_pos
  rw [chV0_eq_mul]
  push_cast
  exact mul_lt_mul_of_pos_right pi_gt_6283_div_2000 heps

end CollatzPosDens
