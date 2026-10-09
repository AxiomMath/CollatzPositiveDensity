/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CollatzPosDens.Attr

/-!
# The logarithm is bounded by the square root

This file proves the scalar inequality $\log x \le \sqrt x$ for every real $x \ge 0$.

## Main results

* `CollatzPosDens.log_le_sqrt`: for `0 ≤ x`, `Real.log x ≤ Real.sqrt x`.

## Implementation notes

The source states the bound for `x > 0`; it also holds at `x = 0`, where both sides vanish
under Mathlib's conventions `Real.log 0 = 0` and `Real.sqrt 0 = 0`, so the hypothesis is
weakened to `0 ≤ x`.

## References

* [Mazur, *Collatz positive density*, §8.1]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every real `x ≥ 0`, `log x ≤ √x`. -/
@[collatz_pos_dens "lem_mo_log_sqrt"]
theorem log_le_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ Real.sqrt x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have h1 := Real.log_le_sub_one_of_pos (half_pos hs)
  have h2 := Real.log_le_sub_one_of_pos (two_pos (α := ℝ))
  rw [Real.log_div hs.ne' two_ne_zero] at h1
  have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]; ring
  linarith

end CollatzPosDens
