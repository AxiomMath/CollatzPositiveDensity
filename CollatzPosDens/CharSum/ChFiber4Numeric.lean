/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChU0
public import Mathlib.Basic.Real.Basic

/-!
# The numerical inequality for the closing letter `4`

With `u∘` the rational lower bound for `sin²` on `[v∘, π / 2]` and `z = 133 / 3125`,
`9 - 4 min(14u∘ - 28u∘² + 16u∘³, 7 / 16) < 9 (1 - 2z + 2z² - (4/3) z³)`.
Indeed `18362 / 100000 < 14u∘ - 28u∘² + 16u∘³ < 7 / 16`, so the minimum is the cubic and the
left side is below `103319 / 12500`, while the right side equals
`252246071481 / 30517578125`.

## Main results

* `CollatzPosDens.ch_fiber4_numeric`: the inequality, over `ℚ`.
* `CollatzPosDens.ch_fiber4_numeric_real`: the same inequality with `u∘` cast to `ℝ`.

## Implementation notes

Both sides are closed rational expressions, so the inequality is decided by exact rational
arithmetic after substituting the value of `u∘`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The numerical inequality behind the cancellation at a white closing letter `4`. -/
@[collatz_pos_dens "lem_ch_fiber4_numeric"]
theorem ch_fiber4_numeric :
    9 - 4 * min (14 * chU0 - 28 * chU0 ^ 2 + 16 * chU0 ^ 3) (7 / 16) <
      9 * (1 - 2 * (133 / 3125) + 2 * (133 / 3125) ^ 2 - 4 / 3 * (133 / 3125) ^ 3) := by
  rw [chU0_eq]
  norm_num

/-- `ch_fiber4_numeric` with `u∘` cast to `ℝ`. -/
theorem ch_fiber4_numeric_real :
    (9 : ℝ) - 4 * min (14 * (chU0 : ℝ) - 28 * (chU0 : ℝ) ^ 2 + 16 * (chU0 : ℝ) ^ 3) (7 / 16) <
      9 * (1 - 2 * (133 / 3125) + 2 * (133 / 3125) ^ 2 - 4 / 3 * (133 / 3125) ^ 3) := by
  rw [chU0_eq]
  norm_num

end CollatzPosDens
