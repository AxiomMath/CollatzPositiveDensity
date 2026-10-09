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

The rational point `v∘ = 6283 / 54250` satisfies `0 < v∘ < 8π / 217`. Indeed
`v∘ = (6283 / 2000) · (8 / 217)` because `2000 · 217 = 434000 = 8 · 54250`, and
`6283 / 2000 < π`.

## Main results

* `CollatzPosDens.chV0_pos_lt`: `0 < v∘ ∧ v∘ < 8π / 217`, with `v∘` cast to `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- `0 < v∘ < 8π / 217`. -/
@[collatz_pos_dens "lem_ch_v0_lower"]
theorem chV0_pos_lt : 0 < (chV0 : ℝ) ∧ (chV0 : ℝ) < 8 * Real.pi / 217 := by
  have h := pi_gt_6283_div_2000
  refine ⟨by exact_mod_cast chV0_pos, ?_⟩
  rw [chV0_def]
  push_cast
  linarith

end CollatzPosDens
