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
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.Transfer.Log3Bounds

/-!
# A linear lower bound for the shift radius `r_b`

The shift radius `rb b = 2 * wb b - ceilLog3 (wb b) - 2 * eb b` satisfies
`rb b ≥ (229/1000) b - 4` for `b ≥ 256`. Indeed `ceilLog3 w < w log₂ 3 + 1`, so
`rb b > (2 - log₂ 3) wb b - 1 - 2 eb b`; with `2 - log₂ 3 ≥ 83/200`, `wb b ≥ 3b/5 - 1` and, for
`b ≥ 256`, `eb b = ⌈b/100⌉ ≤ b/100 + 1`, this gives `rb b > (229/1000) b - 683/200`.

## Main results

* `CollatzPosDens.rb_lower`: `(229/1000) b - 4 ≤ rb b` for every `b ≥ 256`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `b ≥ 256`, the shift radius satisfies `(229/1000) b - 4 ≤ rb b`. -/
@[collatz_pos_dens "lem_rb_lower"]
theorem rb_lower {b : ℕ} (hb : 256 ≤ b) : (229 / 1000 : ℝ) * b - 4 ≤ rb b := by
  have hB := ceilLog3_lt_mul_logb_add_one (wb b)
  have hw : (3 * b : ℝ) < 5 * ((wb b : ℝ) + 1) := by exact_mod_cast lt_five_mul_wb_add_one b
  have he : (100 * eb b : ℝ) ≤ b + 99 := by
    rw [eb_of_le hb]; exact_mod_cast (by omega : 100 * ((b + 99) / 100) ≤ b + 99)
  have hlog := (logb_two_three_bounds).2
  have hr : (rb b : ℝ) = 2 * (wb b : ℝ) - ceilLog3 (wb b) - 2 * eb b := by
    rw [rb_def]; push_cast; ring
  rw [hr]
  nlinarith [(Nat.cast_nonneg (wb b) : (0 : ℝ) ≤ wb b)]

end CollatzPosDens
