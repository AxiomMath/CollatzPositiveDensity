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
public import CollatzPosDens.Transfer.S03Log3Bounds

/-!
# A linear lower bound for the shift radius `r_b`

The shift radius `r_b = 2 w_b - B(w_b) - 2 e_b` satisfies `r_b ≥ (229/1000) b - 4` for
`b ≥ 256`. Indeed `B(w_b) < w_b log₂ 3 + 1`, so `r_b > (2 - log₂ 3) w_b - 1 - 2 e_b`; with
`2 - log₂ 3 ≥ 83/200`, `w_b ≥ 3b/5 - 1` and `e_b = ⌈b/100⌉ ≤ b/100 + 1`, this gives
`r_b > (229/1000) b - 683/200`.

## Main results

* `CollatzPosDens.mul_sub_four_le_rb`: `(229/1000) b - 4 ≤ r_b` for every `b : ℕ`.
* `CollatzPosDens.rb_lower`: `(229/1000) b - 4 ≤ r_b` for every `b ≥ 256`.

## Implementation notes

Since `e_b = ⌈b/100⌉ ≤ b/100 + 1` holds for every `b`, the argument needs no lower bound on
`b`; the general form is `mul_sub_four_le_rb`, and `rb_lower` is the statement for `b ≥ 256`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `b : ℕ`, the shift radius satisfies `r_b ≥ (229/1000) b - 4`. -/
theorem mul_sub_four_le_rb (b : ℕ) : (229 / 1000 : ℝ) * b - 4 ≤ rb b := by
  have hB := ceilLog3_lt_mul_logb_add_one (wb b)
  have hw : (3 * b : ℝ) < 5 * ((wb b : ℝ) + 1) := by exact_mod_cast lt_five_mul_wb_add_one b
  have he : (100 * eb b : ℝ) ≤ b + 99 := by
    rw [eb_eq]; exact_mod_cast (by omega : 100 * ((b + 99) / 100) ≤ b + 99)
  have hlog := (logb_two_three_bounds).2
  have hr : (rb b : ℝ) = 2 * (wb b : ℝ) - ceilLog3 (wb b) - 2 * eb b := by
    rw [rb_def]; push_cast; ring
  rw [hr]
  nlinarith [(Nat.cast_nonneg (wb b) : (0 : ℝ) ≤ wb b)]

/-- For `b ≥ 256`, the shift radius satisfies `r_b ≥ (229/1000) b - 4`. -/
@[collatz_pos_dens "lem_rb_lower"]
theorem rb_lower {b : ℕ} (_hb : 256 ≤ b) : (229 / 1000 : ℝ) * b - 4 ≤ rb b :=
  mul_sub_four_le_rb b

end CollatzPosDens
