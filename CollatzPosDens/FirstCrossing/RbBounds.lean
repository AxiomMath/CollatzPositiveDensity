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
public import CollatzPosDens.FirstCrossing.RbLower

/-!
# Two-sided bounds for the shift radius `r_b`

For `b ≥ 256` the shift radius `r_b = 2 w_b - B(w_b) - 2 e_b` satisfies `0 ≤ r_b ≤ (23/100) b`.

For the upper bound, the exact comparison `3^12 = 531441 > 524288 = 2^19` gives
`log₂ 3 > 19/12`, so `B(w_b) ≥ w_b log₂ 3 ≥ (19/12) w_b`. Together with `e_b = ⌈b/100⌉ ≥ b/100`
and `w_b ≤ 3b/5` this gives `r_b ≤ (5/12) w_b - b/50 ≤ (23/100) b`. This holds for every `b`.

For the lower bound, `r_b ≥ (229/1000) b - 4 ≥ (229/1000) · 256 - 4 > 0` once `b ≥ 256`.

## Main results

* `CollatzPosDens.nineteen_div_twelve_lt_logb_two_three`: `19/12 < log₂ 3`.
* `CollatzPosDens.rb_le`: `r_b ≤ (23/100) b` for every `b : ℕ`.
* `CollatzPosDens.rb_nonneg`: `0 ≤ r_b` for `b ≥ 256`.
* `CollatzPosDens.rb_bounds`: `0 ≤ r_b ∧ r_b ≤ (23/100) b` for `b ≥ 256`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `19/12 < log₂ 3`, from the exact comparison `2 ^ 19 < 3 ^ 12`. -/
theorem nineteen_div_twelve_lt_logb_two_three : (19 / 12 : ℝ) < Real.logb 2 3 := by
  have h : ¬ ((12 : ℕ) : ℝ) * Real.logb 2 3 ≤ (19 : ℕ) := by
    rw [mul_logb_two_three_le_iff]; norm_num
  push_cast at h
  linarith

/-- The upper bound `r_b ≤ (23/100) b`, valid for every natural number `b`. -/
theorem rb_le (b : ℕ) : (rb b : ℝ) ≤ (23 / 100 : ℝ) * b := by
  have hB : (wb b : ℝ) * Real.logb 2 3 ≤ ceilLog3 (wb b) := mul_logb_le_ceilLog3 _
  have hw : (5 * wb b : ℝ) ≤ 3 * b := by exact_mod_cast five_mul_wb_le b
  have he : (b : ℝ) ≤ 100 * eb b := by
    exact_mod_cast (by rw [eb_eq]; omega : b ≤ 100 * eb b)
  rw [rb_def]
  push_cast
  nlinarith [nineteen_div_twelve_lt_logb_two_three, (Nat.cast_nonneg (wb b) : (0 : ℝ) ≤ wb b)]

/-- `r_b ≥ 0` for every `b ≥ 256`, from `r_b ≥ (229/1000) b - 4`. -/
theorem rb_nonneg {b : ℕ} (hb : 256 ≤ b) : 0 ≤ rb b := by
  have hb' : (256 : ℝ) ≤ b := by exact_mod_cast hb
  exact_mod_cast (by linarith [rb_lower hb] : (0 : ℝ) ≤ rb b)

/-- For `b ≥ 256`, the shift radius satisfies `0 ≤ r_b ≤ (23/100) b`. -/
@[collatz_pos_dens "lem_rb_bounds"]
theorem rb_bounds {b : ℕ} (hb : 256 ≤ b) : 0 ≤ rb b ∧ (rb b : ℝ) ≤ (23 / 100 : ℝ) * b :=
  ⟨rb_nonneg hb, rb_le b⟩

end CollatzPosDens
