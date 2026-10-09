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
public import CollatzPosDens.Transfer.Log3Bounds

/-!
# Two-sided bounds for the shift radius `r_b`

For `b ≥ 9` the shift radius `r_b = 2 w_b - B(w_b) - 2 e_b` satisfies `0 ≤ r_b ≤ (3/10) b`.

For the upper bound, `B(w_b) ≥ w_b log₂ 3` and `e_b ≥ 0` give `r_b ≤ (2 - log₂ 3) w_b`;
with `2 - log₂ 3 ≤ 21/50` and `w_b ≤ 3b/5` this is `r_b ≤ (63/250) b ≤ (3/10) b`. This
holds for every `b`.

For the lower bound, `r_b ≥ (229/1000) b - 4 > 0` once `b ≥ 256`. For `9 ≤ b ≤ 255`,
`r_b ≥ 0` is equivalent to `2 e_b ≤ 2 w_b` together with `3^{w_b} ≤ 2^{2 w_b - 2 e_b}`
(since `B(j) ≤ n ↔ 3^j ≤ 2^n`), which is checked for each of these finitely many `b`.

## Main results

* `CollatzPosDens.rb_le`: `r_b ≤ (3/10) b` for every `b : ℕ`.
* `CollatzPosDens.rb_nonneg`: `0 ≤ r_b` for `b ≥ 9`.
* `CollatzPosDens.rb_bounds`: `0 ≤ r_b ∧ r_b ≤ (3/10) b` for `b ≥ 9`.

## Implementation notes

The finite range `9 ≤ b ≤ 255` is settled by kernel evaluation of the natural-number
inequalities above; `e_b` is computable, and the rounded logarithm `B(w_b)` is eliminated
through `ceilLog3_le_iff` rather than evaluated.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The upper bound `r_b ≤ (3/10) b`, valid for every natural number `b`. -/
theorem rb_le (b : ℕ) : (rb b : ℝ) ≤ (3 / 10 : ℝ) * b := by
  have hB : (wb b : ℝ) * Real.logb 2 3 ≤ ceilLog3 (wb b) := mul_logb_le_ceilLog3 _
  have hw : (5 * wb b : ℝ) ≤ 3 * b := by exact_mod_cast five_mul_wb_le b
  rw [rb_def]
  push_cast
  nlinarith [logb_two_three_bounds.1, (Nat.cast_nonneg (wb b) : (0 : ℝ) ≤ wb b),
    (Nat.cast_nonneg (eb b) : (0 : ℝ) ≤ eb b)]

/-- The finite check behind `r_b ≥ 0` for `9 ≤ b ≤ 255`. -/
private theorem rb_nonneg_of_lt_256 :
    ∀ b < 256, 9 ≤ b → 2 * eb b ≤ 2 * wb b ∧ 3 ^ wb b ≤ 2 ^ (2 * wb b - 2 * eb b) := by
  decide +kernel

/-- `r_b ≥ 0` for every `b ≥ 9`. -/
theorem rb_nonneg {b : ℕ} (hb : 9 ≤ b) : 0 ≤ rb b := by
  rcases lt_or_ge b 256 with h | h
  · obtain ⟨h₁, h₂⟩ := rb_nonneg_of_lt_256 b h hb
    have hB := ceilLog3_le_iff.2 h₂
    rw [rb_def]
    omega
  · have hb' : (256 : ℝ) ≤ b := by exact_mod_cast h
    exact_mod_cast (by linarith [rb_lower h] : (0 : ℝ) ≤ rb b)

/-- For `b ≥ 9`, the shift radius satisfies `0 ≤ r_b ≤ (3/10) b`. -/
@[collatz_pos_dens "lem_rb_bounds"]
theorem rb_bounds {b : ℕ} (hb : 9 ≤ b) : 0 ≤ rb b ∧ (rb b : ℝ) ≤ (3 / 10 : ℝ) * b :=
  ⟨rb_nonneg hb, rb_le b⟩

end CollatzPosDens
