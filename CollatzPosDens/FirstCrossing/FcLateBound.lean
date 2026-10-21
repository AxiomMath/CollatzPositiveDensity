/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.FcLateWindow
public import CollatzPosDens.FirstCrossing.Scales
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The window deficit bound `d^w_j`

For a scale index `j`, write `b_j = scale j`, `y^w_j = yW j` for the central window and
`K_j = cap j`. The window deficit bound is the real number
$$\mathsf d^{\mathrm w}_j = 2\exp\Bigl(-\frac{2\,(207\,y^{\mathrm w}_j/500)^2}
  {9\,(b_j+y^{\mathrm w}_j)}\Bigr)+2^{-(K_j+1)}.$$

## Main definitions

* `CollatzPosDens.dW`: the window deficit bound `d^w_j`.

## Main results

* `CollatzPosDens.dW_def`: the defining formula.
* `CollatzPosDens.dW_eq`: the same formula with the exponent written `-2 x² / (9 (b + y))` and
  the dyadic term written `2⁻¹ ^ (K_j + 1)`.
* `CollatzPosDens.dW_pos`, `CollatzPosDens.dW_nonneg`: the bound is positive.
* `CollatzPosDens.two_inv_pow_le_dW`, `CollatzPosDens.dW_le_two_add`: elementary bounds.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The **window deficit bound**
`d^w_j = 2 exp(-2 (207 y^w_j / 500)² / (9 (b_j + y^w_j))) + 2^{-(K_j+1)}`. -/
@[collatz_pos_dens "def_fc_late_bound"]
noncomputable def dW (j : ℕ) : ℝ :=
  2 * exp (-(2 * (207 * (yW j : ℝ) / 500) ^ 2) / (9 * ((scale j : ℝ) + yW j))) +
    (2 : ℝ) ^ (-((cap j : ℤ) + 1))

/-- The defining formula of `dW`. -/
theorem dW_def (j : ℕ) : dW j =
    2 * exp (-(2 * (207 * (yW j : ℝ) / 500) ^ 2) / (9 * ((scale j : ℝ) + yW j))) +
      (2 : ℝ) ^ (-((cap j : ℤ) + 1)) := rfl

/-- The dyadic term of `dW` as a natural power of `2⁻¹`. -/
theorem two_zpow_neg_cap_add_one (j : ℕ) :
    (2 : ℝ) ^ (-((cap j : ℤ) + 1)) = 2⁻¹ ^ (cap j + 1) := by
  rw [zpow_neg, inv_pow, ← zpow_natCast]
  push_cast
  rfl

/-- `dW` with the exponent written `-2 x² / (9 (b_j + y))` and the dyadic term
`2⁻¹ ^ (K_j + 1)`, where `y = min (wd b_j) ⌊b_j/8⌋` is the central window as a natural number. -/
theorem dW_eq (j : ℕ) : dW j =
    2 * exp (-2 * (207 * ((min (wd (scale j)) (scale j / 8) : ℕ) : ℝ) / 500) ^ 2 /
      (9 * ((scale j : ℝ) + ((min (wd (scale j)) (scale j / 8) : ℕ) : ℝ)))) +
      2⁻¹ ^ (cap j + 1) := by
  rw [dW_def, two_zpow_neg_cap_add_one, yW_eq_natCast, neg_mul]
  push_cast
  rfl

/-- The window deficit bound is positive. -/
theorem dW_pos (j : ℕ) : 0 < dW j := by
  rw [dW_def]
  positivity

/-- The window deficit bound is nonnegative. -/
theorem dW_nonneg (j : ℕ) : 0 ≤ dW j := (dW_pos j).le

/-- The dyadic term `2^{-(K_j+1)}` is at most `d^w_j`. -/
theorem two_inv_pow_le_dW (j : ℕ) : (2⁻¹ : ℝ) ^ (cap j + 1) ≤ dW j := by
  rw [dW_def, two_zpow_neg_cap_add_one]
  have := exp_pos (-(2 * (207 * (yW j : ℝ) / 500) ^ 2) / (9 * ((scale j : ℝ) + yW j)))
  linarith

/-- The exponential factor of `d^w_j` is at most `1`, so `d^w_j ≤ 2 + 2^{-(K_j+1)}`. -/
theorem dW_le_two_add (j : ℕ) : dW j ≤ 2 + (2⁻¹ : ℝ) ^ (cap j + 1) := by
  rw [dW_def, two_zpow_neg_cap_add_one]
  have hy : (0 : ℝ) ≤ yW j := by exact_mod_cast yW_nonneg j
  have hle : -(2 * (207 * (yW j : ℝ) / 500) ^ 2) / (9 * ((scale j : ℝ) + yW j)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (by positivity)
  have := exp_le_one_iff.mpr hle
  linarith

end CollatzPosDens
