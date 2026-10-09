/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.Terminal.LowerScale

/-!
# The upper scale `U_b(R)`

For a natural number `b` and a real number `R` this file defines the upper scale
$$U_b(R) = 2^{2 r_b} L_b(R),$$
where `r_b ∈ ℤ` is the shift radius `CollatzPosDens.rb` and `L_b(R)` is the lower
external scale `CollatzPosDens.lowerScale`. Since `r_b` is an integer, `2^{2 r_b}` is an
integer power.

## Main definitions

* `CollatzPosDens.upperScale`: the upper scale `U_b(R)`.

## Main results

* `CollatzPosDens.upperScale_def`: the unfolding of `U_b(R)`.
* `CollatzPosDens.upperScale_eq`: `U_b(R) = 4^b R 2^{r_b} / (4 · 3^b)`.
* `CollatzPosDens.upperScale_eq_mul`: `U_b(R) = U_b(1) · R`.
* `CollatzPosDens.upperScale_pos`: `0 < U_b(R)` when `0 < R`.
* `CollatzPosDens.upperScale_mono`: `U_b` is monotone in `R`.

## Implementation notes

The scale is of interest for `b ≥ 1` and `R > 0`. The formula makes sense for all `b : ℕ` and
`R : ℝ`, so the definition is total and these conditions appear as hypotheses on the lemmas
that need them.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The **upper scale** `U_b(R) = 2^{2 r_b} L_b(R)`. -/
@[collatz_pos_dens "def_upper_scale"]
noncomputable def upperScale (b : ℕ) (R : ℝ) : ℝ :=
  (2 : ℝ) ^ (2 * rb b) * lowerScale b R

/-- Unfolding lemma for `upperScale`. -/
theorem upperScale_def (b : ℕ) (R : ℝ) :
    upperScale b R = (2 : ℝ) ^ (2 * rb b) * lowerScale b R := rfl

/-- Closed form of the upper scale: `U_b(R) = 4^b R 2^{r_b} / (4 · 3^b)`. -/
theorem upperScale_eq (b : ℕ) (R : ℝ) :
    upperScale b R = 4 ^ b * R * (2 : ℝ) ^ rb b / (4 * 3 ^ b) := by
  have h2 : (2 : ℝ) ^ rb b ≠ 0 := zpow_ne_zero _ two_ne_zero
  rw [upperScale_def, lowerScale_def, zpow_mul']
  simp only [zpow_two]
  field_simp

/-- `U_b(R) = U_b(1) · R`. -/
theorem upperScale_eq_mul (b : ℕ) (R : ℝ) : upperScale b R = upperScale b 1 * R := by
  rw [upperScale_def, upperScale_def, lowerScale_eq_mul b R]; ring

/-- The upper scale is positive for a positive argument. -/
theorem upperScale_pos (b : ℕ) {R : ℝ} (hR : 0 < R) : 0 < upperScale b R := by
  rw [upperScale_def]
  have := lowerScale_pos b hR
  positivity

/-- The upper scale is monotone in `R`. -/
theorem upperScale_mono (b : ℕ) : Monotone (upperScale b) := fun _ _ h => by
  rw [upperScale_def, upperScale_def]
  gcongr
  exact lowerScale_mono b h

end CollatzPosDens
