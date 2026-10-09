/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Rb

/-!
# The lower external scale `L_b(R)`

For a natural number `b` and a real number `R` this file defines the lower external scale
$$L_b(R) = \frac{4^b R}{4 \cdot 2^{r_b} \cdot 3^b},$$
where `r_b ∈ ℤ` is the shift radius `CollatzPosDens.rb`, so `2^{r_b}` is an integer power.

## Main definitions

* `CollatzPosDens.lowerScale`: the lower external scale `L_b(R)`.

## Main results

* `CollatzPosDens.lowerScale_def`: the unfolding of `L_b(R)`.
* `CollatzPosDens.lowerScale_pos`: `L_b(R) > 0` when `R > 0`.
* `CollatzPosDens.lowerScale_eq_mul`: `L_b(R) = L_b(1) · R`.
* `CollatzPosDens.lowerScale_mono`: `L_b` is monotone in `R`.

## Implementation notes

The scale is of interest for `b ≥ 1` and `R > 0`. The formula makes sense for all `b : ℕ` and
`R : ℝ`, so the definition is total and these conditions appear as hypotheses on the lemmas
that need them.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The **lower external scale** `L_b(R) = 4^b R / (4 · 2^{r_b} · 3^b)`. -/
@[collatz_pos_dens "def_lower_scale"]
noncomputable def lowerScale (b : ℕ) (R : ℝ) : ℝ :=
  4 ^ b * R / (4 * (2 : ℝ) ^ rb b * 3 ^ b)

/-- Unfolding lemma for `lowerScale`. -/
theorem lowerScale_def (b : ℕ) (R : ℝ) :
    lowerScale b R = 4 ^ b * R / (4 * (2 : ℝ) ^ rb b * 3 ^ b) := rfl

/-- The denominator `4 · 2^{r_b} · 3^b` of the lower scale is positive. -/
theorem lowerScale_denom_pos (b : ℕ) : 0 < 4 * (2 : ℝ) ^ rb b * 3 ^ b := by
  positivity

/-- `L_b(R) = L_b(1) · R`. -/
theorem lowerScale_eq_mul (b : ℕ) (R : ℝ) : lowerScale b R = lowerScale b 1 * R := by
  simp only [lowerScale_def]; ring

/-- The lower scale is positive for a positive argument. -/
theorem lowerScale_pos (b : ℕ) {R : ℝ} (hR : 0 < R) : 0 < lowerScale b R := by
  rw [lowerScale_def]; positivity

/-- The lower scale is monotone in `R`. -/
theorem lowerScale_mono (b : ℕ) : Monotone (lowerScale b) := by
  intro R S h
  rw [lowerScale_def, lowerScale_def]
  have := lowerScale_denom_pos b
  gcongr

end CollatzPosDens
