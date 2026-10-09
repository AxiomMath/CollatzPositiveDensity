/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import CollatzPosDens.Attr

/-!
# Summability of discounted weighted sums

Let `μ, F : X → ℝ` be nonnegative, `g : X → ℝ`, and `C : ℝ`. If the series
`∑ x, μ x * exp (g x)` converges and `F x ≤ C * exp (g x)` whenever `μ x ≠ 0`, then the series
`∑ x, μ x * F x` converges. This is a comparison of nonnegative series:
`0 ≤ μ x * F x ≤ C * (μ x * exp (g x))` for every `x`.

## Main results

* `CollatzPosDens.summable_mul_of_le_exp`: the series `∑ x, μ x * F x` is summable.

## Implementation notes

The statement is commonly given for a countable `X` with `g ≥ 0` and `C ≥ 0`; none of these is
needed, and the result holds for an arbitrary index type, real-valued `g` and real `C`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- If `∑ x, μ x * exp (g x)` converges, `μ, F ≥ 0`, and `F x ≤ C * exp (g x)` wherever
`μ x ≠ 0`, then `∑ x, μ x * F x` converges. -/
@[collatz_pos_dens "lem_mo_discounted_summable"]
theorem summable_mul_of_le_exp {X : Type*} {μ F g : X → ℝ} {C : ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x)
    (hsum : Summable fun x => μ x * exp (g x))
    (hle : ∀ x, μ x ≠ 0 → F x ≤ C * exp (g x)) :
    Summable fun x => μ x * F x := by
  refine (hsum.mul_left C).of_nonneg_of_le (fun x => mul_nonneg (hμ x) (hF x)) fun x => ?_
  by_cases h : μ x = 0
  · simp [h]
  · calc μ x * F x ≤ μ x * (C * exp (g x)) := mul_le_mul_of_nonneg_left (hle x h) (hμ x)
      _ = C * (μ x * exp (g x)) := by ring

end CollatzPosDens
