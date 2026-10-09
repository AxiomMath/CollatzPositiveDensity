/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.Order.Group.Indicator
public import CollatzPosDens.Attr
public import CollatzPosDens.Monotone.MoDiscountedSummable

/-!
# A discounted weighted expectation bound

Let `μ, F, g : X → ℝ` be nonnegative, `V ⊆ X`, and let `C, c, d` be reals with `C ≥ 0`, `c ≥ 0`
and `exp (-d) ≤ 1 - c`. Suppose `∑ x, μ x * exp (g x)` converges, `F x ≤ C * exp (g x)` wherever
`μ x ≠ 0`, and `F x ≤ C * exp (-d) * exp (g x)` for `x ∈ V` with `μ x ≠ 0`. Then
`∑ x, μ x * F x ≤ C * (∑ x, μ x * exp (g x) - c * ∑ x ∈ V, μ x)`.

The proof is pointwise: `μ x * F x + C * c * 1_V(x) * μ x ≤ C * μ x * exp (g x)` for every `x`,
using `c ≤ c * exp (g x)` on `V`; then one sums the three convergent series.

## Main results

* `CollatzPosDens.tsum_mul_le_of_le_exp_discount`: the discounted expectation bound.

## Implementation notes

The index type `X` is arbitrary; no countability hypothesis is needed. The sum over `V` is the
unconditional sum over the subtype `↥V`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- If `∑ x, μ x * exp (g x)` converges, `μ, F, g ≥ 0`,
`F x ≤ C * exp (g x)` wherever `μ x ≠ 0`, and `F x ≤ C * exp (-d) * exp (g x)` on `V` wherever
`μ x ≠ 0`, with `C, c ≥ 0` and `exp (-d) ≤ 1 - c`, then
`∑ x, μ x * F x ≤ C * (∑ x, μ x * exp (g x) - c * ∑ x ∈ V, μ x)`. -/
@[collatz_pos_dens "lem_mo_discounted_expectation"]
theorem tsum_mul_le_of_le_exp_discount {X : Type*} {μ F g : X → ℝ} {V : Set X}
    {C c d : ℝ} (hμ : ∀ x, 0 ≤ μ x) (hF : ∀ x, 0 ≤ F x) (hg : ∀ x, 0 ≤ g x)
    (hC : 0 ≤ C) (hc : 0 ≤ c) (hd : exp (-d) ≤ 1 - c)
    (hsum : Summable fun x => μ x * exp (g x))
    (hle : ∀ x, μ x ≠ 0 → F x ≤ C * exp (g x))
    (hleV : ∀ x ∈ V, μ x ≠ 0 → F x ≤ C * exp (-d) * exp (g x)) :
    ∑' x, μ x * F x ≤ C * (∑' x, μ x * exp (g x) - c * ∑' x : V, μ x) := by
  have hμF : Summable fun x => μ x * F x := summable_mul_of_le_exp hμ hF hsum hle
  have hμle : ∀ x, μ x ≤ μ x * exp (g x) := fun x =>
    le_mul_of_one_le_right (hμ x) (one_le_exp (hg x))
  have hind : Summable (V.indicator μ) :=
    hsum.of_nonneg_of_le (fun x => Set.indicator_nonneg (fun x _ => hμ x) x) fun x =>
      (Set.indicator_le_self' (fun x _ => hμ x) x).trans (hμle x)
  have key : ∀ x, μ x * F x + C * c * V.indicator μ x ≤ C * (μ x * exp (g x)) := by
    intro x
    by_cases h0 : μ x = 0
    · by_cases hx : x ∈ V <;> simp [hx, h0]
    by_cases hx : x ∈ V
    · rw [Set.indicator_of_mem hx]
      have h1 : μ x * F x ≤ μ x * (C * (1 - c) * exp (g x)) := by
        refine mul_le_mul_of_nonneg_left ((hleV x hx h0).trans ?_) (hμ x)
        gcongr
      have h2 : C * c * μ x ≤ C * c * (μ x * exp (g x)) :=
        mul_le_mul_of_nonneg_left (hμle x) (mul_nonneg hC hc)
      nlinarith
    · rw [Set.indicator_of_notMem hx, mul_zero, add_zero]
      calc μ x * F x ≤ μ x * (C * exp (g x)) := mul_le_mul_of_nonneg_left (hle x h0) (hμ x)
        _ = C * (μ x * exp (g x)) := by ring
  have hsumle := (hμF.add (hind.mul_left (C * c))).tsum_le_tsum key (hsum.mul_left C)
  rw [hμF.tsum_add (hind.mul_left (C * c)), tsum_mul_left, tsum_mul_left] at hsumle
  rw [tsum_subtype]
  nlinarith

end CollatzPosDens
