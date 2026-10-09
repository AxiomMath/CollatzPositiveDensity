/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldMass

/-!
# Summability of the holding-time average of the renewal function

For every point `p`, the series `∑_{h ∈ 𝒫} η(h) Q(p + h)` converges. Its terms are nonnegative
and bounded by `η(h)`, since `0 ≤ Q ≤ 1` and `η ≥ 0`, and `∑_{h ∈ 𝒫} η(h) = 1`; comparison of
nonnegative series concludes.

## Main results

* `CollatzPosDens.summable_holdLaw_mul_chQ_add`: `h ↦ η(h) Q(p + h)` is summable on `𝒫`.

## Implementation notes

The statement is given for every `p : ℤ × ℤ`, not only for `p ∈ 𝒫`, since the proof does not
use membership. A point `h = (j, l) ∈ 𝒫` has `j ≥ 1`, and `η(h)` is evaluated as
`holdLaw j.toNat l`, matching the total-mass statement `hasSum_holdLaw_bkPoints`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §8.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Summability of the holding-time average.** For every point `p`, the series
`∑_{h ∈ 𝒫} η(h) Q(p + h)` converges. -/
@[collatz_pos_dens "lem_mo_hold_average_summable"]
theorem summable_holdLaw_mul_chQ_add (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    Summable fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h) :=
  hasSum_holdLaw_bkPoints.summable.of_nonneg_of_le
    (fun _ ↦ mul_nonneg (holdLaw_nonneg _ _) (chQ_range n ξ ε _).1)
    (fun _ ↦ mul_le_of_le_one_right (holdLaw_nonneg _ _) (chQ_range n ξ ε _).2)

end CollatzPosDens
