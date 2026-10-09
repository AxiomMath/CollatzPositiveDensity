/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.FxRefLawTotal

/-!
# The reference law is bounded by one

Each weight of the reference law `μ_n : G_n → [0, ∞]` of `CollatzPosDens.refLaw` is at most
one: `μ_n(y)` is one of the nonnegative terms of the finite sum `∑_{x ∈ G_n} μ_n(x) = 1`.

## Main results

* `CollatzPosDens.refLaw_le_one`: `μ_n(y) ≤ 1`.
* `CollatzPosDens.refLaw_ne_top`: `μ_n(y) ≠ ∞`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.1.
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- Each weight of the reference law is at most one: `μ_n(y) ≤ 1` for `y ∈ G_n`. -/
@[collatz_pos_dens "lem_fx_ref_law_bounded"]
theorem refLaw_le_one (n : ℕ) (y : ResidueGroup n) : refLaw n y ≤ 1 :=
  sum_refLaw n ▸ Finset.single_le_sum_of_canonicallyOrdered (Finset.mem_univ y)

/-- Each weight of the reference law is finite: `μ_n(y) ≠ ∞`. -/
theorem refLaw_ne_top (n : ℕ) (y : ResidueGroup n) : refLaw n y ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (refLaw_le_one n y)

end CollatzPosDens
