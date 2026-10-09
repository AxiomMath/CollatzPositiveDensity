/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxSubmass

/-!
# Total mass of the submasses

For `n ∈ ℕ` and a set `𝒱` of words, the submasses `Sub^n_𝒱(y)` over the residues
`y ∈ G_n = ℤ/3^nℤ` add up to the geometric mass of `𝒱`:
$$\sum_{y \in G_n} \mathrm{Sub}^n_{\mathcal V}(y) = \mathbf{p}(\mathcal V).$$
All terms are nonnegative, so the double series may be summed in either order; summing over `y`
first, each word `w` contributes exactly once, at `y = [off(w)]_n`.

## Main results

* `CollatzPosDens.sum_subMass`: `∑_{y ∈ G_n} Sub^n_𝒱(y) = 𝐩(𝒱)`.

## Implementation notes

The source takes `𝒱 ⊆ ℤ_{≥1}^n`. The identity holds for every set of words, and is stated so.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.2.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The submasses over all residues add up to the geometric mass:
`∑_{y ∈ G_n} Sub^n_𝒱(y) = 𝐩(𝒱)`. -/
@[collatz_pos_dens "lem_mx_submass_total"]
theorem sum_subMass (n : ℕ) (V : Set Word) :
    ∑ y : ResidueGroup n, subMass n V y = geomMass V := by
  simp_rw [subMass_eq_tsum]
  rw [← Summable.tsum_finsetSum fun _ _ => ENNReal.summable, geomMass_def]
  exact tsum_congr fun w => by simp

end CollatzPosDens
