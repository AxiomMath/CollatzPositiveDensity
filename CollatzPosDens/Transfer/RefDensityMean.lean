/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.FxRefLawTotal
public import CollatzPosDens.Transfer.FxRefLawBounded

/-!
# The mean of the reference density

For every `q ∈ ℕ` the reference density `ρ_q` has uniform average `⟨ρ_q⟩_q = 2/3`. Since each
`μ_q(y)` is finite, `∑_y ρ_q(y) = (2/3) · 3^q · (∑_y μ_q(y))^ℝ = (2/3) · 3^q`, the reference law
having total mass one; dividing by `3^q` gives `2/3`.

## Main results

* `CollatzPosDens.sum_refDensity`: `∑_{y ∈ G_q} ρ_q(y) = (2/3) · 3^q`.
* `CollatzPosDens.residueAvg_refDensity`: `⟨ρ_q⟩_q = 2/3`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- The total mass of the reference density: `∑_{y ∈ G_q} ρ_q(y) = (2/3) · 3^q`. -/
theorem sum_refDensity (q : ℕ) : ∑ y, refDensity q y = 2 / 3 * 3 ^ q := by
  simp_rw [refDensity, ← Finset.mul_sum]
  rw [← ENNReal.toReal_sum fun y _ =>
      refLaw_ne_top q y,
    sum_refLaw, ENNReal.toReal_one, mul_one]

/-- The reference density has mean `2/3`: `⟨ρ_q⟩_q = 2/3`. -/
@[collatz_pos_dens "lem_ref_density_mean"]
theorem residueAvg_refDensity (q : ℕ) : residueAvg q (refDensity q) = 2 / 3 := by
  rw [residueAvg_def, sum_refDensity]
  field_simp

end CollatzPosDens
