/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.FxRefLawBounded

/-!
# The reference density in the extended nonnegative reals

For every `q ∈ ℕ` and `y ∈ G_q`, the identity `(2/3) · 3^q · μ_q(y) = ρ_q(y)` holds in `[0, ∞]`,
where the real number `ρ_q(y) ≥ 0` is regarded as an element of `[0, ∞)`. Since `μ_q(y) ≤ 1` is
finite, the truncation `μ_q(y)^ℝ` in the definition of `ρ_q` is `μ_q(y)` itself.

## Main results

* `CollatzPosDens.refLaw_mul_eq_ofReal_refDensity`: `(2/3) · 3^q · μ_q(y) = ρ_q(y)` in `ℝ≥0∞`.

## Implementation notes

The embedding `[0, ∞) → [0, ∞]` of the nonnegative real `ρ_q(y)` is `ENNReal.ofReal`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.3.
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

/-- The reference law and the reference density agree in `[0, ∞]`:
`(2/3) · 3^q · μ_q(y) = ρ_q(y)`. -/
@[collatz_pos_dens "lem_ref_density_ext"]
theorem refLaw_mul_eq_ofReal_refDensity (q : ℕ) (y : ResidueGroup q) :
    2 / 3 * 3 ^ q * refLaw q y = ENNReal.ofReal (refDensity q y) := by
  have hfin : refLaw q y ≠ ∞ := refLaw_ne_top q y
  rw [refDensity, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hfin,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos (by norm_num),
    ENNReal.ofReal_pow (by norm_num)]
  norm_num

end CollatzPosDens
