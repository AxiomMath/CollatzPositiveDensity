/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Basic.ENNReal.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.RefLaw

/-!
# The reference density on the residue spaces

For `q ∈ ℕ`, the reference density `ρ_q : G_q → ℝ` is the rescaled reference law
`ρ_q(y) = (2/3) · 3^q · μ_q(y)^ℝ`, where for `x ∈ [0, ∞]` the real number `x^ℝ` is `x` itself
when `x < ∞` and `0` when `x = ∞`.

## Main definitions

* `CollatzPosDens.refDensity q`: the function `ρ_q : G_q → ℝ`.

## Main results

* `CollatzPosDens.refDensity_nonneg`: `0 ≤ ρ_q(y)`.

## Implementation notes

The operation `x ↦ x^ℝ` is `ENNReal.toReal`, which sends `∞` to `0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The reference density `ρ_q(y) = (2/3) · 3^q · μ_q(y)^ℝ` on `G_q`, where `x^ℝ` is
`ENNReal.toReal x` (equal to `x` for `x < ∞` and to `0` for `x = ∞`). -/
@[collatz_pos_dens "def_ref_density"]
noncomputable def refDensity (q : ℕ) (y : ResidueGroup q) : ℝ :=
  2 / 3 * 3 ^ q * (refLaw q y).toReal

/-- The reference density is nonnegative. -/
theorem refDensity_nonneg (q : ℕ) (y : ResidueGroup q) : 0 ≤ refDensity q y := by
  unfold refDensity
  positivity

end CollatzPosDens
