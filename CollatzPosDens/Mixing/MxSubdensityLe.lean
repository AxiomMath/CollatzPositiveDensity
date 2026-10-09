/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxSubdensity
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Mixing.MxSubmassLe

/-!
# The gate subdensity lies below the reference density

For `y ∈ G_n`, the gate subdensity `g_n(y) = (2/3) 3^n (Sub^n_{𝒰_n}(y))^ℝ` is at most the
reference density `ρ_n(y) = (2/3) 3^n μ_n(y)^ℝ`. Every word of the gate union `𝒰_n` has length
`n`, so `Sub^n_{𝒰_n}(y) ≤ μ_n(y) ≤ 1`; both values are finite, so the inequality survives the
passage to real numbers, and multiplying by `(2/3) 3^n > 0` gives `g_n(y) ≤ ρ_n(y)`.

## Main results

* `CollatzPosDens.mxSubdensity_le_refDensity`: `g_n(y) ≤ ρ_n(y)`.

## Implementation notes

The inequality is stated for every `n : ℕ`, without the hypothesis `n ≥ 1`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **The subdensity lies below the density.** For `y ∈ G_n`, `g_n(y) ≤ ρ_n(y)`. -/
@[collatz_pos_dens "lem_mx_subdensity_le"]
theorem mxSubdensity_le_refDensity (n : ℕ) (y : ResidueGroup n) :
    mxSubdensity n y ≤ refDensity n y := by
  rw [mxSubdensity_def, refDensity]
  have h := subMass_le_refLaw n (mxGateUnion_subset_setOf_length n) y
  gcongr
  exact refLaw_ne_top n y

end CollatzPosDens
