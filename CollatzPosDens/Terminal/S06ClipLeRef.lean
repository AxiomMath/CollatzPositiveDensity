/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxSubmassLe
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Terminal.S06ClipDensity

/-!
# The clipped subdensity is below the reference density

For every `y ∈ G_m`, `0 ≤ g^clp_{m,n,B}(y) ≤ ρ_m(y)`. The clipped words have length `m`, so
their submass is at most the reference law, `Sub^m_{𝒱^clp_{m,n,B}}(y) ≤ μ_m(y) ≤ 1`; both are
finite, and multiplying by `3^m` gives the bound.

## Main results

* `CollatzPosDens.clipDensity_le_refDensity`: `g^clp_{m,n,B}(y) ≤ ρ_m(y)`.
* `CollatzPosDens.clipDensity_mem_Icc`: `g^clp_{m,n,B}(y) ∈ [0, ρ_m(y)]`.

## Implementation notes

The paper assumes `m ≥ 1`, `n ≥ 2` and `B > 0`; the bounds hold for all `m, n ∈ ℕ` and real
`B`, and are stated so.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The clipped subdensity is at most the reference density: `g^clp_{m,n,B}(y) ≤ ρ_m(y)`. -/
theorem clipDensity_le_refDensity (m n : ℕ) (B : ℝ) (y : ResidueGroup m) :
    clipDensity m n B y ≤ refDensity m y := by
  rw [clipDensity_def, refDensity]
  gcongr
  · exact refLaw_ne_top m y
  · exact subMass_le_refLaw m (fun u hu => length_of_mem_clipWords hu) y

/-- **The clipped subdensity is below the reference density.** For every `y ∈ G_m`,
`0 ≤ g^clp_{m,n,B}(y) ≤ ρ_m(y)`. -/
@[collatz_pos_dens "lem_s06_clip_le_ref"]
theorem clipDensity_mem_Icc (m n : ℕ) (B : ℝ) (y : ResidueGroup m) :
    clipDensity m n B y ∈ Set.Icc 0 (refDensity m y) :=
  ⟨clipDensity_nonneg m n B y, clipDensity_le_refDensity m n B y⟩

end CollatzPosDens
