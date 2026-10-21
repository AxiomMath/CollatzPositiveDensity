/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.BlackSet.BkCardinal

/-!
# The cardinal neighbourhood of a triangle

For a triangle `Δ`, its *cardinal neighbourhood* `𝒩(Δ)` is the set of points `v ∈ 𝒫` such that
`v ∉ Δ` and `v` is a cardinal neighbour of some point `x ∈ Δ`: the lattice points just outside
`Δ`, one unit step away from it.

## Main definitions

* `CollatzPosDens.bkNeighbourhood`: the cardinal neighbourhood `𝒩(Δ)` of a triangle `Δ`.

## Main results

* `CollatzPosDens.mem_bkNeighbourhood`: unfolding `v ∈ 𝒩(Δ)`.
* `CollatzPosDens.bkNeighbourhood_subset_bkPoints`: `𝒩(Δ) ⊆ 𝒫`.
* `CollatzPosDens.disjoint_bkNeighbourhood`: no point of `𝒩(Δ)` lies in `Δ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The *cardinal neighbourhood* `𝒩(Δ)` of a triangle `Δ`: the points `v ∈ 𝒫` with `v ∉ Δ`
that are cardinal neighbours of some point `x ∈ Δ`. -/
@[collatz_pos_dens "def_bk_neighbourhood"]
def bkNeighbourhood (Δ : BkTriangle) : Set (ℤ × ℤ) :=
  {v | v ∈ bkPoints ∧ v ∉ Δ ∧ ∃ x ∈ Δ, BkCardinalNeighbour v x}

variable {Δ : BkTriangle} {v x : ℤ × ℤ}

/-- Membership in `𝒩(Δ)`: `v ∈ 𝒫`, `v ∉ Δ` and `v` is a cardinal neighbour of a point of `Δ`. -/
theorem mem_bkNeighbourhood :
    v ∈ bkNeighbourhood Δ ↔ v ∈ bkPoints ∧ v ∉ Δ ∧ ∃ x ∈ Δ, BkCardinalNeighbour v x :=
  Iff.rfl

/-- A point of `𝒫` outside `Δ` that is a cardinal neighbour of a point of `Δ` lies in `𝒩(Δ)`. -/
theorem mem_bkNeighbourhood_of (hv : v ∈ bkPoints) (hvΔ : v ∉ Δ) (hx : x ∈ Δ)
    (hvx : BkCardinalNeighbour v x) : v ∈ bkNeighbourhood Δ :=
  ⟨hv, hvΔ, x, hx, hvx⟩

/-- A point of `𝒩(Δ)` lies in `𝒫`. -/
theorem mem_bkPoints_of_mem_bkNeighbourhood (h : v ∈ bkNeighbourhood Δ) : v ∈ bkPoints :=
  h.1

/-- A point of `𝒩(Δ)` does not lie in `Δ`. -/
theorem notMem_of_mem_bkNeighbourhood (h : v ∈ bkNeighbourhood Δ) : v ∉ Δ :=
  h.2.1

/-- A point of `𝒩(Δ)` is a cardinal neighbour of some point of `Δ`. -/
theorem exists_bkCardinalNeighbour_of_mem_bkNeighbourhood (h : v ∈ bkNeighbourhood Δ) :
    ∃ x ∈ Δ, BkCardinalNeighbour v x :=
  h.2.2

/-- The cardinal neighbourhood of a triangle lies in `𝒫`. -/
theorem bkNeighbourhood_subset_bkPoints (Δ : BkTriangle) : bkNeighbourhood Δ ⊆ bkPoints :=
  fun _ h => h.1

/-- No point of `𝒩(Δ)` lies in `Δ`. -/
theorem disjoint_bkNeighbourhood (Δ : BkTriangle) :
    Disjoint (bkNeighbourhood Δ) {p | p ∈ Δ} :=
  Set.disjoint_left.2 fun _ h => h.2.1

end CollatzPosDens
