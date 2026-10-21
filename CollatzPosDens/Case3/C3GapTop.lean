/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkCover
public import CollatzPosDens.BlackSet.BkDisjoint
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.BlackSet.BkSourceMem
public import CollatzPosDens.StoppingTrace.TrGap

/-!
# The top of a canonical triangle through a point

Let `ξ` be a unit and `0 < ε < 1/27`. If a point `e` lies in a triangle `Δ` of the canonical
family `𝔗_{n,ξ,ε}`, then the second corner coordinate of `Δ` is `l_Δ = l(e) + gap(e)`.
Indeed `e` is black, since it lies in a member of `𝔗`; it lies in its own canonical triangle
`Δ(e) ∈ 𝔗`; disjointness of the family gives `Δ = Δ(e)`; and `l_{Δ(e)} = l_*(e) = l(e) + gap(e)`.

## Main results

* `CollatzPosDens.bkFamily_l_eq_add_trGap`: `l_Δ = l(e) + gap(e)` for `e ∈ Δ ∈ 𝔗_{n,ξ,ε}`,
  for every `0 < ε < 1/27`.
* `CollatzPosDens.bkFamily_epsStar_l_eq_add_trGap`: the same at the colour scale `ε = ε_*`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `ξ` be a unit and `0 < ε < 1/27`. If `Δ ∈ 𝔗_{n,ξ,ε}` and `e ∈ Δ`, then
`l_Δ = l(e) + gap(e)`. -/
theorem bkFamily_l_eq_add_trGap {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {Δ : BkTriangle}
    {e : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hε₀ : 0 < ε) (hε : ε < 1 / 27)
    (hΔ : Δ ∈ bkFamily n ξ ε) (he : e ∈ Δ) :
    Δ.l = bkL e + trGap n ξ ε e := by
  have hp : e ∈ bkPoints := BkTriangle.mem_bkPoints_of_mem he
  have hb : BkBlack n ξ ε e :=
    (bkBlack_iff_exists_mem_bkFamily hξ hε₀ hε hp).2 ⟨Δ, hΔ, he⟩
  have heq : Δ = bkCanonTriangle n ξ ε e hp :=
    eq_of_mem_bkFamily_of_mem hξ hε₀ hε hΔ (bkCanonTriangle_mem_bkFamily hp hb) he
      (mem_bkCanonTriangle_self hξ hε₀ hε hp hb)
  rw [heq, bkCanonTriangle_l, bkColTop_eq_add_trGap]

/-- **The top of a canonical triangle.** Let `ξ` be a unit, `Δ ∈ 𝔗 = 𝔗_{n,ξ,ε_*}` and
`e ∈ Δ`. Then `l_Δ = l(e) + gap(e)`. -/
@[collatz_pos_dens "lem_c3_gap_top"]
theorem bkFamily_epsStar_l_eq_add_trGap {n : ℕ} {ξ : ResidueGroup n} {Δ : BkTriangle}
    {e : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hΔ : Δ ∈ bkFamily n ξ (epsStar : ℝ)) (he : e ∈ Δ) :
    Δ.l = bkL e + trGap n ξ (epsStar : ℝ) e :=
  bkFamily_l_eq_add_trGap hξ epsStar_mem_bkRange.1 epsStar_mem_bkRange.2 hΔ he

end CollatzPosDens
