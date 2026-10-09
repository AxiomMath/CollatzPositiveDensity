/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.Case3.C3Row
public import CollatzPosDens.Case3.C3RowMem
public import CollatzPosDens.Case3.C3Tip
public import CollatzPosDens.Case3.C3Anchors
public import CollatzPosDens.BlackSet.BkDisjoint
public import CollatzPosDens.BlackSet.BkEpsStarRange

/-!
# Separation of anchors

Let `Δ₀` be a triangle, `X ≥ 1` an integer and `s ≥ 4096 X`. Any two anchors `z < z'` in
`Anc(Δ₀, s, 2X)` satisfy `z' - z > (36/25) α s`.

Choose triangles `Δ, Γ` with anchors `z, z'` and put `rl = l_{Δ₀} + ⌊s / log 2⌋`. As
`s / log 2 ≥ s ≥ 2X + 1`, both triangles have their tip at most `l_{Δ₀} + 2X ≤ rl` and their
corner height `l_Θ = tip(Θ) + s_Θ / log 2 ≥ rl`, so `(z', rl) ∈ Γ`. If `z' ≤ row_Δ(rl)` then also
`(z', rl) ∈ Δ`, and disjointness of the family forces `Δ = Γ`, hence `z = z'`. Therefore
`z' > row_Δ(rl) = z + α (rl - tip(Δ)) ≥ z + α (s / log 2 - 1 - 2X)`, and
`s / log 2 - 1 - 2X > (36/25) s` because `log 2 < 347/500` and `s ≥ 4096 X`.

## Main results

* `CollatzPosDens.sub_gt_of_mem_bkAnchors_of_disjoint`: the separation for any family of
  triangles in which two members sharing a point are equal.
* `CollatzPosDens.sub_gt_of_mem_bkAnchors`: the separation for the canonical family
  `𝔗 = 𝔗_{n,ξ,ε_*}`, `ξ` a unit.

## Implementation notes

The source assumes `Δ₀ ∈ 𝔗`; this hypothesis is not used by the argument and is dropped. The
statement is first proved for an arbitrary family of triangles in which two members sharing a
point coincide, and then specialised to `𝔗_{n,ξ,ε_*}` through the disjointness of the canonical
family, which applies because `0 < ε_* < 1/27`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.2.
-/

@[expose] public section

namespace CollatzPosDens

open BkTriangle

/-- Separation of anchors for any family `T` of triangles in which two members sharing a point
are equal: if `X ≥ 1` is an integer, `s ≥ 4096 X` and `z < z'` both lie in `Anc(Δ₀, s, 2X)`,
then `z' - z > (36/25) α s`. -/
theorem sub_gt_of_mem_bkAnchors_of_disjoint {T : Set BkTriangle}
    (hT : ∀ Δ ∈ T, ∀ Γ ∈ T, ∀ x : ℤ × ℤ, x ∈ Δ → x ∈ Γ → Δ = Γ)
    {Δ₀ : BkTriangle} {X : ℤ} (hX : 1 ≤ X) {s : ℝ} (hs : 4096 * X ≤ s) {z z' : ℤ}
    (hz : z ∈ bkAnchors T Δ₀ s (2 * X)) (hz' : z' ∈ bkAnchors T Δ₀ s (2 * X)) (hlt : z < z') :
    36 / 25 * alpha * s < (z' : ℝ) - z := by
  obtain ⟨Δ, hΔ, hsΔ, hl₀Δ, htΔ', rfl⟩ := mem_bkAnchors.1 hz
  obtain ⟨Γ, hΓ, hsΓ, hl₀Γ, htΓ', rfl⟩ := mem_bkAnchors.1 hz'
  have hX' : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hs0 : 0 < s := by linarith
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2u : Real.log 2 < 347 / 500 := by
    have := Real.log_two_lt_d9
    norm_num at this ⊢
    linarith
  have hsl : 500 / 347 * s ≤ s / Real.log 2 := by
    rw [le_div_iff₀ h2]
    nlinarith
  set rl : ℤ := Δ₀.l + ⌊s / Real.log 2⌋ with hrl
  have hfl : (2 * X : ℤ) ≤ ⌊s / Real.log 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  have hfl' : (2 * X : ℝ) ≤ (⌊s / Real.log 2⌋ : ℝ) := by exact_mod_cast hfl
  have hrl_lo : (Δ₀.l : ℝ) + s / Real.log 2 - 1 ≤ rl := by
    have := Int.sub_one_lt_floor (s / Real.log 2)
    push_cast [hrl]
    linarith
  have hrl_hi : (rl : ℝ) ≤ Δ₀.l + s / Real.log 2 := by
    have := Int.floor_le (s / Real.log 2)
    push_cast [hrl]
    linarith
  have hrl_tip : (Δ₀.l : ℝ) + 2 * X ≤ rl := by
    push_cast [hrl]
    linarith
  -- The corner height of a qualifying triangle is at least `rl`.
  have key : ∀ Θ : BkTriangle, s ≤ Θ.s → (Δ₀.l : ℝ) ≤ Θ.tip → rl ≤ Θ.l := by
    intro Θ hsΘ hlo
    have hdiv : s / Real.log 2 ≤ Θ.s / Real.log 2 := div_le_div_of_nonneg_right hsΘ h2.le
    have hl := Θ.l_sub_tip
    have : (rl : ℝ) ≤ Θ.l := by linarith
    exact_mod_cast this
  have hlΓ := key Γ hsΓ hl₀Γ
  have hα := alpha_pos
  have hmemΓ : (Γ.j, rl) ∈ Γ := by
    refine Γ.mem_of_le_row hlΓ le_rfl ?_
    rw [row_def]
    have : (0 : ℝ) ≤ (rl : ℝ) - Γ.tip := by linarith
    nlinarith
  have hrow : Δ.row rl < Γ.j := by
    by_contra h
    rw [not_lt] at h
    have hmemΔ : (Γ.j, rl) ∈ Δ := Δ.mem_of_le_row (key Δ hsΔ hl₀Δ) hlt.le h
    exact hlt.ne (by have := hT Δ hΔ Γ hΓ _ hmemΔ hmemΓ; subst this; rfl)
  rw [row_def] at hrow
  have htΔ : Δ.tip ≤ (Δ₀.l : ℝ) + 2 * X := by linarith
  have hgap : 36 / 25 * s < (rl : ℝ) - Δ.tip := by
    nlinarith
  have := mul_lt_mul_of_pos_left hgap hα
  nlinarith

/-- **Anchors are separated**. Let `ξ` be a unit, `Δ₀` a triangle, `X ≥ 1` an integer and
`s ≥ 4096 X`. Any two elements `z < z'` of `Anc(Δ₀, s, 2X)`, relative to `𝔗 = 𝔗_{n,ξ,ε_*}`,
satisfy `z' - z > (36/25) α s`. -/
@[collatz_pos_dens "lem_c3_anchor_sep"]
theorem sub_gt_of_mem_bkAnchors {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {Δ₀ : BkTriangle} {X : ℤ} (hX : 1 ≤ X) {s : ℝ} (hs : 4096 * X ≤ s) {z z' : ℤ}
    (hz : z ∈ bkAnchors (bkFamily n ξ epsStar) Δ₀ s (2 * X))
    (hz' : z' ∈ bkAnchors (bkFamily n ξ epsStar) Δ₀ s (2 * X)) (hlt : z < z') :
    36 / 25 * alpha * s < (z' : ℝ) - z :=
  sub_gt_of_mem_bkAnchors_of_disjoint
    (fun _ hΔ _ hΓ _ hx hy => eq_of_mem_bkFamily_of_mem hξ epsStar_mem_bkRange.1
      epsStar_mem_bkRange.2 hΔ hΓ hx hy) hX hs hz hz' hlt

end CollatzPosDens
