/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.Case3.C3Row
public import CollatzPosDens.Case3.C3RowMem
public import CollatzPosDens.Case3.C3Tip
public import CollatzPosDens.Case3.C3Anchors
public import CollatzPosDens.BlackSet.BkDisjoint
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.Transfer.S02AdaptiveAnchor

/-!
# Separation of anchors

Let `Δ₀` be a triangle, `W ≥ 0` and `s > 0` real numbers with `b_an s - W - 1 > 0`, where
`b_an` is the adaptive anchor constant. Any two anchors `z < z'` in `Anc(Δ₀, s, W)` satisfy
`z' - z > α (b_an s - W - 1)`.

Choose triangles `Δ, Γ` with anchors `z, z'` and put `rl = l_{Δ₀} + ⌊s / log 2⌋`. Since
`0 < b_an < 1 / log 2`, we have `s / log 2 > b_an s > W + 1`, so `⌊s / log 2⌋ > W`; both
triangles have their tip at most `l_{Δ₀} + W < rl` and their corner height
`l_Θ = tip(Θ) + s_Θ / log 2 ≥ rl`, so `(z', rl) ∈ Γ`. If `z' ≤ row_Δ(rl)` then also
`(z', rl) ∈ Δ`, and disjointness of the family forces `Δ = Γ`, hence `z = z'`. Therefore
`z' > row_Δ(rl) = z + α (rl - tip(Δ)) ≥ z + α (s / log 2 - 1 - W) > z + α (b_an s - 1 - W)`.

## Main results

* `CollatzPosDens.sub_gt_of_mem_bkAnchors_of_disjoint`: the separation for any family of
  triangles in which two members sharing a point are equal.
* `CollatzPosDens.sub_gt_of_mem_bkAnchors`: the separation for the canonical family
  `𝔗 = 𝔗_{n,ξ,ε_*}`, `ξ` a unit.

## Implementation notes

The source assumes `Δ₀ ∈ 𝔗` and `W ≥ 0`; neither is used by the argument, so both are dropped.
The statement is first proved for an arbitrary family of triangles in which two members sharing
a point coincide, and then specialised to `𝔗_{n,ξ,ε_*}` through the disjointness of the canonical
family, which applies because `0 < ε_* < 1/27`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open BkTriangle

/-- Separation of anchors for any family `T` of triangles in which two members sharing a point
are equal: if `s > 0`, `b_an s - W - 1 > 0` and `z < z'` both lie in `Anc(Δ₀, s, W)`,
then `z' - z > α (b_an s - W - 1)`. -/
theorem sub_gt_of_mem_bkAnchors_of_disjoint {T : Set BkTriangle}
    (hT : ∀ Δ ∈ T, ∀ Γ ∈ T, ∀ x : ℤ × ℤ, x ∈ Δ → x ∈ Γ → Δ = Γ)
    {Δ₀ : BkTriangle} {W s : ℝ} (hs0 : 0 < s) (hpos : 0 < (bAn : ℝ) * s - W - 1) {z z' : ℤ}
    (hz : z ∈ bkAnchors T Δ₀ s W) (hz' : z' ∈ bkAnchors T Δ₀ s W) (hlt : z < z') :
    alpha * ((bAn : ℝ) * s - W - 1) < (z' : ℝ) - z := by
  obtain ⟨Δ, hΔ, hsΔ, hl₀Δ, htΔ', rfl⟩ := mem_bkAnchors.1 hz
  obtain ⟨Γ, hΓ, hsΓ, hl₀Γ, htΓ', rfl⟩ := mem_bkAnchors.1 hz'
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨-, hb⟩ := bAn_pos_and_lt
  have hsl : (bAn : ℝ) * s < s / Real.log 2 := by
    have := mul_lt_mul_of_pos_right hb hs0
    rwa [one_div_mul_eq_div] at this
  set rl : ℤ := Δ₀.l + ⌊s / Real.log 2⌋ with hrl
  have hrl_lo : (Δ₀.l : ℝ) + s / Real.log 2 - 1 < rl := by
    have := Int.sub_one_lt_floor (s / Real.log 2)
    push_cast [hrl]
    linarith
  have hrl_hi : (rl : ℝ) ≤ Δ₀.l + s / Real.log 2 := by
    have := Int.floor_le (s / Real.log 2)
    push_cast [hrl]
    linarith
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
    by_contra! h
    have hmemΔ : (Γ.j, rl) ∈ Δ := Δ.mem_of_le_row (key Δ hsΔ hl₀Δ) hlt.le h
    exact hlt.ne (congrArg BkTriangle.j (hT Δ hΔ Γ hΓ _ hmemΔ hmemΓ))
  rw [row_def] at hrow
  have hgap : (bAn : ℝ) * s - W - 1 < (rl : ℝ) - Δ.tip := by linarith
  have := mul_lt_mul_of_pos_left hgap hα
  linarith

/-- **Anchors are separated**. Let `ξ` be a unit, `Δ₀` a triangle, and `W`, `s > 0` real
numbers with `b_an s - W - 1 > 0`. Any two elements `z < z'` of `Anc(Δ₀, s, W)`, relative
to `𝔗 = 𝔗_{n,ξ,ε_*}`, satisfy `z' - z > α (b_an s - W - 1)`. -/
@[collatz_pos_dens "lem_c3_anchor_sep"]
theorem sub_gt_of_mem_bkAnchors {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {Δ₀ : BkTriangle} {W s : ℝ} (hs0 : 0 < s) (hpos : 0 < (bAn : ℝ) * s - W - 1) {z z' : ℤ}
    (hz : z ∈ bkAnchors (bkFamily n ξ epsStar) Δ₀ s W)
    (hz' : z' ∈ bkAnchors (bkFamily n ξ epsStar) Δ₀ s W) (hlt : z < z') :
    alpha * ((bAn : ℝ) * s - W - 1) < (z' : ℝ) - z :=
  sub_gt_of_mem_bkAnchors_of_disjoint
    (fun _ hΔ _ hΓ _ hx hy => eq_of_mem_bkFamily_of_mem hξ epsStar_mem_bkRange.1
      epsStar_mem_bkRange.2 hΔ hΓ hx hy) hs0 hpos hz hz' hlt

end CollatzPosDens
