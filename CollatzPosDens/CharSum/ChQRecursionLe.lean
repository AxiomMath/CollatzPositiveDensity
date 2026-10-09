/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChRaw3Factor
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.CharSum.ChQRecursion
public import CollatzPosDens.CharSum.ChBlockHold
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldMass

/-!
# The renewal inequality for `Q`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For every `p ∈ 𝒫`, the renewal
function satisfies
`Q(p) ≤ w(p) ∑_{h ∈ 𝒫} η(h) Q(p + h)`,
the series converging.

Indeed, in the renewal recursion `Q(p) = w(p) ∑_{β ∈ 𝔅} bw(β) I(p; β) Q(p + bpt(β))` every term
is nonnegative and `I(p; β) ≤ 1`, so `Q(p) ≤ w(p) ∑_β bw(β) Q(p + bpt(β))`. Grouping the terms
according to the block point `h = bpt(β) ∈ 𝒫` and using `∑_{bpt(β) = h} bw(β) = η(h)` turns the
sum into `∑_h η(h) Q(p + h)`. Its terms are at most `η(h)`, so it converges since `η` has total
mass `1`.

## Main results

* `CollatzPosDens.chQ_le_mul_tsum_summable`: `h ↦ η(h) Q(p + h)` is summable on `𝒫`, for
  every `p`.
* `CollatzPosDens.chQ_le_mul_tsum`: for `p ∈ 𝒫`, `Q(p) ≤ w(p) ∑_{h ∈ 𝒫} η(h) Q(p + h)`.
* `CollatzPosDens.chQ_le_mul_tsum_hasSum_blocks`: the block series
  `∑_{β ∈ 𝔅} bw(β) Q(p + bpt(β))` has sum `∑_{h ∈ 𝒫} η(h) Q(p + h)`.

## Implementation notes

The sum over `𝒫` is a `tsum` over the subtype `bkPoints`, and `η(h)` for `h ∈ 𝒫 ⊆ ℤ × ℤ` is
`holdLaw h.1.toNat h.2`, as in `CollatzPosDens.tsum_holdLaw_bkPoints`. The convergence of
the series is stated separately, as a `Summable`, and holds for every base point `p`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Convergence of the renewal series.** For every `p`, `h ↦ η(h) Q(p + h)` is summable
on `𝒫`. -/
@[collatz_pos_dens "lem_ch_Q_recursion_le"]
theorem chQ_le_mul_tsum_summable (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    Summable fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h) :=
  hasSum_holdLaw_bkPoints.summable.of_nonneg_of_le
    (fun _ ↦ mul_nonneg (holdLaw_nonneg _ _) (chQ_nonneg _ _ _ _))
    fun _ ↦ mul_le_of_le_one_right (holdLaw_nonneg _ _) (chQ_le_one _ _ _ _)

/-- Grouping by block points: `∑_{β ∈ 𝔅} bw(β) Q(p + bpt(β)) = ∑_{h ∈ 𝒫} η(h) Q(p + h)`. -/
theorem chQ_le_mul_tsum_hasSum_blocks (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    HasSum (fun β : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)} ↦
        chBlockWeight β * chQ n ξ ε (p + chBlockPoint β))
      (∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h)) := by
  set B := {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}
  set g : B → ℝ := fun β ↦ chBlockWeight β * chQ n ξ ε (p + chBlockPoint β)
  have hg : Summable g := hasSum_prod_chBlockWeight_single.summable.of_nonneg_of_le
    (fun _ ↦ mul_nonneg (chBlockWeight_nonneg _) (chQ_nonneg _ _ _ _))
    fun _ ↦ mul_le_of_le_one_right (chBlockWeight_nonneg _) (chQ_le_one _ _ _ _)
  let bpt : B → bkPoints := fun β ↦ ⟨chBlockPoint β, chBlockPoint_mem_bkPoints _⟩
  suffices hfun : (fun c ↦ ∑' b : ↥(bpt ⁻¹' {c}), g b) =
      fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h) by
    exact (hfun ▸ hg.hasSum.tsum_fiberwise bpt).tsum_eq ▸ hg.hasSum
  funext h
  let e : ↥(bpt ⁻¹' {h}) ≃
      {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockPoint β = h} :=
    { toFun := fun β ↦ ⟨β.1.1, β.1.2, congrArg Subtype.val β.2⟩
      invFun := fun β ↦ ⟨⟨β.1, β.2.1⟩, Subtype.ext β.2.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hg' (β : ↥(bpt ⁻¹' {h})) : g β = chBlockWeight (e β).1 * chQ n ξ ε (p + h) := by
    simp only [g, e, Equiv.coe_fn_mk, show chBlockPoint β.1.1 = h from congrArg Subtype.val β.2]
  rw [tsum_congr hg', e.tsum_eq (fun β ↦ chBlockWeight β.1 * chQ n ξ ε (p + h)), tsum_mul_right,
    holdLaw_eq_tsum_chBlockWeight h.2]

/-- **Renewal inequality for `Q`.** For `p ∈ 𝒫`, `Q(p) ≤ w(p) ∑_{h ∈ 𝒫} η(h) Q(p + h)`; the
series converges by `chQ_le_mul_tsum_summable`. -/
@[collatz_pos_dens "lem_ch_Q_recursion_le"]
theorem chQ_le_mul_tsum (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) {p : ℤ × ℤ}
    (hp : p ∈ bkPoints) :
    chQ n ξ ε p ≤
      chWhiteFactor n ξ ε p * ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ ε (p + h) := by
  have hblk := chQ_le_mul_tsum_hasSum_blocks n ξ ε p
  rw [chQ_eq_mul_tsum n ξ ε hp, ← hblk.tsum_eq]
  refine mul_le_mul_of_nonneg_left ?_ (chWhiteFactor_nonneg _ _ _ _)
  have hle : ∀ β : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
      chBlockWeight β * chInternalWeight n ξ ε p β * chQ n ξ ε (p + chBlockPoint β) ≤
        chBlockWeight β * chQ n ξ ε (p + chBlockPoint β) := fun β ↦ by
    rw [mul_right_comm]
    exact mul_le_of_le_one_right
      (mul_nonneg (chBlockWeight_nonneg _) (chQ_nonneg _ _ _ _))
      (chInternalWeight_le_one _ _ _ _ _)
  exact Summable.tsum_le_tsum hle (hblk.summable.of_nonneg_of_le (fun β ↦ mul_nonneg
    (mul_nonneg (chBlockWeight_nonneg _) (chInternalWeight_nonneg _ _ _ _ _))
    (chQ_nonneg _ _ _ _)) hle) hblk.summable

end CollatzPosDens
