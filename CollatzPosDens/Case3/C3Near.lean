/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkDrift
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.Case3.C3Tip
public import CollatzPosDens.Case3.C3RowBound
public import CollatzPosDens.Case3.C3Anchors
public import CollatzPosDens.Case3.C3Big
public import CollatzPosDens.Case3.C3Close
public import CollatzPosDens.Case3.C3Eprime
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.Renewal.RnFpSupport
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# Outside the exceptional event, large triangles sit at anchors

Let `𝔗 = 𝔗_{n,ξ,ε_*}` with `ξ` a unit, `e = (j₀, l₀) ∈ Δ₀ ∈ 𝔗`, `G ∈ ℕ` with `l₀ + G = l_{Δ₀}`,
`v ∈ ℕ`, `X` and `s` reals, and assume `2 G^{3/5} + 2 α X + 1 ≤ G δ₀`. If an atom
`a = ((r, ℓ), β)` of the fresh law has `μ_{e,G}(a) ≠ 0`, lies in the large-triangle event
`Big_{e,G,v,s}` and not in the exceptional event `Ex_{e,G,v,X}`, then some anchor
`z ∈ Anc(Δ₀, s, 2X)` satisfies `-X < r + j₀ - z < 2 α X`.

Nonzero mass forces `ℓ > G` and a nonzero weight for every block `βᵏ`; a block of nonzero
weight has all its nonclosing letters at least `2`, and its closing letter lies in `{4, 5}`, so
its block point `(j(βᵏ), l(βᵏ))` satisfies `1 ≤ j(βᵏ) ≤ l(βᵏ)`. Let `u ≤ v` and `Δ' ∈ 𝔗` with
`s_{Δ'} ≥ s` and `(j, l) = y^e_u(a) ∈ Δ'`. With `H_u = ∑_{k ≤ u} j(βᵏ)` and
`V_u = ∑_{k ≤ u} l(βᵏ)` we have `j = j₀ + r + H_u` and `l = l₀ + ℓ + V_u`; outside the
exceptional event `0 < l - l_{Δ₀} < 2X` and `|j - (j₀ + G/4)| < 2 G^{3/5}`. So `Δ' ≠ Δ₀`,
`le_tip_of_mem_bkFamily` gives `l_{Δ₀} ≤ tip(Δ')`, `BkTriangle.row_bound_of_mem` gives
`tip(Δ') ≤ l` and `0 ≤ j - j_{Δ'} < 2 α X`, and `z = j_{Δ'}` works since `0 ≤ H_u ≤ V_u < X`.

## Main results

* `CollatzPosDens.exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional`: the
  statement for `𝔗_{n,ξ,ε}` with any `0 < ε < 1/27`.
* `CollatzPosDens.exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional_epsStar`: the
  statement for the canonical family `𝔗_{n,ξ,ε_*}`.

## Implementation notes

The source takes `X ≥ 1` an integer and `v ≤ J = ⌊n/2⌋`; neither is used, so `X` is any real
number and `v` any natural number, which generalizes the source. The bound
`1 ≤ j(βᵏ) ≤ l(βᵏ)` on the block points is read off the block weight directly (a block of
nonzero weight has nonclosing letters `≥ 2`), rather than through the holding law `η`; the two
are equivalent by the block decomposition of `η`. The atom is written `((r, ℓ), β)` and the
point `e = (j(e), l(e))`; the conclusion is stated in `ℝ`.

## References

* [Mazur, *Collatz positive density*], §10.3.
-/

@[expose] public section

namespace CollatzPosDens

open BkTriangle

/-- A block of nonzero weight with closing letter in `{4, 5}` has `j(bpt β) ≤ l(bpt β)`. -/
private lemma c3Near_fst_le_snd {b : List ℤ × ℤ} (hw : chBlockWeight b ≠ 0)
    (he : b.2 ∈ ({4, 5} : Set ℤ)) : bkJ (chBlockPoint b) ≤ bkL (chBlockPoint b) := by
  obtain ⟨c, e⟩ := b
  have : 2 * (c.length : ℤ) ≤ c.sum := two_mul_length_le_sum_of_chBlockWeight_ne_zero hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
  simp only [bkJ, bkL, chBlockPoint_fst, chBlockPoint_snd]
  omega

/-- Partial sums of nonnegative terms are monotone in the number of terms. -/
private lemma c3Near_sum_take_le {f : List ℤ × ℤ → ℤ} {β : List (List ℤ × ℤ)}
    (hf : ∀ b ∈ β, 0 ≤ f b) {u v : ℕ} (huv : u ≤ v) :
    ((β.take u).map f).sum ≤ ((β.take v).map f).sum := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le huv
  rw [List.take_add, List.map_append, List.sum_append, le_add_iff_nonneg_right]
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  exact hf b (List.mem_of_mem_drop (List.mem_of_mem_take hb))

/-- **Large triangles sit at anchors**, for `𝔗_{n,ξ,ε}` with `ξ` a unit and `0 < ε < 1/27`. -/
theorem exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional {n : ℕ}
    {ξ : ResidueGroup n} {ε : ℝ} (hξ : IsResidueUnit ξ) (hε : 0 < ε) (hε' : ε < 1 / 27)
    {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ ε) {e : ℤ × ℤ} (he : e ∈ Δ₀) {G v : ℕ}
    (hG : bkL e + G = Δ₀.l) {X s : ℝ}
    (hGδ : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + 2 * alpha * X + 1 ≤ G * drift)
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hμ : trFreshLaw n e G a ≠ 0)
    (hbig : a ∈ c3Big n ξ ε e G v s) (hex : a ∉ c3Exceptional n e G v X) :
    ∃ z ∈ bkAnchors (bkFamily n ξ ε) Δ₀ s (2 * X),
      -X < (a.1.1 : ℝ) + bkJ e - z ∧ (a.1.1 : ℝ) + bkJ e - z < 2 * alpha * X := by
  obtain ⟨⟨r, ℓ⟩, β⟩ := a
  obtain ⟨ha, u, huv, Δ', hΔ', hy, hs⟩ := mem_c3Big.1 hbig
  rw [notMem_c3Exceptional_iff ha] at hex
  obtain ⟨hex₁, hex₂, hex₃, hex₄⟩ := hex
  simp only at hex₁ hex₂ hex₃ hex₄
  rw [trFreshLaw_mk] at hμ
  have hℓ : (G : ℤ) < ℓ := (firstPassageLaw_support (left_ne_zero_of_mul hμ)).2
  have hw : ∀ b ∈ β, chBlockWeight b ≠ 0 :=
    trListWeight_ne_zero_iff.1 (right_ne_zero_of_mul hμ)
  have hjl : ∀ b ∈ β, bkJ (chBlockPoint b) ≤ bkL (chBlockPoint b) := fun b hb =>
    c3Near_fst_le_snd (hw b hb) (trAtoms_closing_mem ha hb)
  have hj0 : ∀ b ∈ β, 0 ≤ bkJ (chBlockPoint b) := fun b _ => by
    simp only [bkJ, chBlockPoint_fst]; positivity
  have hl0 : ∀ b ∈ β, 0 ≤ bkL (chBlockPoint b) := fun b hb => (hj0 b hb).trans (hjl b hb)
  set H : ℤ := ((β.take u).map fun b => bkJ (chBlockPoint b)).sum with hH
  set V : ℤ := ((β.take u).map fun b => bkL (chBlockPoint b)).sum with hV
  have hyJ : bkJ (trFreshPath e ((r, ℓ), β) u) = bkJ e + r + H := by
    rw [trFreshPath_def, trPath_eq_add_chBlockPath, chBlockPath]
    simp only [bkJ, Prod.fst_add] at hH ⊢
    rw [hH]
    exact congrArg (_ + ·) ((bkJ_list_sum _).trans (congrArg List.sum (List.map_map ..)))
  have hyL : bkL (trFreshPath e ((r, ℓ), β) u) = bkL e + ℓ + V := by
    rw [trFreshPath_def, trPath_eq_add_chBlockPath, chBlockPath]
    simp only [bkL, Prod.snd_add] at hV ⊢
    rw [hV]
    exact congrArg (_ + ·) ((bkL_list_sum _).trans (congrArg List.sum (List.map_map ..)))
  set y := trFreshPath e ((r, ℓ), β) u with hydef
  have hH0 : 0 ≤ H := List.sum_nonneg fun x hx => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    exact hj0 b (List.mem_of_mem_take hb)
  have hHV : H ≤ V := List.sum_le_sum fun b hb => hjl b (List.mem_of_mem_take hb)
  have hHv : (H : ℝ) ≤ (((β.take v).map fun b => bkJ (chBlockPoint b)).sum : ℤ) := by
    exact_mod_cast c3Near_sum_take_le hj0 huv
  have hVv : (V : ℝ) ≤ (((β.take v).map fun b => bkL (chBlockPoint b)).sum : ℤ) := by
    exact_mod_cast c3Near_sum_take_le hl0 huv
  have hV0 : (0 : ℝ) ≤ V := by exact_mod_cast hH0.trans hHV
  have hHVr : (H : ℝ) ≤ V := by exact_mod_cast hHV
  have hℓr : (G : ℝ) < ℓ := by exact_mod_cast hℓ
  have hGr : ((bkL e : ℤ) : ℝ) + G = Δ₀.l := by exact_mod_cast hG
  have hlr : ((bkL y : ℤ) : ℝ) = (bkL e : ℝ) + ℓ + V := by rw [hyL]; push_cast; ring
  have hjr : ((bkJ y : ℤ) : ℝ) = (bkJ e : ℝ) + r + H := by rw [hyJ]; push_cast; ring
  have hl₁ : Δ₀.l < bkL y := by
    have : ((Δ₀.l : ℤ) : ℝ) < ((bkL y : ℤ) : ℝ) := by rw [hlr, ← hGr]; linarith
    exact_mod_cast this
  have hl₂ : ((bkL y : ℤ) : ℝ) < Δ₀.l + 2 * X := by rw [hlr, ← hGr]; linarith
  have hj : |((bkJ y : ℤ) : ℝ) - ((bkJ e : ℤ) + (G : ℝ) / 4)| ≤ 2 * (G : ℝ) ^ ((3 : ℝ) / 5) := by
    rw [hjr, show (bkJ e : ℝ) + r + H - ((bkJ e : ℤ) + (G : ℝ) / 4) = ((r : ℝ) - G / 4) + H by
      ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg (by exact_mod_cast hH0 : (0 : ℝ) ≤ H)]
    linarith
  have hne : Δ₀ ≠ Δ' := by
    rintro rfl
    exact absurd (le_l_of_mem hy) (not_le.2 hl₁)
  have hE : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + alpha * (2 * X) + 1 ≤ G * drift := by linarith
  have hy' : (bkJ y, bkL y) ∈ Δ' := hy
  have he' : (bkJ e, bkL e) ∈ Δ₀ := he
  have htip : (Δ₀.l : ℝ) ≤ Δ'.tip :=
    le_tip_of_mem_bkFamily hξ hε hε' hΔ₀ hΔ' hne he' hG hy' hl₁.le hl₂.le hj hE
  have hrow := row_bound_of_mem hy
  have hjz : Δ'.j ≤ bkJ y := ((mem_iff).1 hy).1
  have hjz' : (0 : ℝ) ≤ ((bkJ y - Δ'.j : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.2 hjz
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htip₂ : Δ'.tip ≤ ((bkL y : ℤ) : ℝ) := by
    have : 0 ≤ ((bkL y : ℝ) - Δ'.tip) * Real.log 2 :=
      (mul_nonneg hjz' hlog9.le).trans hrow
    have := nonneg_of_mul_nonneg_left this hlog2
    linarith
  refine ⟨Δ'.j, j_mem_bkAnchors hΔ' hs htip (by linarith), ?_, ?_⟩
  · have : ((bkJ y - Δ'.j : ℤ) : ℝ) = (bkJ e : ℝ) + r + H - Δ'.j := by
      rw [← hjr]; push_cast; ring
    have hX : (V : ℝ) < X := hVv.trans_lt hex₂
    linarith
  · have h1 : ((bkJ y - Δ'.j : ℤ) : ℝ) * Real.log 9 < 2 * X * Real.log 2 := by
      refine hrow.trans_lt ?_
      exact mul_lt_mul_of_pos_right (by linarith) hlog2
    have h2 : ((bkJ y - Δ'.j : ℤ) : ℝ) < 2 * alpha * X := by
      rw [alpha_def, show 2 * (Real.log 2 / Real.log 9) * X = 2 * X * Real.log 2 / Real.log 9 by
        ring, lt_div_iff₀ hlog9]
      exact h1
    have : ((bkJ y - Δ'.j : ℤ) : ℝ) = (bkJ e : ℝ) + r + H - Δ'.j := by
      rw [← hjr]; push_cast; ring
    have : (0 : ℝ) ≤ H := by exact_mod_cast hH0
    linarith

/-- **Outside the exceptional event, large triangles sit at anchors**. Let `ξ` be a unit,
`e = (j₀, l₀) ∈ Δ₀ ∈ 𝔗 = 𝔗_{n,ξ,ε_*}`, `G ∈ ℕ` with `l₀ + G = l_{Δ₀}`, `v ∈ ℕ`, `X, s ∈ ℝ`, and
assume `2 G^{3/5} + 2 α X + 1 ≤ G δ₀`. If an atom `a = ((r, ℓ), β)` has `μ_{e,G}(a) ≠ 0`,
`a ∈ Big_{e,G,v,s}` and `a ∉ Ex_{e,G,v,X}`, then there is `z ∈ Anc(Δ₀, s, 2X)` with
`-X < r + j₀ - z < 2 α X`. -/
@[collatz_pos_dens "lem_c3_near"]
theorem exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional_epsStar {n : ℕ}
    {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ) {Δ₀ : BkTriangle}
    (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ} (he : e ∈ Δ₀) {G v : ℕ}
    (hG : bkL e + G = Δ₀.l) {X s : ℝ}
    (hGδ : 2 * (G : ℝ) ^ ((3 : ℝ) / 5) + 2 * alpha * X + 1 ≤ G * drift)
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hμ : trFreshLaw n e G a ≠ 0)
    (hbig : a ∈ c3Big n ξ epsStar e G v s) (hex : a ∉ c3Exceptional n e G v X) :
    ∃ z ∈ bkAnchors (bkFamily n ξ epsStar) Δ₀ s (2 * X),
      -X < (a.1.1 : ℝ) + bkJ e - z ∧ (a.1.1 : ℝ) + bkJ e - z < 2 * alpha * X :=
  exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional hξ
    epsStar_mem_bkRange.1 epsStar_mem_bkRange.2 hΔ₀ he hG hGδ hμ hbig hex

end CollatzPosDens
