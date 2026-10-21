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
public import CollatzPosDens.Case3.C3Cols
public import CollatzPosDens.Case3.C3Eprime
public import CollatzPosDens.Case3.C3InitEvent
public import CollatzPosDens.Transfer.S02Wtot
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.Renewal.RnFpSupport
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# Outside the deviation event, large triangles sit at anchor columns

Let `ι ∈ 𝔍` be a Fourier index, `𝔗 = 𝔗_{n,ξ,ε_*}` with `ξ` a unit, `e = (j₀, l₀) ∈ Δ₀ ∈ 𝔗`,
`g ∈ ℕ` with `l₀ + g = l_{Δ₀}`, `v ∈ ℕ` and `s` real, and assume
`g/32 + X_d(ι, v) + X_l(ι, v)/4 + λ W(ι, v) + 1 ≤ g λ₀`, where `λ = log 2 / log 9`,
`λ₀ = λ - 1/4` and `W(ι, v) = X_o(ι) + X_l(ι, v)`. If an atom `a = ((r, ℓ), β)` of
the fresh law has `μ_{e,g}(a) ≠ 0`, lies in the large-triangle event `Big_{e,v,s}` and not in
the deviation event `Dev_{g,v}(ι)`, then `r` lies in the anchor columns `𝒰_{e,Δ₀,v,s}(ι)`.

Nonzero mass forces `ℓ > g` and a nonzero weight for every block `βᵏ`, whence
`1 ≤ j(βᵏ) ≤ l(βᵏ)` for its block point. Let `u ≤ v` and `Δ' ∈ 𝔗` with `s_{Δ'} ≥ s` and
`(j, l) = y^e_u(a) ∈ Δ'`. With `H_u = ∑_{k ≤ u} j(βᵏ)` and `V_u = ∑_{k ≤ u} l(βᵏ)` we have
`j = j₀ + r + H_u` and `l = l₀ + ℓ + V_u`. Outside the deviation event `0 < ℓ - g < X_o(ι)`,
`0 ≤ V_u < X_l(ι, v)`, `|r - g/4| < g/32` and `|H_u - V_u/4| < X_d(ι, v)`, so
`0 < l - l_{Δ₀} < W(ι, v)` and `|j - (j₀ + g/4)| < g/32 + X_d(ι, v) + X_l(ι, v)/4`. Hence
`Δ' ≠ Δ₀`, `le_tip_of_mem_bkFamily` gives `l_{Δ₀} ≤ tip(Δ')`, `BkTriangle.tip_le_bkL_of_mem`
gives `tip(Δ') ≤ l` and `BkTriangle.bkJ_sub_j_le_of_mem` gives `0 ≤ j - j_{Δ'} ≤ λ (l - l_{Δ₀})`,
so `z = j_{Δ'} ∈ Anc(Δ₀, s, W(ι, v))`, and `i = r + j₀ - z` satisfies
`-X_d(ι, v) - X_l(ι, v)/4 < i < λ X_o(ι) + λ₀ X_l(ι, v) + X_d(ι, v)`.

## Main results

* `CollatzPosDens.exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional`: `r` lies in the
  anchor columns, for `𝔗_{n,ξ,ε}` with any `0 < ε < 1/27`.
* `CollatzPosDens.exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional_epsStar`: `r` lies in
  the anchor columns, for the canonical family `𝔗_{n,ξ,ε_*}`.
* `CollatzPosDens.bkJ_trFreshPath`, `CollatzPosDens.bkL_trFreshPath`: the coordinates of the
  fresh path.
* `CollatzPosDens.BkTriangle.bkJ_sub_j_le_of_mem`: `j - j_Δ ≤ λ (l - tip(Δ))` on a triangle.

## Implementation notes

[Mazur] assumes `v ≤ J = ⌊n/2⌋`; this hypothesis is not needed, so `v` is any natural
number. The bound `1 ≤ j(βᵏ) ≤ l(βᵏ)` on the block points is read off the block
weight directly (a block of nonzero weight has nonclosing letters `≥ 2`), rather than through
the holding law `η`; the two are equivalent by the block decomposition of `η`. The atom is
written `((r, ℓ), β)`, the entry point `e = (j(e), l(e))`, and the conclusion `r ∈ 𝒰` is stated
for `r` cast to `ℤ`. The allowances `X_d(ι, v)`, `X_l(ι, v)` and `W(ι, v)` are rational and
enter the margin hypothesis through their casts to `ℝ`; the first-passage conditions
`ℓ - g < X_o(ι)` and `|r - g/4| < g/32` are read off the initial deviation set `𝓘_g(ι)`.

## References

* [Mazur, *Collatz positive density*], §10.5.
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

/-- Block points have nonnegative `j`-coordinate. -/
theorem bkJ_chBlockPoint_nonneg (b : List ℤ × ℤ) : 0 ≤ bkJ (chBlockPoint b) := by
  simp only [bkJ, chBlockPoint_fst]
  positivity

/-- The `j`-coordinate of the fresh path: `j(y^e_u) = j(e) + r + ∑_{k ≤ u} j(βᵏ)`. -/
theorem bkJ_trFreshPath (e : ℤ × ℤ) (r : ℕ) (ℓ : ℤ) (β : List (List ℤ × ℤ)) (u : ℕ) :
    bkJ (trFreshPath e ((r, ℓ), β) u) =
      bkJ e + r + ((β.take u).map fun b => bkJ (chBlockPoint b)).sum := by
  rw [trFreshPath_def, trPath_eq_add_chBlockPath, chBlockPath]
  simp only [bkJ, Prod.fst_add]
  exact congrArg (_ + ·) ((bkJ_list_sum _).trans (congrArg List.sum (List.map_map ..)))

/-- The `l`-coordinate of the fresh path: `l(y^e_u) = l(e) + ℓ + ∑_{k ≤ u} l(βᵏ)`. -/
theorem bkL_trFreshPath (e : ℤ × ℤ) (r : ℕ) (ℓ : ℤ) (β : List (List ℤ × ℤ)) (u : ℕ) :
    bkL (trFreshPath e ((r, ℓ), β) u) =
      bkL e + ℓ + ((β.take u).map fun b => bkL (chBlockPoint b)).sum := by
  rw [trFreshPath_def, trPath_eq_add_chBlockPath, chBlockPath]
  simp only [bkL, Prod.snd_add]
  exact congrArg (_ + ·) ((bkL_list_sum _).trans (congrArg List.sum (List.map_map ..)))

namespace BkTriangle

/-- A point of a triangle lies at or beyond its tip. -/
theorem tip_le_bkL_of_mem {Δ : BkTriangle} {p : ℤ × ℤ} (h : p ∈ Δ) :
    Δ.tip ≤ ((bkL p : ℤ) : ℝ) := by
  have hjz : (0 : ℝ) ≤ ((bkJ p - Δ.j : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.2 (mem_iff.1 h).1
  have := nonneg_of_mul_nonneg_left
    ((mul_nonneg hjz (Real.log_pos (by norm_num : (1 : ℝ) < 9)).le).trans (row_bound_of_mem h))
    (Real.log_pos one_lt_two)
  linarith

/-- A point of a triangle lies within `α (l - tip(Δ))` of its row:
`j - j_Δ ≤ α (l - tip(Δ))`. -/
theorem bkJ_sub_j_le_of_mem {Δ : BkTriangle} {p : ℤ × ℤ} (h : p ∈ Δ) :
    ((bkJ p - Δ.j : ℤ) : ℝ) ≤ alpha * (((bkL p : ℤ) : ℝ) - Δ.tip) := by
  have hlog9 : 0 < Real.log 9 := Real.log_pos (by norm_num)
  rw [alpha_def, show Real.log 2 / Real.log 9 * (((bkL p : ℤ) : ℝ) - Δ.tip) =
    (((bkL p : ℤ) : ℝ) - Δ.tip) * Real.log 2 / Real.log 9 by ring, le_div_iff₀ hlog9]
  exact row_bound_of_mem h

end BkTriangle

/-- **Large triangles sit at anchors**, for `𝔗_{n,ξ,ε}` with `ξ` a unit and `0 < ε < 1/27`. -/
theorem exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional {ι : FIndex} {n : ℕ}
    {ξ : ResidueGroup n} {ε : ℝ} (hξ : IsResidueUnit ξ) (hε : 0 < ε) (hε' : ε < 1 / 27)
    {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ ε) {e : ℤ × ℤ} (he : e ∈ Δ₀) {g v : ℕ}
    (hg : bkL e + g = Δ₀.l) {s : ℝ}
    (hgW : (g : ℝ) / 32 + (Xd ι v : ℝ) + (Xl ι v : ℝ) / 4 + alpha * (totalAllowance ι v : ℝ) + 1 ≤
      g * drift)
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hμ : trFreshLaw n e g a ≠ 0)
    (hbig : a ∈ c3Big n ξ ε e v s) (hex : a ∉ c3Exceptional ι n g v) :
    (a.1.1 : ℤ) ∈ c3AnchorCols ι (bkFamily n ξ ε) e Δ₀ v s := by
  obtain ⟨⟨r, ℓ⟩, β⟩ := a
  obtain ⟨ha, u, huv, Δ', hΔ', hy, hs⟩ := mem_c3Big.1 hbig
  have hdr := abs_drift_lt_of_notMem_c3Exceptional ha hex huv
  rw [notMem_c3Exceptional_iff ha] at hex
  obtain ⟨hex₁, hex₂, -⟩ := hex
  simp only at hex₁ hex₂ hdr
  rw [mem_c3InitEvent, not_or, not_le, not_le] at hex₁
  obtain ⟨hexo, hexr⟩ := hex₁
  rw [trFreshLaw_mk] at hμ
  have hℓ : (g : ℤ) < ℓ := (firstPassageLaw_support (left_ne_zero_of_mul hμ)).2
  have hjl : ∀ b ∈ β, bkJ (chBlockPoint b) ≤ bkL (chBlockPoint b) := fun b hb =>
    c3Near_fst_le_snd (trListWeight_ne_zero_iff.1 (right_ne_zero_of_mul hμ) b hb)
      (trAtoms_closing_mem ha hb)
  have hj0 : ∀ b ∈ β, 0 ≤ bkJ (chBlockPoint b) := fun b _ => bkJ_chBlockPoint_nonneg b
  have hl0 : ∀ b ∈ β, 0 ≤ bkL (chBlockPoint b) := fun b hb => (hj0 b hb).trans (hjl b hb)
  have hyJ := bkJ_trFreshPath e r ℓ β u
  have hyL := bkL_trFreshPath e r ℓ β u
  set H : ℤ := ((β.take u).map fun b => bkJ (chBlockPoint b)).sum
  set V : ℤ := ((β.take u).map fun b => bkL (chBlockPoint b)).sum
  set y := trFreshPath e ((r, ℓ), β) u
  have hH0 : 0 ≤ H := by
    simpa only [List.take_zero, List.map_nil, List.sum_nil] using c3Near_sum_take_le hj0 u.zero_le
  have hV0 : 0 ≤ V := by
    simpa only [List.take_zero, List.map_nil, List.sum_nil] using c3Near_sum_take_le hl0 u.zero_le
  have hVv : ((V : ℤ) : ℝ) ≤ (((β.take v).map fun b => bkL (chBlockPoint b)).sum : ℤ) := by
    exact_mod_cast c3Near_sum_take_le hl0 huv
  -- real-valued facts
  have hH0r : (0 : ℝ) ≤ H := by exact_mod_cast hH0
  have hV0r : (0 : ℝ) ≤ V := by exact_mod_cast hV0
  have hVr : (V : ℝ) < Xl ι v := hVv.trans_lt hex₂
  have hℓr : (g : ℝ) < ℓ := by exact_mod_cast hℓ
  have hor : (ℓ : ℝ) - g < overshootAllowance ι := by exact_mod_cast hexo
  have hrr : |(r : ℝ) - g / 4| < g / 32 := by exact_mod_cast hexr
  have hdr' : |(4 * H - V : ℝ)| < 4 * Xd ι v := by exact_mod_cast hdr
  have hdr₁ := (le_abs_self _).trans_lt hdr'
  have hdr₂ := (neg_lt_neg hdr').trans_le (neg_abs_le _)
  have hgr : ((bkL e : ℤ) : ℝ) + g = Δ₀.l := by exact_mod_cast hg
  have hlr : ((bkL y : ℤ) : ℝ) = (bkL e : ℝ) + ℓ + V := by rw [hyL]; push_cast; ring
  have hjr : ((bkJ y : ℤ) : ℝ) = (bkJ e : ℝ) + r + H := by rw [hyJ]; push_cast; ring
  have hW : (totalAllowance ι v : ℝ) = overshootAllowance ι + Xl ι v := by
    rw [totalAllowance_def, Rat.cast_add, Rat.cast_natCast]
  have hl₁ : Δ₀.l < bkL y := by
    exact_mod_cast (show ((Δ₀.l : ℤ) : ℝ) < ((bkL y : ℤ) : ℝ) by rw [hlr, ← hgr]; linarith)
  have hl₂ : ((bkL y : ℤ) : ℝ) < Δ₀.l + totalAllowance ι v := by rw [hlr, ← hgr, hW]; linarith
  have hj : |((bkJ y : ℤ) : ℝ) - ((bkJ e : ℤ) + (g : ℝ) / 4)| ≤
      (g : ℝ) / 32 + Xd ι v + (Xl ι v : ℝ) / 4 := by
    rw [hjr, show (bkJ e : ℝ) + r + H - ((bkJ e : ℤ) + (g : ℝ) / 4) = ((r : ℝ) - g / 4) + H by
      ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hH0r]
    linarith
  have hne : Δ₀ ≠ Δ' := by
    rintro rfl
    exact (le_l_of_mem hy).not_gt hl₁
  have htip : (Δ₀.l : ℝ) ≤ Δ'.tip :=
    le_tip_of_mem_bkFamily hξ hε hε' hΔ₀ hΔ' hne he hg hy hl₁.le hl₂.le hj hgW
  have htip₂ := tip_le_bkL_of_mem hy
  have hrow := bkJ_sub_j_le_of_mem hy
  have hjy : ((bkJ y - Δ'.j : ℤ) : ℝ) = (bkJ e : ℝ) + r + H - Δ'.j := by rw [Int.cast_sub, hjr]
  have hα : 0 < alpha := alpha_pos
  have hrow' : (bkJ e : ℝ) + r + H - Δ'.j ≤ alpha * ((ℓ - g) + V) := by
    rw [← hjy]
    refine hrow.trans (mul_le_mul_of_nonneg_left ?_ hα.le)
    rw [hlr]
    linarith
  have hdrift : drift = alpha - 1 / 4 := drift_def
  have hd0 : 0 < drift := drift_pos
  refine ⟨Δ'.j, j_mem_bkAnchors hΔ' hs htip (by linarith), r + bkJ e - Δ'.j, ?_, ?_, by ring⟩
  · rw [show (((r : ℤ) + bkJ e - Δ'.j : ℤ) : ℝ) = (r : ℝ) + bkJ e - Δ'.j by push_cast; ring]
    have hjz : (0 : ℝ) ≤ ((bkJ y - Δ'.j : ℤ) : ℝ) := by
      exact_mod_cast sub_nonneg.2 (mem_iff.1 hy).1
    linarith
  · rw [show (((r : ℤ) + bkJ e - Δ'.j : ℤ) : ℝ) = (r : ℝ) + bkJ e - Δ'.j by push_cast; ring]
    have h1 : alpha * ((ℓ : ℝ) - g) ≤ alpha * overshootAllowance ι :=
      mul_le_mul_of_nonneg_left hor.le hα.le
    have h2 : drift * (V : ℝ) ≤ drift * Xl ι v := mul_le_mul_of_nonneg_left hVr.le hd0.le
    have h3 : alpha * ((ℓ - g) + V) = alpha * ((ℓ : ℝ) - g) + drift * V + V / 4 := by
      rw [hdrift]; ring
    linarith

/-- **Outside the deviation event, large triangles sit at anchor columns**. Let `ι ∈ 𝔍`, `ξ` a
unit, `e = (j₀, l₀) ∈ Δ₀ ∈ 𝔗 = 𝔗_{n,ξ,ε_*}`, `g ∈ ℕ` with `l₀ + g = l_{Δ₀}`, `v ∈ ℕ`, `s ∈ ℝ`, and
assume `g/32 + X_d(ι, v) + X_l(ι, v)/4 + λ W(ι, v) + 1 ≤ g λ₀`. If an atom `a = ((r, ℓ), β)` has
`μ_{e,g}(a) ≠ 0`, `a ∈ Big_{e,v,s}` and `a ∉ Dev_{g,v}(ι)`, then `r ∈ 𝒰_{e,Δ₀,v,s}(ι)`. -/
@[collatz_pos_dens "lem_c3_near"]
theorem exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional_epsStar {ι : FIndex} {n : ℕ}
    {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ) {Δ₀ : BkTriangle}
    (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ} (he : e ∈ Δ₀) {g v : ℕ}
    (hg : bkL e + g = Δ₀.l) {s : ℝ}
    (hgW : (g : ℝ) / 32 + (Xd ι v : ℝ) + (Xl ι v : ℝ) / 4 + alpha * (totalAllowance ι v : ℝ) + 1 ≤
      g * drift)
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (hμ : trFreshLaw n e g a ≠ 0)
    (hbig : a ∈ c3Big n ξ epsStar e v s) (hex : a ∉ c3Exceptional ι n g v) :
    (a.1.1 : ℤ) ∈ c3AnchorCols ι (bkFamily n ξ epsStar) e Δ₀ v s :=
  exists_mem_bkAnchors_of_mem_c3Big_of_notMem_c3Exceptional hξ
    epsStar_mem_bkRange.1 epsStar_mem_bkRange.2 hΔ₀ he hg hgW hμ hbig hex

end CollatzPosDens
