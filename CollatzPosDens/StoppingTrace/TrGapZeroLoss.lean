/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.StoppingTrace.TrBridgeLoss
public import CollatzPosDens.StoppingTrace.TrBridgeLossReal
public import CollatzPosDens.StoppingTrace.TrBridgeMassLe
public import CollatzPosDens.StoppingTrace.TrBridgeWhite
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrGainLe
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrGapAdjacent
public import CollatzPosDens.StoppingTrace.TrGuardOut
public import CollatzPosDens.StoppingTrace.TrGuardTheta
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrLossBlack
public import CollatzPosDens.StoppingTrace.TrLossNonneg
public import CollatzPosDens.StoppingTrace.TrLossOutside
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrReward
public import CollatzPosDens.StoppingTrace.TrSupportUpward
public import CollatzPosDens.StoppingTrace.TrTheta
public import CollatzPosDens.StoppingTrace.TrW
public import CollatzPosDens.StoppingTrace.TrWitnessWhite
public import CollatzPosDens.StoppingTrace.TrWordSum

/-!
# The loss of a gap-zero entry

Fix a level `n` and a unit `ξ ∈ G_n`, and take black and white points with respect to
`(n, ξ, ε_*)`. Let `v ∈ 𝒫` be black with `gap(v) = 0`. Then the passage lists `π ∈ Π_0` above
level `0`, weighted by their tilted weight `bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}`, lose at least
```
∑_{π ∈ Π_0} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)} Loss(x_{|π|}(v, π))
  ≥ e^{-γ_*} θ_∘ (3/16 + 6701/26392).
```

Every one-block list `(β)` with `bw(β) ≠ 0` lies in `Π_0`, since a block of nonzero weight climbs
by at least `4`. For it, `N^*(v, (β); 1) = rw(v, β)` and `x_1(v, (β)) = v + bpt(β)`. Group the
blocks `β = (c, e)` by their nonclosing word `c`. For `c = ()` and `e = 4` the endpoint
`v + (1, 4)` is white (an exit witness of `v`, as `gap(v) = 0`), so this block alone contributes
at least `ϖ(4) e^{-γ_*} θ_∘ = (3/16) e^{-γ_*} θ_∘`. For a nonempty word `c` of weight `ω(c)`, the
two blocks `(c, 4)` and `(c, 5)` together contribute at least
`ω(c) (1163/1250)^{t(c)} e^{-γ_*} θ_∘ / 8`, by a case analysis on the endpoints (beyond the strip,
both black, or one white), where `t(c)` is the number of letters `3` of `c`. Summing over the
nonempty words with the weighted word sum gives the factor `∑_{m ≥ 1} (6701/10000)^m = 6701/3299`.

## Main results

* `CollatzPosDens.le_tsum_trPassage_zero_trBridgeLoss`: the lower bound above.

## Implementation notes

The bridge loss takes values in `EReal` and is nonnegative, so the sum of nonnegative terms is
stated in `[0, ∞]`, the loss entering through `EReal.toENNReal` (which is the identity on
nonnegative values), and the real right side through `ENNReal.ofReal`. The set `Π_0` is the
subtype `trPassage 0`. Only the inclusion of the one-block lists into `Π_0` is needed for a lower
bound, so the identification of `Π_0` with these lists is not formalized. The hypothesis `n ≥ 1`
is not needed and is omitted; the black point `v` is taken in `𝒫`.

## References

* [Mazur, *Collatz positive density*], §9.6.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n} {y : ℤ × ℤ}

/-- A one-block list of a live block of `𝔅` is a passage list above level `0`. -/
private lemma singleton_mem_trPassage_zero {β : List ℤ × ℤ} (he : β.2 ∈ ({4, 5} : Set ℤ))
    (hw : chBlockWeight β ≠ 0) : [β] ∈ trPassage 0 := by
  have h4 : 4 ≤ β.2 := by
    rcases he with h | h
    · rw [h]
    · rw [Set.mem_singleton_iff.1 h]
      norm_num
  have hl := four_le_bkL_chBlockPoint_of_chBlockWeight_ne_zero h4 hw
  refine mem_trPassage.2 ⟨fun b hb => ?_, trLive_singleton.2 hw, List.cons_ne_nil _ _,
    fun i hi => ?_, ?_⟩
  · rw [List.mem_singleton.1 hb]
    exact he
  · obtain rfl : i = 0 := by simpa using hi
    simp
  · simp only [List.length_singleton, chBlockPath_cons_succ, chBlockPath_nil, add_zero,
      Nat.cast_zero]
    simp only [bkL] at hl
    omega

private lemma trTheta_le_trBridgeLossReal (hξ : IsResidueUnit ξ) {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (hw : IsBkWhite n ξ (epsStar : ℝ) p) : trTheta ≤ trBridgeLossReal n ξ p := by
  have h := trTheta_le_trBridgeLoss hξ hp hw
  rw [trBridgeLoss_eq_coe_trBridgeLossReal hξ hp] at h
  exact_mod_cast h

/-- The real inequality behind the pairing estimate. -/
private lemma pair_real {μ θ b x L4 L5 : ℝ} {W4 W5 : Prop} [Decidable W4] [Decidable W5]
    (hb0 : 0 ≤ b) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hθ0 : 0 ≤ θ) (hθμ : θ < 8 * μ)
    (hL4 : 0 ≤ L4) (hL5 : 0 ≤ L5)
    (h : (¬W4 ∧ ¬W5 ∧ μ ≤ 3 / 16 * L4 + 1 / 8 * L5) ∨ (W4 ∧ θ ≤ L4) ∨ (W5 ∧ θ ≤ L5)) :
    b * (x * θ / 8) ≤ 3 / 16 * (b * (if W4 then x else 1) * L4) +
      1 / 8 * (b * (if W5 then x else 1) * L5) := by
  have hxθ : x * θ ≤ θ := by nlinarith
  have hbx : 0 ≤ b * x := mul_nonneg hb0 hx0
  have hb4 : 0 ≤ b * L4 := mul_nonneg hb0 hL4
  have hb5 : 0 ≤ b * L5 := mul_nonneg hb0 hL5
  have hbx4 : 0 ≤ b * x * L4 := mul_nonneg hbx hL4
  have hbx5 : 0 ≤ b * x * L5 := mul_nonneg hbx hL5
  rcases h with ⟨h4, h5, hμL⟩ | ⟨hW, hL⟩ | ⟨hW, hL⟩
  · simp only [h4, h5, ↓reduceIte, mul_one]
    have h1 : x * θ / 8 ≤ μ := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hμL hb0, mul_le_mul_of_nonneg_left h1 hb0]
  · have := mul_le_mul_of_nonneg_left hL hbx
    simp only [hW, ↓reduceIte]
    split_ifs <;> nlinarith
  · have := mul_le_mul_of_nonneg_left hL hbx
    simp only [hW, ↓reduceIte]
    split_ifs <;> nlinarith

/-- The pairing estimate: for a nonclosing word `c`, the two blocks `(c, 4)` and `(c, 5)`
together lose at least `e^{-γ_* ι} e^{-γ_*} θ_∘ / 8`. -/
private lemma pair_bound (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints) (c : List ℤ) :
    Real.exp (-(gammaStar : ℝ) * trInnerReward n ξ y c) *
        (Real.exp (-(gammaStar : ℝ)) * trTheta / 8) ≤
      3 / 16 * (Real.exp (-(gammaStar : ℝ) * trReward n ξ y (c, 4)) *
          trBridgeLossReal n ξ (y + chBlockPoint (c, 4))) +
        1 / 8 * (Real.exp (-(gammaStar : ℝ) * trReward n ξ y (c, 5)) *
          trBridgeLossReal n ξ (y + chBlockPoint (c, 5))) := by
  set b := Real.exp (-(gammaStar : ℝ) * trInnerReward n ξ y c) with hb
  have hγ : (0 : ℝ) < gammaStar := by exact_mod_cast gammaStar_pos
  have hρ : ∀ e, Real.exp (-(gammaStar : ℝ) * trReward n ξ y (c, e)) =
      b * (if IsBkWhite n ξ (epsStar : ℝ) (y + chBlockPoint (c, e)) then
        Real.exp (-(gammaStar : ℝ)) else 1) := by
    intro e
    rw [trReward_eq_add_trInnerReward]
    split_ifs
    · rw [hb, ← Real.exp_add]
      congr 1
      ring
    · rw [hb, mul_one]
      congr 1
      ring
  have hmem : ∀ e, y + chBlockPoint (c, e) ∈ bkPoints := by
    intro e
    simp only [mem_bkPoints, bkJ, Prod.fst_add, chBlockPoint_fst] at hy ⊢
    omega
  set y4 := y + chBlockPoint (c, 4) with hy4
  have hy5 : y + chBlockPoint (c, 5) = (bkJ y4, bkL y4 + 1) := by
    refine Prod.ext rfl ?_
    simp only [hy4, chBlockPoint, Prod.snd_add, bkL]
    ring
  have hm5 : (bkJ y4, bkL y4 + 1) ∈ bkPoints := hy5 ▸ hmem 5
  rw [hρ 4, hρ 5]
  refine pair_real (Real.exp_pos _).le (Real.exp_pos _).le
    (Real.exp_le_one_iff.2 (by linarith)) trTheta_nonneg trTheta_lt
    (trBridgeLossReal_nonneg n ξ _) (trBridgeLossReal_nonneg n ξ _) ?_
  rw [← hy4, hy5]
  by_cases hJ : ((n / 2 : ℕ) : ℤ) < bkJ y4
  · have hJ5 : ((n / 2 : ℕ) : ℤ) < bkJ (bkJ y4, bkL y4 + 1) := hJ
    refine Or.inl ⟨fun h => (h.1.trans_lt hJ).false, fun h => (h.1.trans_lt hJ5).false, ?_⟩
    rw [trBridgeLossReal_of_lt_bkJ hJ, trBridgeLossReal_of_lt_bkJ hJ5]
    linarith [sixteen_mul_trMu_lt_five_mul_one_sub_dStar]
  by_cases hW4 : IsBkWhite n ξ (epsStar : ℝ) y4
  · exact Or.inr (Or.inl ⟨hW4, trTheta_le_trBridgeLossReal hξ (hmem 4) hW4⟩)
  by_cases hW5 : IsBkWhite n ξ (epsStar : ℝ) (bkJ y4, bkL y4 + 1)
  · exact Or.inr (Or.inr ⟨hW5, trTheta_le_trBridgeLossReal hξ hm5 hW5⟩)
  simp only [not_lt] at hJ
  have hB4 : BkBlack n ξ (epsStar : ℝ) y4 := ⟨hJ, not_lt.1 fun h => hW4 ⟨hJ, h⟩⟩
  have hB5 : BkBlack n ξ (epsStar : ℝ) (bkJ y4, bkL y4 + 1) :=
    ⟨hJ, not_lt.1 fun h => hW5 ⟨hJ, h⟩⟩
  refine Or.inl ⟨hW4, hW5, ?_⟩
  rw [trBridgeLossReal_of_bkBlack hB4, trBridgeLossReal_of_bkBlack hB5]
  have hgap : trGap n ξ (epsStar : ℝ) y4 =
      trGap n ξ (epsStar : ℝ) (bkJ y4, bkL y4 + 1) + 1 :=
    trGap_eq_trGap_add_one_of_bkBlack_of_bkBlack (j := bkJ y4) (l := bkL y4) hξ
      (by rw [epsStar_cast]; norm_num) (hmem 4) hB4 hB5
  have hW' := trMu_le_trW (k := trGap n ξ (epsStar : ℝ) y4) (by omega)
  rwa [show trGap n ξ (epsStar : ℝ) y4 - 1 = trGap n ξ (epsStar : ℝ) (bkJ y4, bkL y4 + 1) by
    omega] at hW'

/-- The term `bw(β) e^{-γ_* rw(y, β)} Loss(y + bpt(β))` of a one-block passage list. -/
private noncomputable def term (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) (β : List ℤ × ℤ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (chBlockWeight β) *
    ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trReward n ξ y β)) *
      (trBridgeLoss n ξ (y + chBlockPoint β)).toENNReal

private lemma term_eq (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints) (β : List ℤ × ℤ) :
    term n ξ y β = ENNReal.ofReal (chBlockWeight β *
      Real.exp (-(gammaStar : ℝ) * trReward n ξ y β) *
        trBridgeLossReal n ξ (y + chBlockPoint β)) := by
  have hmem : y + chBlockPoint β ∈ bkPoints := by
    simp only [mem_bkPoints, bkJ, Prod.fst_add, chBlockPoint_fst] at hy ⊢
    omega
  rw [term, toENNReal_trBridgeLoss hξ hmem, ← ENNReal.ofReal_mul (chBlockWeight_nonneg β),
    ← ENNReal.ofReal_mul (mul_nonneg (chBlockWeight_nonneg β) (Real.exp_pos _).le)]

open Finset in
/-- The pairing estimate for the word `c = (v₀, …, v_{m-1})`, multiplied by the weight `ω(c)`
and written in `[0, ∞]`. -/
private lemma pair_ennreal (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints) {m : ℕ} (v : Fin m → ℤ) :
    ENNReal.ofReal ((∏ i, varpiIn (v i)) *
        (1163 / 1250 : ℝ) ^ #{i | v i = 3} * (Real.exp (-(gammaStar : ℝ)) * trTheta / 8)) ≤
      term n ξ y (List.ofFn v, 4) + term n ξ y (List.ofFn v, 5) := by
  have hpair := pair_bound (n := n) (ξ := ξ) hξ hy (List.ofFn v)
  have hq := pow_le_exp_neg_trInnerReward (n := n) (ξ := ξ) y v
  have hmem : ∀ e, y + chBlockPoint (List.ofFn v, e) ∈ bkPoints := by
    intro e
    simp only [mem_bkPoints, bkJ, Prod.fst_add, chBlockPoint_fst] at hy ⊢
    omega
  set W := ∏ i, varpiIn (v i) with hW
  have hW0 : 0 ≤ W := Finset.prod_nonneg fun i _ => varpiIn_nonneg _
  rw [term_eq hξ hy, term_eq hξ hy, chBlockWeight_ofFn, chBlockWeight_ofFn, varpi_four,
    varpi_five, ← hW, ← ENNReal.ofReal_add]
  rotate_left
  · exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (trBridgeLossReal_nonneg n ξ _)
  · exact mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le)
      (trBridgeLossReal_nonneg n ξ _)
  refine ENNReal.ofReal_le_ofReal ?_
  set K := Real.exp (-(gammaStar : ℝ)) * trTheta / 8 with hK
  have hK0 : 0 ≤ K := by
    have := trTheta_nonneg
    positivity
  have h1 := mul_le_mul_of_nonneg_left hpair hW0
  have h2 := mul_le_mul_of_nonneg_left hq (mul_nonneg hW0 hK0)
  nlinarith

/-- The empty word: the block `((), 4)` alone loses at least `(3/16) e^{-γ_*} θ_∘`. -/
private lemma empty_bound {v : ℤ × ℤ} (hξ : IsResidueUnit ξ) (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) (hgap : trGap n ξ (epsStar : ℝ) v = 0) :
    ENNReal.ofReal (3 / 16 * (Real.exp (-(gammaStar : ℝ)) * trTheta)) ≤ term n ξ v ([], 4) := by
  have hw : IsBkWhite n ξ (epsStar : ℝ) (v + (1, 4)) := by
    have h := isBkWhite_add_of_bkBlack_trGap (r := 1) (O := 4) hξ hv hb (by norm_num)
      (by rw [hgap]; norm_num) (by norm_num) (by norm_num)
    rwa [hgap, Nat.cast_zero, zero_add] at h
  have hmem : v + (1, 4) ∈ bkPoints := by
    simp only [mem_bkPoints, bkJ, Prod.fst_add] at hv ⊢
    omega
  rw [term_eq hξ hv, chBlockWeight_nil, varpi_four, chBlockPoint_nil, trReward_nil]
  simp only [hw, ↓reduceIte]
  refine ENNReal.ofReal_le_ofReal ?_
  have := trTheta_le_trBridgeLossReal hξ hmem hw
  have : 0 ≤ Real.exp (-(gammaStar : ℝ)) := (Real.exp_pos _).le
  rw [mul_one]
  nlinarith

open Finset in
/-- **The loss of a gap-zero entry.** Let `ξ ∈ G_n` be a unit and let `v ∈ 𝒫` be black with
`gap(v) = 0`. Then
`∑_{π ∈ Π_0} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)} Loss(x_{|π|}(v, π)) ≥
e^{-γ_*} θ_∘ (3/16 + 6701/26392)`. -/
@[collatz_pos_dens "lem_tr_gap_zero_loss"]
theorem le_tsum_trPassage_zero_trBridgeLoss {v : ℤ × ℤ} (hξ : IsResidueUnit ξ)
    (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v)
    (hgap : trGap n ξ (epsStar : ℝ) v = 0) :
    ENNReal.ofReal (Real.exp (-(gammaStar : ℝ)) * trTheta * (3 / 16 + 6701 / 26392)) ≤
      ∑' π : trPassage 0, ENNReal.ofReal (trListWeight π.1) *
        ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length)) *
          (trBridgeLoss n ξ (trPath v π.1 π.1.length)).toENNReal := by
  set K := Real.exp (-(gammaStar : ℝ)) * trTheta / 8 with hK
  have hK0 : 0 ≤ K := by
    have := trTheta_nonneg
    positivity
  -- the one-block lists
  have hA : ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockWeight β ≠ 0},
      term n ξ v β.1 ≤ ∑' π : trPassage 0, ENNReal.ofReal (trListWeight π.1) *
        ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length)) *
          (trBridgeLoss n ξ (trPath v π.1 π.1.length)).toENNReal := by
    refine le_of_eq_of_le ?_ (ENNReal.tsum_comp_le_tsum_of_injective
      (f := fun β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockWeight β ≠ 0} =>
        (⟨[β.1], singleton_mem_trPassage_zero β.2.1 β.2.2⟩ : trPassage 0)) ?_ _)
    · refine tsum_congr fun β => ?_
      simp only [term, List.length_singleton, trListWeight_singleton]
      rw [trCount_cons_succ, trCount_nil, add_zero, trPath_cons_succ, trPath_nil]
    · intro β β' h
      simp only [Subtype.mk.injEq, List.cons.injEq, and_true] at h
      exact Subtype.ext h
  refine le_trans ?_ hA
  rw [tsum_liveBlocks_eq (fun β => term n ξ v β) (fun β h => by simp [term, h]),
    tsum_blocks_eq_tsum_ofFn]
  -- the sum over word lengths
  set f : ℕ → ℝ≥0∞ := fun m => ∑' w : Fin m → ℤ,
    (term n ξ v (List.ofFn w, 4) + term n ξ v (List.ofFn w, 5)) with hf
  have hsplit : ∑' m, f m = f 0 + ∑' m, f (m + 1) := tsum_eq_zero_add' ENNReal.summable
  rw [hsplit]
  have h0 : ENNReal.ofReal (3 / 16 * (Real.exp (-(gammaStar : ℝ)) * trTheta)) ≤ f 0 := by
    refine le_trans (empty_bound hξ hv hb hgap)
      (le_trans (le_self_add (b := term n ξ v ([], 5))) ?_)
    refine le_of_eq_of_le ?_ (ENNReal.le_tsum (default : Fin 0 → ℤ))
    simp [List.ofFn_zero]
  have hgeom : HasSum (fun m : ℕ => (6701 / 10000 : ℝ) ^ (m + 1) * K) (6701 / 3299 * K) := by
    have := ((hasSum_geometric_of_lt_one (r := (6701 / 10000 : ℝ)) (by norm_num)
      (by norm_num)).mul_left (6701 / 10000 : ℝ)).mul_right K
    convert this using 1
    · ext m
      ring
    · norm_num
  have h1 : ENNReal.ofReal (6701 / 3299 * K) ≤ ∑' m, f (m + 1) := by
    rw [← hgeom.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hgeom.summable]
    refine ENNReal.tsum_le_tsum fun m => ?_
    have hm := (hasSum_trWordSum (m + 1)).mul_right K
    rw [← hm.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun w => ?_) hm.summable]
    · exact ENNReal.tsum_le_tsum fun w => pair_ennreal hξ hv w
    refine mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => varpiIn_nonneg _)
      (by positivity)) hK0
  refine le_trans (le_of_eq ?_) (add_le_add h0 h1)
  rw [← ENNReal.ofReal_add (by have := trTheta_nonneg; positivity) (by positivity), hK]
  congr 1
  ring

end CollatzPosDens
