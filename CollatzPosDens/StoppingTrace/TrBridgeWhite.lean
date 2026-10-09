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
public import CollatzPosDens.CharSum.ChBlockListMass
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.StoppingTrace.TrBridgeGain
public import CollatzPosDens.StoppingTrace.TrBridgeLoss
public import CollatzPosDens.StoppingTrace.TrBridgeLossReal
public import CollatzPosDens.StoppingTrace.TrBridgeMass
public import CollatzPosDens.StoppingTrace.TrBridgeMassLe
public import CollatzPosDens.StoppingTrace.TrConcatShift
public import CollatzPosDens.StoppingTrace.TrCountConcat
public import CollatzPosDens.StoppingTrace.TrE8Bound
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrGainLe
public import CollatzPosDens.StoppingTrace.TrGapAdjacent
public import CollatzPosDens.StoppingTrace.TrGuardOut
public import CollatzPosDens.StoppingTrace.TrGuardTheta
public import CollatzPosDens.StoppingTrace.TrGuardWhite
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrLossBlack
public import CollatzPosDens.StoppingTrace.TrLossNonneg
public import CollatzPosDens.StoppingTrace.TrLossOutside
public import CollatzPosDens.StoppingTrace.TrReward
public import CollatzPosDens.StoppingTrace.TrTheta
public import CollatzPosDens.StoppingTrace.TrW
public import CollatzPosDens.StoppingTrace.TrWordSum

/-!
# A white exit loses at least the bridge floor

Fix a level `n` and a unit `ξ ∈ G_n`; "black" and "white" refer to `(n, ξ, ε_*)`. For every
white point `y ∈ 𝒫`, the bridge loss satisfies `Loss(y) ≥ θ_∘`, where
`θ_∘ = (10000/3299) μ_∘` is the white-bridge floor.

Since `y` is not black, every first-stop list `u ∈ 𝒰(y)` is nonempty, and splitting off its
first block `β` identifies `𝒰(y)` with the pairs `(β, u')` of a live block `β ∈ 𝔅` and a
first-stop list `u' ∈ 𝒰(y + bpt(β))`. Along this bijection the list weight and the weighted
white count factor, so that, with `ρ_β = e^{-γ_* rw(y, β)}` and `∑_{β ∈ 𝔅} bw(β) = 1`,
```
Loss(y) = ∑_{β ∈ 𝔅} bw(β) ((1 - d_*) (1 - ρ_β) + ρ_β Loss(y + bpt(β))).
```
Grouping the blocks `β = (c, e)` by their nonclosing word `c`, the two blocks `(c, 4)` and
`(c, 5)` end at vertically adjacent points; a case analysis (beyond the strip, both endpoints
black, or one endpoint white) shows that together they contribute at least
`ω(c) e^{-γ_* ι(c)} μ_∘ ≥ ω(c) (1163/1250)^{t(c)} μ_∘`, where `ω(c)` is the weight of the word,
`t(c)` its number of letters `3` and `ι(c) ≤ κ_* t(c)` the part of the reward collected on
them. Summing over `c` with the weighted word sum gives
`Loss(y) ≥ μ_∘ ∑_{m ≥ 0} (6701/10000)^m = θ_∘`.

## Main results

* `CollatzPosDens.trTheta_le_trBridgeLoss`: `θ_∘ ≤ Loss(y)` for every white point
  `y ∈ 𝒫`, when `ξ` is a unit.

## Implementation notes

The bridge loss takes values in `EReal`, and the inequality is stated there. The computation
is carried out in `[0, ∞]`, where the identity above is used in the subtraction-free form
`(1 - d_*) g_br(y) + θ_∘ ≤ (1 - d_*) + H(y)`: every series is then an unconditional sum of
nonnegative terms, so the regrouping by words and the termwise comparison need no
summability argument. The standing hypothesis `n ≥ 1` of [mazur2026] is not needed and is
omitted; the point `y` is taken in `𝒫`, as are all points in [mazur2026].

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.6.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {y : ℤ × ℤ}

/-- Away from a black base point, a nonempty list is a first-stop list iff its first block is a
live block of `𝔅` and the rest is a first-stop list from the endpoint of that block. -/
private lemma cons_mem_trFirstStopSet_iff (hy : ¬BkBlack n ξ ε y) (β : List ℤ × ℤ)
    (u : List (List ℤ × ℤ)) :
    β :: u ∈ trFirstStopSet n ξ ε y ↔
      (β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockWeight β ≠ 0) ∧
        u ∈ trFirstStopSet n ξ ε (y + chBlockPoint β) := by
  simp only [mem_trFirstStopSet, List.forall_mem_cons, trLive_cons, List.length_cons,
    trPath_cons_succ]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6⟩
    exact ⟨⟨h1, h3⟩, h2, h4, h5, fun t ht => by
      simpa [trPath_cons_succ] using h6 (t + 1) (by omega)⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4, h5, h6⟩
    refine ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, fun t ht => ?_⟩
    cases t with
    | zero => simpa using hy
    | succ t =>
      rw [trPath_cons_succ]
      exact h6 t (by omega)

/-- Splitting off the first block of a first-stop list. -/
private noncomputable def consEquiv (hy : ¬BkBlack n ξ ε y) :
    (Σ β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockWeight β ≠ 0},
      trFirstStopSet n ξ ε (y + chBlockPoint β.1)) ≃ trFirstStopSet n ξ ε y :=
  Equiv.ofBijective
    (fun x => ⟨x.1.1 :: x.2.1, (cons_mem_trFirstStopSet_iff hy _ _).2 ⟨x.1.2, x.2.2⟩⟩)
    ⟨by
      rintro ⟨⟨β, hβ⟩, ⟨u, hu⟩⟩ ⟨⟨β', hβ'⟩, ⟨u', hu'⟩⟩ h
      simp only [Subtype.mk.injEq, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl,
    by
      rintro ⟨u, hu⟩
      cases u with
      | nil => exact absurd (nil_mem_trFirstStopSet_iff.1 hu) hy
      | cons β u =>
        obtain ⟨hβ, hu'⟩ := (cons_mem_trFirstStopSet_iff hy β u).1 hu
        exact ⟨⟨⟨β, hβ⟩, ⟨u, hu'⟩⟩, rfl⟩⟩

private lemma tsum_trFirstStopSet_cons (hy : ¬BkBlack n ξ ε y)
    (f : List (List ℤ × ℤ) → ℝ≥0∞) :
    ∑' u : trFirstStopSet n ξ ε y, f u =
      ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ) ∧ chBlockWeight β ≠ 0},
        ∑' u : trFirstStopSet n ξ ε (y + chBlockPoint β.1), f (β.1 :: u) := by
  rw [← (consEquiv hy).tsum_eq, ENNReal.tsum_sigma']
  rfl

/-- The tilted weight of a list `β :: u` factors through its first block. -/
private lemma tiltedWeight_cons (y : ℤ × ℤ) (β : List ℤ × ℤ) (u : List (List ℤ × ℤ)) :
    ENNReal.ofReal (trListWeight (β :: u)) *
        ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y (β :: u) (β :: u).length)) =
      ENNReal.ofReal (chBlockWeight β) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trReward n ξ y β)) *
        (ENNReal.ofReal (trListWeight u) * ENNReal.ofReal
          (Real.exp (-(gammaStar : ℝ) * trCount n ξ (y + chBlockPoint β) u u.length))) := by
  rw [List.length_cons, trCount_cons_succ, trListWeight_cons, mul_add, Real.exp_add,
    ENNReal.ofReal_mul (chBlockWeight_nonneg β), ENNReal.ofReal_mul (Real.exp_pos _).le]
  ring

/-- The contribution `bw(β) e^{-γ_* rw(y, β)} g_br(y + bpt(β))` of a first block `β` to the
bridge mass at `y`. -/
private noncomputable def massTerm (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) (β : List ℤ × ℤ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (chBlockWeight β) *
    ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trReward n ξ y β)) *
      trBridgeMass n ξ (y + chBlockPoint β)

/-- The contribution `bw(β) e^{-γ_* rw(y, β)} H(y + bpt(β))` of a first block `β` to the
bridge gain at `y`. -/
private noncomputable def gainTerm (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) (β : List ℤ × ℤ) :
    ℝ≥0∞ :=
  ENNReal.ofReal (chBlockWeight β) *
    ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trReward n ξ y β)) *
      trBridgeGain n ξ (y + chBlockPoint β)

/-- First-block decomposition of the bridge mass at a point that is not black. -/
private lemma trBridgeMass_eq_tsum_block (hy : ¬BkBlack n ξ (epsStar : ℝ) y) :
    trBridgeMass n ξ y = ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}, massTerm n ξ y β := by
  rw [trBridgeMass_def]
  refine (tsum_trFirstStopSet_cons hy (fun b => ENNReal.ofReal (trListWeight b) *
    ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b b.length)))).trans ?_
  refine Eq.trans ?_ (tsum_liveBlocks_eq (massTerm n ξ y) (fun β h => by simp [massTerm, h]))
  refine tsum_congr fun β => ?_
  rw [massTerm, trBridgeMass_def, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun u => tiltedWeight_cons y β.1 u.1

/-- First-block decomposition of the bridge gain at a point that is not black. -/
private lemma trBridgeGain_eq_tsum_block (hy : ¬BkBlack n ξ (epsStar : ℝ) y) :
    trBridgeGain n ξ y = ∑' β : {β : List ℤ × ℤ // β.2 ∈ ({4, 5} : Set ℤ)}, gainTerm n ξ y β := by
  rw [trBridgeGain_def]
  refine (tsum_trFirstStopSet_cons hy (fun b => ENNReal.ofReal (trListWeight b) *
    ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b b.length)) *
      ENNReal.ofReal
        (max (trDelta (trGap n ξ (epsStar : ℝ) (trPath y b b.length))) 0))).trans ?_
  refine Eq.trans ?_ (tsum_liveBlocks_eq (gainTerm n ξ y) (fun β h => by simp [gainTerm, h]))
  refine tsum_congr fun β => ?_
  rw [gainTerm, trBridgeGain_def, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun u => ?_
  rw [tiltedWeight_cons y β.1 u.1, List.length_cons, trPath_cons_succ]
  ring

/-- The real inequality behind the pairing estimate. -/
private lemma pair_real {d μ b x L4 L5 : ℝ} {W4 W5 : Prop} [Decidable W4] [Decidable W5]
    (hd : d < 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hL4 : 0 ≤ L4) (hL5 : 0 ≤ L5)
    (h : (¬W4 ∧ ¬W5 ∧ μ ≤ 3 / 16 * L4 + 1 / 8 * L5) ∨
      ((W4 ∨ W5) ∧ 8 * μ ≤ (1 - d) * (1 - x))) :
    b * μ ≤ 3 / 16 * ((1 - d) * (1 - b * (if W4 then x else 1)) +
        b * (if W4 then x else 1) * L4) +
      1 / 8 * ((1 - d) * (1 - b * (if W5 then x else 1)) + b * (if W5 then x else 1) * L5) := by
  have h1 : 0 ≤ (1 - b) * (1 - d) := mul_nonneg (by linarith) (by linarith)
  have hbx : 0 ≤ b * x := mul_nonneg hb0 hx0
  have hbx1 : b * x ≤ 1 := by nlinarith
  have hbx4 : 0 ≤ b * x * L4 := mul_nonneg hbx hL4
  have hbx5 : 0 ≤ b * x * L5 := mul_nonneg hbx hL5
  have hb4 : 0 ≤ b * L4 := mul_nonneg hb0 hL4
  have hb5 : 0 ≤ b * L5 := mul_nonneg hb0 hL5
  have hbxd : 0 ≤ (1 - b * x) * (1 - d) := mul_nonneg (by linarith) (by linarith)
  rcases h with ⟨h4, h5, hμL⟩ | ⟨hW, hx⟩
  · simp only [h4, h5, ↓reduceIte, mul_one]
    nlinarith [mul_le_mul_of_nonneg_left hμL hb0]
  · have h8 := mul_le_mul_of_nonneg_left hx hb0
    rcases hW with hW | hW <;> split_ifs <;> nlinarith

/-- Appending a block keeps a point inside `𝒫`. -/
private lemma add_chBlockPoint_mem_bkPoints (hy : y ∈ bkPoints) (c : List ℤ) (e : ℤ) :
    y + chBlockPoint (c, e) ∈ bkPoints := by
  simp only [mem_bkPoints, bkJ, Prod.fst_add, chBlockPoint_fst] at hy ⊢
  omega

/-- The pairing estimate: for a nonclosing word `c`, the two blocks `(c, 4)` and `(c, 5)` together
lose at least `e^{-γ_* ι} μ_∘`. -/
private lemma pair_bound (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints) (c : List ℤ) :
    Real.exp (-(gammaStar : ℝ) * trInnerReward n ξ y c) * trMu ≤
      varpi 4 * ((1 - (dStar : ℝ)) * (1 - Real.exp (-(gammaStar : ℝ) * trReward n ξ y (c, 4))) +
        Real.exp (-(gammaStar : ℝ) * trReward n ξ y (c, 4)) *
          trBridgeLossReal n ξ (y + chBlockPoint (c, 4))) +
      varpi 5 * ((1 - (dStar : ℝ)) * (1 - Real.exp (-(gammaStar : ℝ) * trReward n ξ y (c, 5))) +
        Real.exp (-(gammaStar : ℝ) * trReward n ξ y (c, 5)) *
          trBridgeLossReal n ξ (y + chBlockPoint (c, 5))) := by
  set b := Real.exp (-(gammaStar : ℝ) * trInnerReward n ξ y c) with hb
  have hd : (dStar : ℝ) < 1 := by exact_mod_cast dStar_lt_one
  have hγ : (0 : ℝ) < gammaStar := by exact_mod_cast gammaStar_pos
  have hb1 : b ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [trInnerReward_nonneg (n := n) (ξ := ξ) y c])
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
  set y4 := y + chBlockPoint (c, 4) with hy4
  have hy5 : y + chBlockPoint (c, 5) = (bkJ y4, bkL y4 + 1) := by
    refine Prod.ext rfl ?_
    simp only [hy4, chBlockPoint, Prod.snd_add, bkL]
    ring
  rw [hρ 4, hρ 5, varpi_four, varpi_five]
  refine pair_real hd (Real.exp_pos _).le hb1 (Real.exp_pos _).le
    (Real.exp_le_one_iff.2 (by linarith)) (trBridgeLossReal_nonneg n ξ _)
    (trBridgeLossReal_nonneg n ξ _) ?_
  rw [← hy4, hy5]
  by_cases hJ : ((n / 2 : ℕ) : ℤ) < bkJ y4
  · have hJ5 : ((n / 2 : ℕ) : ℤ) < bkJ (bkJ y4, bkL y4 + 1) := hJ
    refine Or.inl ⟨fun h => (h.bkJ_le.trans_lt hJ).false, fun h => (h.bkJ_le.trans_lt hJ5).false,
      ?_⟩
    rw [trBridgeLossReal_of_lt_bkJ hJ, trBridgeLossReal_of_lt_bkJ hJ5]
    linarith [sixteen_mul_trMu_lt_five_mul_one_sub_dStar]
  by_cases hW : IsBkWhite n ξ (epsStar : ℝ) y4 ∨
      IsBkWhite n ξ (epsStar : ℝ) (bkJ y4, bkL y4 + 1)
  · refine Or.inr ⟨hW, ?_⟩
    nlinarith [eight_mul_trMu_lt_one_sub_dStar_mul_E8, E8_lt_one_sub_exp_neg hγ]
  · simp only [not_or, not_lt] at hJ hW
    obtain ⟨hW4, hW5⟩ := hW
    have hB4 : BkBlack n ξ (epsStar : ℝ) y4 :=
      ⟨hJ, not_lt.1 fun h => hW4 ⟨hJ, h⟩⟩
    have hB5 : BkBlack n ξ (epsStar : ℝ) (bkJ y4, bkL y4 + 1) :=
      ⟨hJ, not_lt.1 fun h => hW5 ⟨hJ, h⟩⟩
    refine Or.inl ⟨hW4, hW5, ?_⟩
    rw [trBridgeLossReal_of_bkBlack hB4, trBridgeLossReal_of_bkBlack hB5]
    have hgap : trGap n ξ (epsStar : ℝ) y4 =
        trGap n ξ (epsStar : ℝ) (bkJ y4, bkL y4 + 1) + 1 :=
      trGap_eq_trGap_add_one_of_bkBlack_of_bkBlack (j := bkJ y4) (l := bkL y4) hξ
        (by rw [epsStar_cast]; norm_num) (add_chBlockPoint_mem_bkPoints hy c 4) hB4 hB5
    have hW' := trMu_le_trW (k := trGap n ξ (epsStar : ℝ) y4) (by omega)
    rwa [show trGap n ξ (epsStar : ℝ) y4 - 1 = trGap n ξ (epsStar : ℝ) (bkJ y4, bkL y4 + 1) by
      omega] at hW'

open Finset in
/-- The pairing estimate `pair_bound` for the word `c = (v₀, …, v_{m-1})`, multiplied by the weight
`ω(c)` and written in `[0, ∞]`. -/
private lemma pair_ennreal (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints) {m : ℕ} (v : Fin m → ℤ) :
    ENNReal.ofReal (1 - (dStar : ℝ)) *
        (massTerm n ξ y (List.ofFn v, 4) + massTerm n ξ y (List.ofFn v, 5)) +
        ENNReal.ofReal ((∏ i, varpiIn (v i)) *
          (1163 / 1250 : ℝ) ^ #{i | v i = 3} * trMu) ≤
      (ENNReal.ofReal (1 - (dStar : ℝ)) * ENNReal.ofReal (chBlockWeight (List.ofFn v, 4)) +
          ENNReal.ofReal (1 - (dStar : ℝ)) * ENNReal.ofReal (chBlockWeight (List.ofFn v, 5))) +
        (gainTerm n ξ y (List.ofFn v, 4) + gainTerm n ξ y (List.ofFn v, 5)) := by
  have hpair := pair_bound (n := n) (ξ := ξ) hξ hy (List.ofFn v)
  have hq := pow_le_exp_neg_trInnerReward (n := n) (ξ := ξ) y v
  have hw4 := chBlockWeight_ofFn v 4
  have hw5 := chBlockWeight_ofFn v 5
  set c := List.ofFn v with hc
  set W := ∏ i, varpiIn (v i) with hW
  have hW0 : 0 ≤ W := Finset.prod_nonneg fun i _ => varpiIn_nonneg _
  have hd : (dStar : ℝ) < 1 := by exact_mod_cast dStar_lt_one
  have hμ := trMu_nonneg
  simp only [trBridgeLossReal] at hpair
  simp only [massTerm, gainTerm]
  rw [← ENNReal.ofReal_toReal (trBridgeMass_ne_top n ξ (y + chBlockPoint (c, 4))),
    ← ENNReal.ofReal_toReal (trBridgeMass_ne_top n ξ (y + chBlockPoint (c, 5))),
    ← ENNReal.ofReal_toReal (trBridgeGain_ne_top hξ (add_chBlockPoint_mem_bkPoints hy c 4)),
    ← ENNReal.ofReal_toReal (trBridgeGain_ne_top hξ (add_chBlockPoint_mem_bkPoints hy c 5))]
  set M4 := (trBridgeMass n ξ (y + chBlockPoint (c, 4))).toReal
  set M5 := (trBridgeMass n ξ (y + chBlockPoint (c, 5))).toReal
  set G4 := (trBridgeGain n ξ (y + chBlockPoint (c, 4))).toReal
  set G5 := (trBridgeGain n ξ (y + chBlockPoint (c, 5))).toReal
  set ρ4 := Real.exp (-(gammaStar : ℝ) * trReward n ξ y (c, 4))
  set ρ5 := Real.exp (-(gammaStar : ℝ) * trReward n ξ y (c, 5))
  set w4 := chBlockWeight (c, 4)
  set w5 := chBlockWeight (c, 5)
  set q := (1163 / 1250 : ℝ) ^ #{i | v i = 3}
  have ha : 0 ≤ 1 - (dStar : ℝ) := by linarith
  have hM4 : 0 ≤ M4 := ENNReal.toReal_nonneg
  have hM5 : 0 ≤ M5 := ENNReal.toReal_nonneg
  have hG4 : 0 ≤ G4 := ENNReal.toReal_nonneg
  have hG5 : 0 ≤ G5 := ENNReal.toReal_nonneg
  have hρ4 : 0 ≤ ρ4 := (Real.exp_pos _).le
  have hρ5 : 0 ≤ ρ5 := (Real.exp_pos _).le
  have hw40 : 0 ≤ w4 := chBlockWeight_nonneg _
  have hw50 : 0 ≤ w5 := chBlockWeight_nonneg _
  have hq0 : 0 ≤ q := by positivity
  have key : (1 - (dStar : ℝ)) * (w4 * ρ4 * M4 + w5 * ρ5 * M5) + W * q * trMu ≤
      (1 - (dStar : ℝ)) * w4 + (1 - (dStar : ℝ)) * w5 + (w4 * ρ4 * G4 + w5 * ρ5 * G5) := by
    rw [hw4, hw5]
    nlinarith [mul_le_mul_of_nonneg_left hpair hW0,
      mul_le_mul_of_nonneg_left hq (mul_nonneg hW0 hμ)]
  have h1 : 0 ≤ w4 * ρ4 := mul_nonneg hw40 hρ4
  have h2 : 0 ≤ w5 * ρ5 := mul_nonneg hw50 hρ5
  refine le_of_eq_of_le ?_ (le_of_le_of_eq (ENNReal.ofReal_le_ofReal key) ?_)
  · rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul h1,
      ENNReal.ofReal_mul hw40, ENNReal.ofReal_mul h2, ENNReal.ofReal_mul hw50]
  · rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul ha, ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul h1, ENNReal.ofReal_mul hw40, ENNReal.ofReal_mul h2,
      ENNReal.ofReal_mul hw50]

open Finset in
/-- The bridge floor `θ_∘` as a sum over words `c = (v₀, …, v_{m-1})`. -/
lemma ofReal_trTheta_eq_tsum_ofFn : ENNReal.ofReal trTheta = ∑' m : ℕ, ∑' v : Fin m → ℤ,
    ENNReal.ofReal ((∏ i, varpiIn (v i)) * (1163 / 1250 : ℝ) ^ #{i | v i = 3} * trMu) := by
  have hgeom : HasSum (fun m : ℕ => (6701 / 10000 : ℝ) ^ m * trMu) trTheta := by
    rw [trTheta_def]
    convert (hasSum_geometric_of_lt_one (r := (6701 / 10000 : ℝ)) (by norm_num)
      (by norm_num)).mul_right trMu using 1
    norm_num
  have hμ := trMu_nonneg
  rw [← hgeom.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hgeom.summable]
  refine tsum_congr fun m => ?_
  have hm := (hasSum_trWordSum m).mul_right trMu
  rw [← hm.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun v => ?_) hm.summable]
  exact mul_nonneg (mul_nonneg (prod_nonneg fun i _ => varpiIn_nonneg _) (by positivity)) hμ

/-- The constant `1 - d_*` as a sum over the nonclosing words of the blocks ending in `4, 5`. -/
lemma ofReal_one_sub_dStar_eq_tsum_ofFn : ENNReal.ofReal (1 - (dStar : ℝ)) =
    ∑' m : ℕ, ∑' v : Fin m → ℤ,
      (ENNReal.ofReal (1 - (dStar : ℝ)) * ENNReal.ofReal (chBlockWeight (List.ofFn v, 4)) +
        ENNReal.ofReal (1 - (dStar : ℝ)) * ENNReal.ofReal (chBlockWeight (List.ofFn v, 5))) := by
  rw [← tsum_blocks_eq_tsum_ofFn
      (fun β => ENNReal.ofReal (1 - (dStar : ℝ)) * ENNReal.ofReal (chBlockWeight β)),
    ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun β => chBlockWeight_nonneg _)
      hasSum_prod_chBlockWeight_single.summable,
    hasSum_prod_chBlockWeight_single.tsum_eq, ENNReal.ofReal_one, mul_one]

/-- **A white exit loses at least the bridge floor.** Let `ξ ∈ G_n` be a unit. For every white
point `y ∈ 𝒫`, `Loss(y) ≥ θ_∘`. -/
@[collatz_pos_dens "lem_tr_bridge_white"]
theorem trTheta_le_trBridgeLoss (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints)
    (hw : IsBkWhite n ξ (epsStar : ℝ) y) : (trTheta : EReal) ≤ trBridgeLoss n ξ y := by
  have hnb : ¬BkBlack n ξ (epsStar : ℝ) y := fun h => (h.2.trans_lt hw.2).false
  have hd : (dStar : ℝ) < 1 := by exact_mod_cast dStar_lt_one
  have A : ENNReal.ofReal (1 - (dStar : ℝ)) * trBridgeMass n ξ y + ENNReal.ofReal trTheta ≤
      ENNReal.ofReal (1 - (dStar : ℝ)) + trBridgeGain n ξ y := by
    rw [trBridgeMass_eq_tsum_block hnb, trBridgeGain_eq_tsum_block hnb, tsum_blocks_eq_tsum_ofFn,
      tsum_blocks_eq_tsum_ofFn, ofReal_trTheta_eq_tsum_ofFn]
    conv_rhs => rw [ofReal_one_sub_dStar_eq_tsum_ofFn]
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun m => ?_
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun v => pair_ennreal hξ hy v
  rw [trBridgeLoss_eq_coe_trBridgeLossReal hξ hy, EReal.coe_le_coe_iff, trBridgeLossReal]
  have hm := trBridgeMass_ne_top n ξ y
  have hg := trBridgeGain_ne_top hξ hy
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hg⟩) A
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.ofReal_ne_top hg, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal trTheta_nonneg] at h
  linarith

end CollatzPosDens
