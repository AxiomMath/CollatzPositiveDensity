/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.S02Gamma
public import CollatzPosDens.Transfer.S02Z
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.BlackSet.BkCanonTriangle
public import CollatzPosDens.BlackSet.BkExitWidth
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.CharSum.ChOddDyadicExit
public import CollatzPosDens.CharSum.ChOddDyadicExitStrip
public import CollatzPosDens.CharSum.ChPaidRewardCap
public import CollatzPosDens.CharSum.ChPaidRewardNonneg
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrGapNonneg
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrPassage
public import CollatzPosDens.StoppingTrace.TrCapFactor
public import CollatzPosDens.StoppingTrace.TrRaw3Cap
public import CollatzPosDens.StoppingTrace.TrRaw3Witness
public import CollatzPosDens.StoppingTrace.TrRepCoeff
public import CollatzPosDens.StoppingTrace.TrDirectCrossing
public import CollatzPosDens.StoppingTrace.TrPacketRange
public import CollatzPosDens.StoppingTrace.TrPhi2Small
public import CollatzPosDens.StoppingTrace.TrGapOneCells
public import CollatzPosDens.StoppingTrace.TrCrossingReward
public import CollatzPosDens.StoppingTrace.TrExitReward
public import CollatzPosDens.StoppingTrace.TrPassageDeficit

/-!
# One passage from a black point

Fix a level `n` and a unit `ξ ∈ G_n`, and let "white" and "black" refer to the colour scale
`ε_*`. Let `v ∈ 𝒫` be black and `s = gap(v)`. Then the tilted mass of one passage of the block
path above level `s`, started from `v`, is at most `1 - D_cr(s)`:
```
∑_{π ∈ Π_s} bw^⊗(π) exp(-γ_* N^*(v, π; |π|)) ≤ 1 - D_cr(s).
```

The gap is a natural number. Let `I` be the set of triples `(c, o, r)` with `3 ≤ c ≤ 16`,
`1 ≤ o ≤ c` and `1 ≤ r ≤ f_s`. On the first raw crossing event `𝒳_{c,o,r}(s)` the count
`N^*(v, π; |π|)` is at least the paid reward `R_c(y)` at the exit point `y = v + (r, s + o)`,
and `γ_* = z_* > 0`, so it suffices to show `e^{-z_* R_c(y)} ≤ 1 - δ^{rep}_{s,c,o}`.

* Off the exceptional cases `exp_neg_zStar_mul_chPaidReward_le_one_sub_trPacketDeficit` gives
  `e^{-z_* R_c(y)} ≤ 1 - δ^{pk}_{c,o} = 1 - δ^{rep}_{s,c,o}`.
* At an exit point the angle is an odd dyadic point up to a small error:
  `ϑ(y) = (b + β) / 2^o` with `b` odd and `|β| ≤ 9^{f_s} ε_* 2^{-s}`, and
  `exp_neg_zStar_mul_chPaidReward_le` gives `e^{-z_* R_c(y)} ≤ Φ^cap_c(ϑ(y))`.
* For `(c, o) = (3, 1)`, `Φ_2((b + β)/2) ≤ (11/7)|β|`, so `e^{-z_* R_3(y)} ≤ ς_s`; together with
  the bound `e^{-z_* R_3(y)} ≤ 1 - δ^{pk}_{3,1}` this is
  `e^{-z_* R_3(y)} ≤ min {1 - δ^{pk}_{3,1}, ς_s} = 1 - δ^{rep}_{s,3,1}`.
* For `(c, o) = (4, 1)` and `s ∈ {12, 19}`, `|β| < 1/12`, resp. `|β| < 1/24`, and
  `chPacketFn_gap_one_cells` gives `Φ^cap_4(ϑ(y)) < 21/50`, resp. `< 9/25`.

Then `tsum_trPassage_mul_exp_neg_trCount_le_one_sub` bounds the passage series by
`1 - ∑_{(c,o,r) ∈ I} δ^{rep}_{s,c,o} ϖ(c) 𝖱(r - 1, s + o - c) = 1 - D_cr(s)`.

## Main results

* `CollatzPosDens.summable_trPassage_mul_exp_neg_trCount`: the series converges.
* `CollatzPosDens.exp_neg_zStar_mul_chPaidReward_le_one_sub_trRepCoeff`: the reward at an exit
  point is at least the replaced crossing coefficient,
  `e^{-z_* R_c(v + (r, s + o))} ≤ 1 - δ^{rep}_{s,c,o}`.
* `CollatzPosDens.tsum_trPassage_mul_exp_neg_trCount_le`: the one-passage bound.

## Implementation notes

The sum over `Π_s` is the real `tsum` over the subtype `trPassage s`; its summability is proved
separately, so the bound is not an artefact of the junk value of a divergent `tsum`. The gap is
an integer-valued function; the level of the passage is its natural-number value
`gap(v).toNat`, which equals `gap(v)` because the gap is nonnegative. The point `v` is taken in
`𝒫` (`v ∈ bkPoints`).

## References

* [Mazur, *Collatz positive density*], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The tilted passage series `∑_{π ∈ Π_s} bw^⊗(π) e^{-γ_* N^*(v, π; |π|)}` converges, for any
base point `v` and level `s`. -/
theorem summable_trPassage_mul_exp_neg_trCount {n : ℕ} (ξ : ResidueGroup n) (v : ℤ × ℤ)
    (s : ℕ) :
    Summable fun π : trPassage s ↦
      trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) := by
  have hγ : (0 : ℝ) < gammaStar := by exact_mod_cast gammaStar_pos
  refine (hasSum_trListWeight_trPassage s).summable.of_nonneg_of_le
    (fun π ↦ mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le) fun π ↦ ?_
  refine mul_le_of_le_one_right (trListWeight_nonneg _) (Real.exp_le_one_iff.mpr ?_)
  nlinarith [trCount_nonneg (n := n) (ξ := ξ) v π.1 π.1.length]

/-- At an exit point `y = v + (r, s + o)` of a black point `v` of gap `s`, with `r ≤ f_s`, the
angle is `ϑ(y) = (b + β) / 2^o` with `b` odd and `|β| ≤ 9^{f_s} ε_* 2^{-s}`, and
`e^{-z_* R_c(y)} ≤ Φ^cap_c(ϑ(y))` for `3 ≤ c ≤ 16`. -/
private theorem exists_exp_neg_zStar_mul_chPaidReward_le_trCapFactor {n : ℕ}
    {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) {r : ℕ}
    (hr : r ≤ bkExitWidth (trGap n ξ (epsStar : ℝ) v).toNat) {c o : ℕ}
    (hc₁ : 3 ≤ c) (hc₂ : c ≤ 16) (ho : 1 ≤ o) :
    ∃ b : ℤ, Odd b ∧ ∃ β : ℝ,
      |β| ≤ 9 ^ bkExitWidth (trGap n ξ (epsStar : ℝ) v).toNat * (epsStar : ℝ) *
        (2 : ℝ) ^ (-((trGap n ξ (epsStar : ℝ) v).toNat : ℤ)) ∧
      Real.exp (-(zStar : ℝ) * chPaidReward n ξ (epsStar : ℝ) c
        (v + ((r : ℤ), trGap n ξ (epsStar : ℝ) v + o))) ≤ trCapFactor c ((b + β) / 2 ^ o) := by
  obtain ⟨hε₀, hε⟩ := epsStar_mem_bkRange (K := ℝ)
  set s := (trGap n ξ (epsStar : ℝ) v).toNat with hs_def
  have hs : (s : ℤ) = trGap n ξ (epsStar : ℝ) v := Int.toNat_of_nonneg (trGap_nonneg ..)
  have hω : bkL v + s = (bkCanonTriangle n ξ (epsStar : ℝ) v hv).l := by
    rw [bkCanonTriangle_l, bkColTop_eq_add_trGap, hs]
  have hy : v + ((r : ℤ), trGap n ξ (epsStar : ℝ) v + o) =
      (bkJ v + r, (bkCanonTriangle n ξ (epsStar : ℝ) v hv).l + o) := by
    rw [← hω, ← hs]
    ext
    · simp [bkJ]
    · simp [bkL]; ring
  rw [hy]
  have hJ := bkJ_add_le_of_le_bkExitWidth hξ hε₀ hε hv hb hω hr
  obtain ⟨b, hbodd, β, hβ, hθ⟩ := exists_odd_bkTheta_dyadic_exit hξ hε₀ hε hv hb s hω r o ho
  refine ⟨b, hbodd, β, hβ.trans ?_, ?_⟩
  · have h9 : (9 : ℝ) ^ r ≤ 9 ^ bkExitWidth s := pow_le_pow_right₀ (by norm_num) hr
    have hpos : (0 : ℝ) ≤ (epsStar : ℝ) * (2 : ℝ) ^ (-(s : ℤ)) := by positivity
    nlinarith
  · have hcap := exp_neg_zStar_mul_chPaidReward_le (n := n) (ξ := ξ) (ε := (epsStar : ℝ))
      (c := (c : ℤ)) (p := (bkJ v + r, (bkCanonTriangle n ξ (epsStar : ℝ) v hv).l + o))
      (by exact_mod_cast hc₁) (by exact_mod_cast hc₂) hJ
    rwa [chRawFactor_of_two_le n ξ (by omega), hθ,
      ← trCapFactor_of_mem (by exact_mod_cast hc₁) (by exact_mod_cast hc₂)] at hcap

/-- **The reward at an exit point, with the replaced coefficient.** Let `ξ ∈ G_n` be a unit,
`v ∈ 𝒫` black and `s = gap(v)`. For `1 ≤ r ≤ f_s`, `3 ≤ c ≤ 16` and `o ≥ 1`,
`e^{-z_* R_c(v + (r, s + o))} ≤ 1 - δ^{rep}_{s,c,o}`. -/
theorem exp_neg_zStar_mul_chPaidReward_le_one_sub_trRepCoeff {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v)
    {r : ℕ} (hr : r ≤ bkExitWidth (trGap n ξ (epsStar : ℝ) v).toNat) {c o : ℕ}
    (hc₁ : 3 ≤ c) (hc₂ : c ≤ 16) (ho : 1 ≤ o) :
    Real.exp (-(zStar : ℝ) * chPaidReward n ξ (epsStar : ℝ) c
        (v + ((r : ℤ), trGap n ξ (epsStar : ℝ) v + o))) ≤
      1 - (trRepCoeff (trGap n ξ (epsStar : ℝ) v).toNat c o : ℝ) := by
  have hpk := exp_neg_zStar_mul_chPaidReward_le_one_sub_trPacketDeficit hξ hv hb hr hc₁ hc₂ ho
  obtain ⟨b, hbodd, β, hβ, hcap⟩ :=
    exists_exp_neg_zStar_mul_chPaidReward_le_trCapFactor hξ hv hb hr hc₁ hc₂ ho
  have hz : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
  have hE1 : Real.exp (-(zStar : ℝ) * chPaidReward n ξ (epsStar : ℝ) c
      (v + ((r : ℤ), trGap n ξ (epsStar : ℝ) v + o))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hz.le (zero_le_chPaidReward n ξ
      (epsStar : ℝ) c (v + ((r : ℤ), trGap n ξ (epsStar : ℝ) v + o)))])
  generalize Real.exp (-(zStar : ℝ) * chPaidReward n ξ (epsStar : ℝ) c
    (v + ((r : ℤ), trGap n ξ (epsStar : ℝ) v + o))) = E at hpk hcap hE1 ⊢
  generalize (trGap n ξ (epsStar : ℝ) v).toNat = s at hβ ⊢
  by_cases h₃ : c = 3 ∧ o = 1
  · obtain ⟨rfl, rfl⟩ := h₃
    rw [trRepCoeff_three_one, Rat.cast_max, Rat.cast_sub, Rat.cast_one, le_sub_comm]
    refine max_le (by linarith) ?_
    suffices hς : E ≤ (trRaw3Cap s : ℝ) by linarith
    rw [trRaw3Cap_def]
    push_cast
    refine le_min hE1 (hcap.trans ?_)
    rw [trCapFactor_of_mem (by norm_num) (by norm_num), max_comm]
    refine max_le_max le_rfl ?_
    rw [show (((3 : ℕ) : ℤ) - 1).toNat = 2 from rfl, pow_one]
    refine (chPacketFn_two_odd_add_div_two_le hbodd β).trans ?_
    linarith
  by_cases h₄ : c = 4 ∧ o = 1 ∧ (s = 12 ∨ s = 19)
  · obtain ⟨rfl, rfl, rfl | rfl⟩ := h₄
    · rw [trRepCoeff_four_one_twelve]
      have hβ' : |β| ≤ 1 / 12 := hβ.trans (by norm_num [bkExitWidth, epsStar_cast])
      have h := chPacketFn_gap_one_cells (4, 1, 1 / 12, 21 / 50) (by simp) b hbodd β hβ'
      push_cast at hcap h ⊢
      linarith
    · rw [trRepCoeff_four_one_nineteen]
      have hβ' : |β| ≤ 1 / 24 := hβ.trans (by norm_num [bkExitWidth, epsStar_cast])
      have h := chPacketFn_gap_one_cells (4, 1, 1 / 24, 9 / 25) (by simp) b hbodd β hβ'
      push_cast at hcap h ⊢
      linarith
  · rw [trRepCoeff_of_ne h₃ h₄]
    exact hpk

/-- **One passage from a black point.** Let `ξ ∈ G_n` be a unit, `v ∈ 𝒫` black (at the colour
scale `ε_*`) and `s = gap(v)`. Then
`∑_{π ∈ Π_s} bw^⊗(π) exp(-γ_* N^*(v, π; |π|)) ≤ 1 - D_cr(s)`. -/
@[collatz_pos_dens "lem_tr_passage_bound"]
theorem tsum_trPassage_mul_exp_neg_trCount_le {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v) :
    ∑' π : trPassage (trGap n ξ (epsStar : ℝ) v).toNat,
        trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) ≤
      1 - trDirectCrossing (trGap n ξ (epsStar : ℝ) v).toNat := by
  set s := (trGap n ξ (epsStar : ℝ) v).toNat with hs_def
  have hs : (s : ℤ) = trGap n ξ (epsStar : ℝ) v := Int.toNat_of_nonneg (trGap_nonneg ..)
  set J : Finset (Σ _ : ℕ, ℕ × ℕ) :=
    (Icc 3 16).sigma fun c ↦ Icc 1 c ×ˢ Icc 1 (bkExitWidth s) with hJ
  set e : (Σ _ : ℕ, ℕ × ℕ) → ℤ × ℤ × ℕ := fun t ↦ ((t.1 : ℤ), (t.2.1 : ℤ), t.2.2) with he
  have hinj : Set.InjOn e J := by
    rintro ⟨c, o, r⟩ - ⟨c', o', r'⟩ - h
    simp only [he, Prod.mk.injEq, Nat.cast_inj] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  have hmemJ : ∀ t ∈ J, 3 ≤ t.1 ∧ t.1 ≤ 16 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2 ∧
      t.2.2 ≤ bkExitWidth s := by
    rintro ⟨c, o, r⟩ ht
    simp only [hJ, mem_sigma, mem_product, mem_Icc] at ht ⊢
    omega
  set b : ℤ × ℤ × ℕ → ℝ := fun t ↦ 1 - (trRepCoeff s t.1.toNat t.2.1.toNat : ℝ) with hb_def
  have h := tsum_trPassage_mul_exp_neg_trCount_le_one_sub ξ v s (J.image e) b ?_ ?_
  · convert h using 2
    rw [sum_image hinj, trDirectCrossing_eq_sum_sum_sum, sum_sigma]
    refine sum_congr rfl fun c _ ↦ ?_
    rw [sum_product]
    refine sum_congr rfl fun o _ ↦ sum_congr rfl fun r _ ↦ ?_
    simp only [hb_def, he, Int.toNat_natCast]
    ring
  · simp only [mem_image]
    rintro _ ⟨t, ht, rfl⟩
    have := hmemJ t ht
    simp only [he]
    omega
  · simp only [mem_image]
    rintro _ ⟨⟨c, o, r⟩, ht, rfl⟩ π hπ
    obtain ⟨hc3, hc16, ho1, -, hr1, hrf⟩ := hmemJ _ ht
    simp only [he, hb_def, Int.toNat_natCast] at hπ ⊢
    have hR := chPaidReward_le_trCount_of_mem_trRawThreeWitness ξ v hr1 hπ
    have hE := exp_neg_zStar_mul_chPaidReward_le_one_sub_trRepCoeff hξ hv hb
      (r := r) hrf hc3 hc16 ho1
    rw [← hs_def, ← hs] at hE
    have hγ : (gammaStar : ℝ) = zStar := by rw [gammaStar_cast, zStar_cast]
    have hz : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
    refine le_trans (Real.exp_le_exp.mpr ?_) hE
    rw [hγ]
    nlinarith

end CollatzPosDens
