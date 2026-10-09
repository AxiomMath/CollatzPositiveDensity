/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.Transfer.FiberSource
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.RefDensityMean
public import CollatzPosDens.Transfer.LiftedTransfer
public import CollatzPosDens.Transfer.TransferAbsMean
public import CollatzPosDens.FirstCrossing.BracketDecay
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.LengthLoss
public import CollatzPosDens.FirstCrossing.LengthLossRate
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.Recipe.F
public import CollatzPosDens.Recipe.Growth
public import CollatzPosDens.Recipe.Varrho
public import CollatzPosDens.Recipe.Varsigma
public import CollatzPosDens.Seed.Pairing
public import CollatzPosDens.Terminal.MarkedMass
public import CollatzPosDens.Terminal.MarkedMassUnfiltered
public import CollatzPosDens.Terminal.ShiftCount

/-!
# Removing the length condition costs little

Write `Θ°_{n,X}(M) = CollatzPosDens.markedMassUnfiltered n X M` and
`Θ_{n,X}(M) = CollatzPosDens.markedMass n X M` for the marked masses without and with the length
condition, `b_j = CollatzPosDens.scale j`, `F = CollatzPosDens.errorPrefactor` and
`ϱ = CollatzPosDens.errorDecayRatio`. Let `M ≥ 16^{b_0}` be an odd integer and `n ≥ 9200000`.
Then
$$0 \le \Theta^{\circ}_{n,X}(M) - \Theta_{n,X}(M) \le F\,n^{9/2}\,\varrho^n.$$

The difference is the sum, over `h ∈ 𝓗_n(M)` and over the first crossings
`w ∈ 𝒲(b_n, u_h, K_n)` admissible from `R_h` and failing `Λ_{b_n,u_h}`, of the nonnegative
terms `ω(h) ω(w) ρ_{k_n}(src(w, R_h) mod 3^{k_n})`; this gives the lower bound. For the upper
bound, with `Q = h_{b_n} + k_n ≤ 2 b_n`, the inner sum for `h` is the value at `R_h mod 3^Q` of
`g_u = ∑_{w ∈ 𝒲(b_n,u,K_n), ¬Λ_{b_n,u}(w)} 𝒯_{w,Q} ρ_{k_n}` with `u = u_h`, by the fibre
description of the transfer at an integer point. Grouping the histories by their shift `u`,
which takes fewer than `n^2/56` values, the pairing estimate bounds each group by
`Π_n ⟨g_u⟩_Q` with `Π_n = (4075/56)(277/128) n^{5/2} 𝖦^n`. The mean `⟨g_u⟩_Q` is `2/3` times
the geometric mass `Δ'_u` of the removed words, and `Δ'_u ≤ 2^{114} b_n^{-6} ≤ 2^{95} ς^n`, so
the bracket decay gives `Δ'_u < (28/1000)(C+1) ς^n`. Finally `𝖦 ς = ϱ` and
`(1/56)(4075/56)(277/128)(2/3)(28/1000) < 3`.

## Main results

* `CollatzPosDens.markedMassUnfiltered_sub_markedMass_nonneg`:
  `0 ≤ Θ°_{n,X}(M) - Θ_{n,X}(M)`.
* `CollatzPosDens.markedMassUnfiltered_sub_markedMass_le`:
  `Θ°_{n,X}(M) - Θ_{n,X}(M) ≤ F n^{9/2} ϱ^n`.

## Implementation notes

The lower bound holds for every `n`, `X` and `M`, and is stated so. The upper bound is stated
under weaker hypotheses than the source's: `n ≥ 10000` (all that the pairing estimate and the
shift count need) instead of `n ≥ 9200000`, and every real `X` instead of an admissible one,
since the length-loss bound holds for every shift. The seed `M` is an integer, cast to `ℚ` as
in `CollatzPosDens.markedMass`, and `n^{9/2}` is the real power `(n : ℝ) ^ (9/2 : ℝ)`.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

open Finset
open scoped ENNReal

/-- The words of `𝒲(b_n, u_h, K_n)` that fail `Λ_{b_n,u_h}` and are admissible from `R_h`. -/
private def removedWords (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) : Set Word :=
  {w | w ∈ firstCrossing (scale n) (historyShift n X M h) (cap n) ∧
    ¬LengthOk (scale n) (historyShift n X M h) w ∧ Admissible (historyEndpoint M h) w}

private theorem removedWords_finite (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) :
    (removedWords n X M h).Finite :=
  (firstCrossing_finite _ _ _).subset fun _ hw => hw.1

/-- The summand `ω(w) ρ_{k_n}(src(w, R_h) mod 3^{k_n})` of the marked masses. -/
private noncomputable abbrev removedTerm (n : ℕ) (M : ℚ) (h : Fin n → Word) (w : Word) : ℝ :=
  (w.weight : ℝ) * refDensity (level n) ((src w (historyEndpoint M h)).num : ResidueGroup (level n))

/-- `Θ° - Θ` is the sum over the removed words. -/
private theorem sub_eq_sum (n : ℕ) (X : ℝ) (M : ℚ) :
    markedMassUnfiltered n X M - markedMass n X M =
      ∑ h ∈ (centralHistories_finite M n).toFinset,
        ((concatWord h).weight : ℝ) *
          ∑ w ∈ (removedWords_finite n X M h).toFinset, removedTerm n M h w := by
  classical
  rw [markedMassUnfiltered_eq_sum, markedMass_eq_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun h _ => ?_
  rw [← mul_sub, ← sum_filter_add_sum_filter_not
    (markedMassUnfilteredWords_finite n X M h).toFinset
    (fun w => LengthOk (scale n) (historyShift n X M h) w)]
  have h1 : (markedMassUnfilteredWords_finite n X M h).toFinset.filter
      (fun w => LengthOk (scale n) (historyShift n X M h) w) =
        (markedMassWords_finite n X M h).toFinset := by
    ext w
    simp only [mem_filter, Set.Finite.mem_toFinset, mem_markedMassUnfilteredWords,
      mem_markedMassWords]
    tauto
  have h2 : (markedMassUnfilteredWords_finite n X M h).toFinset.filter
      (fun w => ¬LengthOk (scale n) (historyShift n X M h) w) =
        (removedWords_finite n X M h).toFinset := by
    ext w
    simp only [mem_filter, Set.Finite.mem_toFinset, mem_markedMassUnfilteredWords,
      removedWords, Set.mem_ofPred_eq]
    tauto
  rw [h1, h2, add_sub_cancel_left]

/-- **Removing the length condition, lower bound.** `0 ≤ Θ°_{n,X}(M) - Θ_{n,X}(M)`. -/
@[collatz_pos_dens "lem_length_removed"]
theorem markedMassUnfiltered_sub_markedMass_nonneg (n : ℕ) (X : ℝ) (M : ℚ) :
    0 ≤ markedMassUnfiltered n X M - markedMass n X M := by
  rw [sub_eq_sum]
  refine sum_nonneg fun h _ => mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) ?_
  exact sum_nonneg fun w _ =>
    mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) (refDensity_nonneg _ _)

/-- The removed first crossings `{w ∈ 𝒲(b_n, v, K_n) : ¬Λ_{b_n,v}(w)}`. -/
private def removedFamily (n v : ℕ) : Set Word :=
  {w | w ∈ firstCrossing (scale n) v (cap n) ∧ ¬LengthOk (scale n) v w}

private theorem removedFamily_finite (n v : ℕ) : (removedFamily n v).Finite :=
  (firstCrossing_finite _ _ _).subset fun _ hw => hw.1

private theorem length_add_level_le {n v : ℕ} {w : Word}
    (hw : w ∈ (removedFamily_finite n v).toFinset) :
    w.length + level n ≤ hb (scale n) + level n := by
  rw [Set.Finite.mem_toFinset] at hw
  have := length_le_hb_of_mem_firstCrossing hw.1
  omega

/-- The function `g_v = ∑_{w ∈ 𝒲(b_n,v,K_n), ¬Λ_{b_n,v}(w)} 𝒯_{w,Q} ρ_{k_n}` on `G_Q`, for
`Q = h_{b_n} + k_n`. -/
private noncomputable def removedDensity (n v : ℕ)
    (y : ResidueGroup (hb (scale n) + level n)) : ℝ :=
  ∑ w ∈ (removedFamily_finite n v).toFinset,
    if hw : w.length + level n ≤ hb (scale n) + level n then
      liftedTransfer w hw (refDensity (level n)) y
    else 0

private theorem removedDensity_nonneg (n v : ℕ) (y : ResidueGroup (hb (scale n) + level n)) :
    0 ≤ removedDensity n v y := by
  refine sum_nonneg fun w _ => ?_
  split_ifs with hw
  · exact liftedTransfer_nonneg w hw (refDensity_nonneg _) y
  · exact le_rfl

/-- The mean of `g_v` is `2/3` times the geometric mass of the removed words. -/
private theorem residueAvg_removedDensity (n v : ℕ) :
    residueAvg (hb (scale n) + level n) (removedDensity n v) =
      2 / 3 * ∑ w ∈ (removedFamily_finite n v).toFinset, (2 : ℝ)⁻¹ ^ w.valSum := by
  rw [residueAvg_def]
  unfold removedDensity
  rw [sum_comm, mul_sum, mul_sum]
  refine sum_congr rfl fun w hw => ?_
  simp only [dite_eq_left (length_add_level_le hw)]
  rw [← residueAvg_def, residueAvg_liftedTransfer, residueAvg_refDensity, zpow_neg, zpow_natCast,
    ← inv_pow]
  ring

/-- The geometric mass `Δ'_v` of the removed words is below `(28/1000)(C+1) ς^n`. -/
private theorem removedMass_lt {n : ℕ} (hn : 444 ≤ n) (v : ℕ) :
    ∑ w ∈ (removedFamily_finite n v).toFinset, (2 : ℝ)⁻¹ ^ w.valSum <
      28 / 1000 * (mixingConst + 1) * deficitRate ^ n := by
  set b := scale n
  have hb0 : 0 < b := lt_of_lt_of_le (by norm_num) (nine_le_scale n)
  have hloss := geomMass_firstCrossing_not_lengthOk_le b (v : ℤ) (cap n)
  have hset : {w | w ∈ firstCrossing b (v : ℤ) (cap n) ∧ ¬LengthOk b v w} =
      ((removedFamily_finite n v).toFinset : Set Word) := by
    rw [Set.Finite.coe_toFinset]
    rfl
  rw [hset] at hloss
  have hne : (2 : ℝ≥0∞) ^ 114 / (b : ℝ≥0∞) ^ 6 ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (pow_ne_zero _ (by exact_mod_cast hb0.ne'))
  have hreal := ENNReal.toReal_mono hne hloss
  rw [toReal_geomMass_coe_finset] at hreal
  simp only [ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_div,
    ENNReal.toReal_natCast] at hreal
  have hrate := lengthLossRate_le n
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv] at hrate
  have hs := deficitRate_pos
  have hsn : 0 ≤ deficitRate ^ n := pow_nonneg hs.le n
  set D := ∑ w ∈ (removedFamily_finite n v).toFinset, (2 : ℝ)⁻¹ ^ w.valSum
  have hD0 : 0 ≤ D := sum_nonneg fun w _ => by positivity
  have hD : D ≤ (2 ^ 121 + 1024 + 2⁻¹ ^ 16) * deficitRate ^ n := by
    refine (hreal.trans hrate).trans ?_
    gcongr
    norm_num
  have hbr := bracket_decay_lt hn le_rfl le_rfl hD0 hD
  have hk : 0 ≤ mixingConst * ((level n : ℕ) : ℝ) ^ (-(9 / 8) : ℝ) :=
    mul_nonneg mixingConst_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  linarith

/-- The inner sum for `h` is `g_{u_h}` at `R_h mod 3^Q`. -/
private theorem sum_removedWords_eq {M : ℤ} (hodd : Odd M) (hM : 0 < M)
    {n : ℕ} (X : ℝ) {h : Fin n → Word} (hh : h ∈ centralHistories M n) :
    ∑ w ∈ (removedWords_finite n X M h).toFinset, removedTerm n M h w =
      removedDensity n (historyShift n X M h)
        ((historyEndpoint M h).num : ResidueGroup (hb (scale n) + level n)) := by
  classical
  obtain ⟨m, hR⟩ := pairing_finsum_weight_mul_abs_le_endpoint_eq_int hodd hM hh
  unfold removedDensity
  rw [hR, Rat.num_intCast]
  have hterm : ∀ w ∈ (removedFamily_finite n (historyShift n X M h)).toFinset,
      (if hw : w.length + level n ≤ hb (scale n) + level n then
        liftedTransfer w hw (refDensity (level n)) (m : ResidueGroup (hb (scale n) + level n))
      else 0) =
      if Admissible (m : ℚ) w then removedTerm n M h w else 0 := by
    intro w hw
    rw [dite_eq_left (length_add_level_le hw), liftedTransfer_intCast, removedTerm, hR]
  rw [sum_congr rfl hterm, ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext w
  simp only [mem_filter, Set.Finite.mem_toFinset, removedWords, removedFamily,
    Set.mem_ofPred_eq, hR]
  exact and_assoc.symm

/-- The prefactor `Π_n = (4075/56)(277/128) n^{5/2} 𝖦^n` of the pairing estimate. -/
private noncomputable abbrev pairingFactor (n : ℕ) : ℝ :=
  4075 / 56 * (277 / 128) * (n : ℝ) ^ (5 / 2 : ℝ) * histogramGrowth ^ n

/-- Each group of central histories with a common shift `v` contributes at most
`Π_n · (2/3) · (28/1000)(C+1) ς^n`. -/
private theorem sum_filter_shift_eq_le {M : ℤ} (hodd : Odd M) (hM : 0 < M) {n : ℕ}
    (hn : 10000 ≤ n) (X : ℝ) (v : ℕ) :
    ∑ h ∈ (centralHistories_finite (M : ℚ) n).toFinset with
        historyShift n X M h = v,
      ((concatWord h).weight : ℝ) * removedDensity n (historyShift n X M h)
        ((historyEndpoint M h).num : ResidueGroup (hb (scale n) + level n)) ≤
      pairingFactor n * (2 / 3 * (28 / 1000 * (mixingConst + 1) * deficitRate ^ n)) := by
  classical
  have hQ : hb (scale n) + level n ≤ 2 * scale n := by
    simp only [hb_def, wb_def, level_def]
    omega
  have hsub : (((centralHistories_finite (M : ℚ) n).toFinset.filter
      fun h => historyShift n X M h = v : Finset _) : Set (Fin n → Word)) ⊆
        centralHistories M n := by
    intro h hh
    simp only [coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset] at hh
    exact hh.1
  have hp := pairing_finsum_weight_mul_abs_le hodd hM hn hQ hsub (removedDensity n v)
  rw [finsum_mem_coe_finset] at hp
  have habs : residueAvg _ (fun y => |removedDensity n v y|) =
      residueAvg _ (removedDensity n v) :=
    congrArg _ (funext fun y => abs_of_nonneg (removedDensity_nonneg n v y))
  rw [habs, residueAvg_removedDensity] at hp
  have hG : 0 ≤ pairingFactor n := by
    have := histogramGrowth_pos
    positivity
  calc _ = ∑ h ∈ (centralHistories_finite (M : ℚ) n).toFinset with
          historyShift n X M h = v, ((concatWord h).weight : ℝ) *
            |removedDensity n v ((historyEndpoint M h).num : ResidueGroup _)| := by
        refine sum_congr rfl fun h hh => ?_
        rw [(mem_filter.mp hh).2, abs_of_nonneg (removedDensity_nonneg n v _)]
    _ ≤ _ := hp
    _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (removedMass_lt
          (by omega) v).le (by norm_num)) hG

/-- **Removing the length condition, upper bound.** For an odd integer `M ≥ 16^{b_0}`, every
`n ≥ 10000` and every real `X`, `Θ°_{n,X}(M) - Θ_{n,X}(M) ≤ F n^{9/2} ϱ^n`. -/
@[collatz_pos_dens "lem_length_removed"]
theorem markedMassUnfiltered_sub_markedMass_le {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) {n : ℕ} (hn : 10000 ≤ n) (X : ℝ) :
    markedMassUnfiltered n X M - markedMass n X M ≤
      errorPrefactor * (n : ℝ) ^ (9 / 2 : ℝ) * errorDecayRatio ^ n := by
  classical
  have hM0 : 0 < M := lt_of_lt_of_le (by positivity) hM
  set Hs := (centralHistories_finite (M : ℚ) n).toFinset
  set u : (Fin n → Word) → ℕ := historyShift n X M
  set E : ℝ := pairingFactor n * (2 / 3 * (28 / 1000 * (mixingConst + 1) * deficitRate ^ n))
  have hE : 0 ≤ E := by
    have := histogramGrowth_pos
    have := mixingConst_pos
    have := deficitRate_pos
    positivity
  have hcard : ((Hs.image u).card : ℝ) ≤ (n : ℝ) ^ 2 / 56 := by
    obtain ⟨-, hlt⟩ := ncard_historyShift_image_lt hn X hodd hM
    have : historyShift n X M '' centralHistories M n = ((Hs.image u : Finset _) : Set ℕ) := by
      rw [coe_image, Set.Finite.coe_toFinset]
    rw [this, Set.ncard_coe_finset] at hlt
    exact hlt.le
  rw [sub_eq_sum, sum_congr rfl fun h hh =>
      congrArg _ (sum_removedWords_eq hodd hM0 X (Set.Finite.mem_toFinset _ |>.mp hh)),
    ← sum_fiberwise_of_maps_to (g := u) (t := Hs.image u) fun h hh => mem_image_of_mem u hh]
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hpow : (n : ℝ) ^ (9 / 2 : ℝ) = (n : ℝ) ^ 2 * (n : ℝ) ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hnpos]
    norm_num
  calc _ ≤ ∑ _v ∈ Hs.image u, E := sum_le_sum fun v _ => sum_filter_shift_eq_le hodd hM0 hn X v
    _ = (Hs.image u).card * E := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (n : ℝ) ^ 2 / 56 * E := mul_le_mul_of_nonneg_right hcard hE
    _ = 45151 / 15360 / 56 * (mixingConst + 1) * ((n : ℝ) ^ 2 * (n : ℝ) ^ (5 / 2 : ℝ)) *
          (histogramGrowth * deficitRate) ^ n := by
        simp only [E, pairingFactor, mul_pow]
        ring
    _ ≤ 3 * (mixingConst + 1) * ((n : ℝ) ^ 2 * (n : ℝ) ^ (5 / 2 : ℝ)) *
          (histogramGrowth * deficitRate) ^ n := by
        have := mixingConst_pos
        have := histogramGrowth_pos
        have := deficitRate_pos
        gcongr
        norm_num
    _ = _ := by
        rw [histogramGrowth_mul_deficitRate, hpow, errorPrefactor_def]

end CollatzPosDens
