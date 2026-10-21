/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.LengthLoss
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Transfer.FiberSource
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.RefDensityMean
public import CollatzPosDens.Transfer.S02LiftedTransfer
public import CollatzPosDens.Transfer.TransferAbsMean
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.NstarRange
public import CollatzPosDens.Recipe.PhHhist
public import CollatzPosDens.Seed.PairingSharp
public import CollatzPosDens.Terminal.MarkedMass
public import CollatzPosDens.Terminal.MarkedMassUnfiltered
public import CollatzPosDens.Terminal.ShiftCount

/-!
# Removing the length condition costs little

Let `t ≥ t_min` be an odd integer (`t_min = targetFloor`) and `j ≥ J_c` (`J_c = covGen`). Then
$$0 \le \Theta^{\circ}_{j,X}(t) - \Theta_{j,X}(t) \le 5\,j^{9/2}\,\mathsf g^{j/2}\,
  \frac{2^{113}}{b_j^{6}}.$$

The difference is the sum, over `h ∈ 𝓗_j(t)` and over the first crossings
`w ∈ 𝒲(b_j, u_h, K_j)` admissible from `R_h` and failing `Λ_{b_j,u_h}`, of the nonnegative
terms `ω(h) ω(w) ρ_{k_j}(src(w, R_h) mod 3^{k_j})`; this gives the lower bound. For the upper
bound, with `Q = h_{b_j} + k_j ≤ 2 b_j`, the inner sum for `h` is the value at `R_h mod 3^Q` of
`g_u = ∑_{w ∈ 𝒲(b_j,u,K_j), ¬Λ_{b_j,u}(w)} 𝒯_{w,Q} ρ_{k_j}` with `u = u_h`, by
`CollatzPosDens.liftedTransfer_intCast`. Grouping the histories by their shift `u`, which takes
fewer than `j^2/82` values (`CollatzPosDens.ncard_historyShift_image_lt`),
`CollatzPosDens.finsum_weight_mul_abs_le_Hhist` bounds each group by
`𝓗_hist j^{5/2} 𝗀^{j/2} ⟨g_u⟩_Q` with `𝓗_hist = 344` (it applies as `N_* ≤ J_c ≤ j`).
The mean `⟨g_u⟩_Q` is the geometric mass `𝐩(𝓕_u)` of the removed words, and
`𝐩(𝓕_u) ≤ 2^{113}/b_j^6` by `CollatzPosDens.geomMass_firstCrossing_not_lengthOk_le`.
Since `344/82 ≤ 5`, summing over the shifts gives `5 j^{9/2} 𝗀^{j/2} 2^{113}/b_j^6`.

## Main results

* `CollatzPosDens.markedMassUnfiltered_sub_markedMass_nonneg`:
  `0 ≤ Θ°_{j,X}(t) - Θ_{j,X}(t)`.
* `CollatzPosDens.markedMassUnfiltered_sub_markedMass_le`:
  `Θ°_{j,X}(t) - Θ_{j,X}(t) ≤ 5 j^{9/2} 𝗀^{j/2} 2^{113}/b_j^6`.

## Implementation notes

The lower bound holds for every `j`, `X` and `t`, and is stated so. The upper bound is stated
for every real `X` instead of an admissible one, since
`CollatzPosDens.geomMass_firstCrossing_not_lengthOk_le` holds for every integer shift. The seed
`t` is an integer, cast to `ℚ` as in `CollatzPosDens.markedMass`; `j^{9/2}` is the real power
`(j : ℝ) ^ (9/2 : ℝ)` and `𝗀^{j/2}` the real power `(growthRatio : ℝ) ^ ((j : ℝ) / 2)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset
open scoped ENNReal

/-- The words of `𝒲(b_j, u_h, K_j)` that fail `Λ_{b_j,u_h}` and are admissible from `R_h`. -/
private def removedWords (n : ℕ) (X : ℝ) (t : ℚ) (h : Fin n → Word) : Set Word :=
  {w | w ∈ firstCrossing (scale n) (historyShift n X t h) (cap n) ∧
    ¬LengthOk (scale n) (historyShift n X t h) w ∧ Admissible (historyEndpoint t h) w}

private theorem removedWords_finite (n : ℕ) (X : ℝ) (t : ℚ) (h : Fin n → Word) :
    (removedWords n X t h).Finite :=
  (firstCrossing_finite _ _ _).subset fun _ hw => hw.1

/-- The summand `ω(w) ρ_{k_j}(src(w, R_h) mod 3^{k_j})` of the marked masses. -/
private noncomputable abbrev removedTerm (n : ℕ) (t : ℚ) (h : Fin n → Word)
    (w : Word) : ℝ :=
  (w.weight : ℝ) * refDensity (level n) ((src w (historyEndpoint t h)).num : ResidueGroup (level n))

/-- `Θ° - Θ` is the sum over the removed words. -/
private theorem sub_eq_sum (n : ℕ) (X : ℝ) (t : ℚ) :
    markedMassUnfiltered n X t - markedMass n X t =
      ∑ h ∈ (centralHistories_finite t n).toFinset,
        ((concatWord h).weight : ℝ) *
          ∑ w ∈ (removedWords_finite n X t h).toFinset, removedTerm n t h w := by
  classical
  rw [markedMassUnfiltered_eq_sum, markedMass_eq_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun h _ => ?_
  rw [← mul_sub, ← sum_filter_add_sum_filter_not
    (markedMassUnfilteredWords_finite n X t h).toFinset
    (fun w => LengthOk (scale n) (historyShift n X t h) w)]
  have h1 : (markedMassUnfilteredWords_finite n X t h).toFinset.filter
      (fun w => LengthOk (scale n) (historyShift n X t h) w) =
        (markedMassWords_finite n X t h).toFinset := by
    ext w
    simp only [mem_filter, Set.Finite.mem_toFinset, mem_markedMassUnfilteredWords,
      mem_markedMassWords]
    tauto
  have h2 : (markedMassUnfilteredWords_finite n X t h).toFinset.filter
      (fun w => ¬LengthOk (scale n) (historyShift n X t h) w) =
        (removedWords_finite n X t h).toFinset := by
    ext w
    simp only [mem_filter, Set.Finite.mem_toFinset, mem_markedMassUnfilteredWords,
      removedWords, Set.mem_ofPred_eq]
    tauto
  rw [h1, h2, add_sub_cancel_left]

/-- **Removing the length condition, lower bound.** `0 ≤ Θ°_{j,X}(t) - Θ_{j,X}(t)`. -/
@[collatz_pos_dens "lem_length_removed"]
theorem markedMassUnfiltered_sub_markedMass_nonneg (j : ℕ) (X : ℝ) (t : ℚ) :
    0 ≤ markedMassUnfiltered j X t - markedMass j X t := by
  rw [sub_eq_sum]
  refine sum_nonneg fun h _ => mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) ?_
  exact sum_nonneg fun w _ =>
    mul_nonneg (by exact_mod_cast (Word.weight_pos _).le) (refDensity_nonneg _ _)

/-- The removed first crossings `{w ∈ 𝒲(b_j, v, K_j) : ¬Λ_{b_j,v}(w)}`. -/
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

/-- The function `g_v = ∑_{w ∈ 𝒲(b_j,v,K_j), ¬Λ_{b_j,v}(w)} 𝒯_{w,Q} ρ_{k_j}` on `G_Q`, for
`Q = h_{b_j} + k_j`. -/
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

/-- The mean of `g_v` is the geometric mass of the removed words. -/
private theorem residueAvg_removedDensity (n v : ℕ) :
    residueAvg (hb (scale n) + level n) (removedDensity n v) =
      ∑ w ∈ (removedFamily_finite n v).toFinset, (2 : ℝ)⁻¹ ^ w.valSum := by
  rw [residueAvg_def]
  unfold removedDensity
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun w hw => ?_
  simp only [dite_eq_left (length_add_level_le hw)]
  rw [← residueAvg_def, residueAvg_liftedTransfer, residueAvg_refDensity, zpow_neg, zpow_natCast,
    ← inv_pow, mul_one]

/-- The geometric mass `𝐩(𝓕_v)` of the removed words is at most `2^{113}/b_j^6`. -/
private theorem removedMass_le (n v : ℕ) :
    ∑ w ∈ (removedFamily_finite n v).toFinset, (2 : ℝ)⁻¹ ^ w.valSum ≤
      2 ^ 113 / (scale n : ℝ) ^ 6 := by
  have hloss := geomMass_firstCrossing_not_lengthOk_le (scale n) (v : ℤ) (cap n)
  have hset : {w | w ∈ firstCrossing (scale n) (v : ℤ) (cap n) ∧
      ¬LengthOk (scale n) v w} = ((removedFamily_finite n v).toFinset : Set Word) := by
    rw [Set.Finite.coe_toFinset]
    rfl
  rw [hset] at hloss
  have hb0 : (scale n : ℝ≥0∞) ≠ 0 := by
    have := sixteen544_le_scale n
    exact_mod_cast (show scale n ≠ 0 by omega)
  have hne : (2 : ℝ≥0∞) ^ 113 / (scale n : ℝ≥0∞) ^ 6 ≠ ⊤ :=
    ENNReal.div_ne_top (by simp) (pow_ne_zero _ hb0)
  have hreal := ENNReal.toReal_mono hne hloss
  rw [toReal_geomMass_coe_finset, ENNReal.toReal_div] at hreal
  simpa only [ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast] using hreal

/-- The inner sum for `h` is `g_{u_h}` at `R_h mod 3^Q`. -/
private theorem sum_removedWords_eq {t : ℤ} (hodd : Odd t) (ht : 0 < t)
    {n : ℕ} (X : ℝ) {h : Fin n → Word} (hh : h ∈ centralHistories t n) :
    ∑ w ∈ (removedWords_finite n X t h).toFinset, removedTerm n t h w =
      removedDensity n (historyShift n X t h)
        ((historyEndpoint t h).num : ResidueGroup (hb (scale n) + level n)) := by
  classical
  obtain ⟨m, hR⟩ := exists_historyEndpoint_eq_intCast hodd ht hh
  unfold removedDensity
  rw [hR, Rat.num_intCast]
  have hterm : ∀ w ∈ (removedFamily_finite n (historyShift n X t h)).toFinset,
      (if hw : w.length + level n ≤ hb (scale n) + level n then
        liftedTransfer w hw (refDensity (level n)) (m : ResidueGroup (hb (scale n) + level n))
      else 0) =
      if Admissible (m : ℚ) w then removedTerm n t h w else 0 := by
    intro w hw
    rw [dite_eq_left (length_add_level_le hw), liftedTransfer_intCast, removedTerm, hR]
  rw [sum_congr rfl hterm, ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext w
  simp only [mem_filter, Set.Finite.mem_toFinset, removedWords, removedFamily,
    Set.mem_ofPred_eq, hR]
  exact and_assoc.symm

/-- The prefactor `𝓗_hist j^{5/2} 𝗀^{j/2}`. -/
private noncomputable abbrev pairingFactor (n : ℕ) : ℝ :=
  (Hhist : ℝ) * (n : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2)

/-- Each group of central histories with a common shift `v` contributes at most
`𝓗_hist j^{5/2} 𝗀^{j/2} · 2^{113}/b_j^6`. -/
private theorem sum_filter_shift_eq_le {t : ℤ} (hodd : Odd t) (ht : 0 < t) {n : ℕ}
    (hn : generationThreshold ≤ n) (X : ℝ) (v : ℕ) :
    ∑ h ∈ (centralHistories_finite (t : ℚ) n).toFinset with
        historyShift n X t h = v,
      ((concatWord h).weight : ℝ) * removedDensity n (historyShift n X t h)
        ((historyEndpoint t h).num : ResidueGroup (hb (scale n) + level n)) ≤
      pairingFactor n * (2 ^ 113 / (scale n : ℝ) ^ 6) := by
  classical
  have hQ : hb (scale n) + level n ≤ 2 * scale n := by
    simp only [hb_def, wb_def, level_def]
    omega
  have hsub : (((centralHistories_finite (t : ℚ) n).toFinset.filter
      fun h => historyShift n X t h = v : Finset _) : Set (Fin n → Word)) ⊆
        centralHistories t n := by
    intro h hh
    simp only [coe_filter, Set.mem_ofPred_eq, Set.Finite.mem_toFinset] at hh
    exact hh.1
  have hp := finsum_weight_mul_abs_le_Hhist hodd ht hn hQ hsub (removedDensity n v)
  rw [finsum_mem_coe_finset] at hp
  have habs : residueAvg _ (fun y => |removedDensity n v y|) =
      residueAvg _ (removedDensity n v) :=
    congrArg _ (funext fun y => abs_of_nonneg (removedDensity_nonneg n v y))
  rw [habs, residueAvg_removedDensity] at hp
  have hG : 0 ≤ pairingFactor n := by
    have := growthRatio_cast_pos
    rw [pairingFactor, Hhist_cast]
    positivity
  calc _ = ∑ h ∈ (centralHistories_finite (t : ℚ) n).toFinset with
          historyShift n X t h = v, ((concatWord h).weight : ℝ) *
            |removedDensity n v ((historyEndpoint t h).num : ResidueGroup _)| := by
        refine sum_congr rfl fun h hh => ?_
        rw [(mem_filter.mp hh).2, abs_of_nonneg (removedDensity_nonneg n v _)]
    _ ≤ pairingFactor n * ∑ w ∈ (removedFamily_finite n v).toFinset,
          (2 : ℝ)⁻¹ ^ w.valSum := hp
    _ ≤ _ := mul_le_mul_of_nonneg_left (removedMass_le n v) hG

/-- **Removing the length condition, upper bound.** For an odd integer `t ≥ t_min`, every
`j ≥ J_c` and every real `X`, `Θ°_{j,X}(t) - Θ_{j,X}(t) ≤ 5 j^{9/2} 𝗀^{j/2} 2^{113}/b_j^6`. -/
@[collatz_pos_dens "lem_length_removed"]
theorem markedMassUnfiltered_sub_markedMass_le {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) {j : ℕ} (hj : covGen ≤ j) (X : ℝ) :
    markedMassUnfiltered j X t - markedMass j X t ≤
      5 * (j : ℝ) ^ (9 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
        (2 ^ 113 / (scale j : ℝ) ^ 6) := by
  classical
  have ht0 : 0 < t := lt_of_lt_of_le (by exact_mod_cast targetFloor_pos) ht
  have hjN : generationThreshold ≤ j := selEnd_le_generationThreshold_range.2.trans hj
  set Hs := (centralHistories_finite (t : ℚ) j).toFinset
  set u : (Fin j → Word) → ℕ := historyShift j X t
  set E : ℝ := pairingFactor j * (2 ^ 113 / (scale j : ℝ) ^ 6)
  have hg := growthRatio_cast_pos
  have hE : 0 ≤ E := by
    simp only [E, pairingFactor, Hhist_cast]
    positivity
  have hcard : ((Hs.image u).card : ℝ) ≤ (j : ℝ) ^ 2 / 82 := by
    obtain ⟨-, hlt⟩ := ncard_historyShift_image_lt hj X hodd ht
    have : historyShift j X t '' centralHistories t j = ((Hs.image u : Finset _) : Set ℕ) := by
      rw [coe_image, Set.Finite.coe_toFinset]
    rw [this, Set.ncard_coe_finset] at hlt
    exact hlt.le
  rw [sub_eq_sum, sum_congr rfl fun h hh =>
      congrArg _ (sum_removedWords_eq hodd ht0 X (Set.Finite.mem_toFinset _ |>.mp hh)),
    ← sum_fiberwise_of_maps_to (g := u) (t := Hs.image u) fun h hh => mem_image_of_mem u hh]
  have hjpos : (0 : ℝ) < j := Nat.cast_pos.mpr
    (lt_of_lt_of_le (by rw [covGen_def]; norm_num) hj)
  have hpow : (j : ℝ) ^ (9 / 2 : ℝ) = (j : ℝ) ^ 2 * (j : ℝ) ^ (5 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hjpos]
    norm_num
  have hR : 0 ≤ (j : ℝ) ^ 2 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
      (2 ^ 113 / (scale j : ℝ) ^ 6) := by positivity
  calc _ ≤ ∑ _v ∈ Hs.image u, E := sum_le_sum fun v _ => sum_filter_shift_eq_le hodd ht0 hjN X v
    _ = (Hs.image u).card * E := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (j : ℝ) ^ 2 / 82 * E := mul_le_mul_of_nonneg_right hcard hE
    _ = 344 / 82 *
          ((j : ℝ) ^ 2 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
            (2 ^ 113 / (scale j : ℝ) ^ 6)) := by
        simp only [E, pairingFactor, Hhist_cast]
        ring
    _ ≤ 5 * ((j : ℝ) ^ 2 * (j : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) *
            (2 ^ 113 / (scale j : ℝ) ^ 6)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hR
    _ = _ := by rw [hpow]; ring

end CollatzPosDens
