/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.NstarGate
public import CollatzPosDens.Recipe.NstarRange
public import CollatzPosDens.Recipe.PhEj
public import CollatzPosDens.Recipe.PhHhist
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Seed.ZnIncrementIdentity
public import CollatzPosDens.Seed.PairingSharp
public import CollatzPosDens.FirstCrossing.SelEnd
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.LevelLateLower
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.CentralDeficitDecay
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FiniteTransfer.TransferEstimate
public import CollatzPosDens.Mixing.MxProfileAntitone
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.PrefixExtension
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.MxProfile

/-!
# The central increment bound

Let `t` be an odd positive integer and `n ≥ N_*` an integer. Then
$$|Z_{n+1}(t) - Z_n(t)| \le \mathsf E_n,$$
where `E_n` is the propagation majorant.

Write `b = b_n`, `x_n = 2^{12} 𝗀^n` and `Q = h_b + k_{n+1}`; by the range of `N_*`,
`n ≥ N_* ≥ j_e`. Since `b ≥ b_0 = 16544 ≥ 256`, the growth step `e_b = ⌈b/100⌉` is at most
`b/50`, so `b_{n+1} ≤ 51 b/50` and `Q ≤ (8/5 + 51/200) b < 2b`. By the increment identity,
`Z_{n+1}(t) - Z_n(t) = ∑_{h ∈ 𝓗_n(t)} ω(h) f_n(R_h mod 3^Q)`, and the sharp pairing estimate
bounds its absolute value by `𝓗_hist n^{5/2} 𝗀^{n/2} ⟨|f_n|⟩_Q`. The finite-transfer estimate,
applied to the finite prefix-disjoint family `𝒞(b, K_n)` with `k = k_{n+1}` and `m = k_n` (both
at least the gate level `n₀` by the late lower bound on the levels), at the bootstrap Fourier
index `b`, bounds `⟨|f_n|⟩_Q` by `𝔐_b(k_{n+1}) + 𝔐_b(k_n) + 1 - 𝐩(𝒞(b, K_n))`. Since
`n₀ < 2^{12} 𝗀^{N_*} ≤ x_n ≤ k_n ≤ k_{n+1}`, the antitonicity of the mixing profile `𝔐_b`
bounds both profile terms by `𝔐_b(x_n)`, and the decay of the central deficit bounds
`1 - 𝐩(𝒞(b, K_n))` by `½ 𝗀^{-3n/2} + 2^{-29} 2^{-n/56}`. Multiplying out gives the
propagation majorant `E_n`.

## Main results

* `CollatzPosDens.abs_weightedCentralSum_succ_sub_le`: the bound above.

## Implementation notes

The starting point `t` is an integer, cast to `ℚ` as in the definition of `Z_n(t)`.

## References

* [Mazur, *Collatz positive density*], §16.5.
-/

@[expose] public section

open Finset InformationTheory

namespace CollatzPosDens

/-- `Q = h_{b_n} + k_{n+1} ≤ 2 b_n`, as `b_n ≥ 16544`. -/
private lemma centralIncrement_modulus_le (n : ℕ) :
    hb (scale n) + level (n + 1) ≤ 2 * scale n := by
  have h := scale_succ n
  have hb := sixteen544_le_scale n
  rw [eb_eq] at h
  rw [hb_eq, level_def, h]
  omega

/-- The mixing gate level `n₀` is at most `k_j` once `j ≥ N_*`. -/
private lemma mxGateLevel_le_level {j : ℕ} (hj : generationThreshold ≤ j) :
    mxGateLevel ≤ level j := by
  exact_mod_cast (le_max_left _ _).trans (level_late_lower hj)

/-- `n₀ ≤ 2^{12} 𝗀^j` once `j ≥ N_*`. -/
private lemma mxGateLevel_le_two_pow_twelve_mul_growthRatio_pow {j : ℕ}
    (hj : generationThreshold ≤ j) :
    (mxGateLevel : ℝ) ≤ 2 ^ 12 * (growthRatio : ℝ) ^ j :=
  (mxGateLevel_lt_two_pow_twelve_mul_growthRatio_pow.trans_le (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ one_lt_growthRatio_cast.le hj) (by norm_num))).le

/-- The deficit `1 - 𝐩(𝒞(b_n, K_n))`, as a real number, is at most
`½ 𝗀^{-3n/2} + 2^{-29} 2^{-n/56}`. -/
private lemma one_sub_geomMass_centralFamily_toReal_le (n : ℕ) :
    1 - (geomMass (centralFamily (scale n) (cap n))).toReal ≤
      1 / 2 * (growthRatio : ℝ) ^ (-(3 * (n : ℝ) / 2)) +
        (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) / 56)) := by
  have hg := growthRatio_cast_pos
  have h := ENNReal.toReal_le_of_le_ofReal (by positivity)
    (one_sub_geomMass_centralFamily_scale_cap_le_rpow n)
  have hle : geomMass (centralFamily (scale n) (cap n)) ≤ 1 :=
    geomMass_le_one_of_isPrefixFree
      (fun x hx y hy => isPrefixFree_firstCrossing _ _ _ x hx.1 y hy.1)
      (fun _ hw => length_le_hb_of_mem_firstCrossing hw.1)
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top,
    ENNReal.toReal_one] at h
  have h29 : (2 : ℝ) ^ (-29 : ℤ) = (2 : ℝ) ^ (-29 : ℝ) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [h29] at h
  exact h

/-- The finite-transfer, profile and deficit estimates:
`⟨|f_n|⟩_Q ≤ 2 𝔐_b(2^{12} 𝗀^n) + ½ 𝗀^{-3n/2} + 2^{-29} 2^{-n/56}`. -/
private lemma residueAvg_abs_centralIncrementDensity_le {n : ℕ}
    (hn : generationThreshold ≤ n) :
    residueAvg (hb (scale n) + level (n + 1)) (fun y => |centralIncrementDensity n y|) ≤
      2 * mxProfile .b (2 ^ 12 * (growthRatio : ℝ) ^ (n : ℝ)) +
        1 / 2 * (growthRatio : ℝ) ^ (-(3 * (n : ℝ) / 2)) +
        (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((n : ℝ) / 56)) := by
  classical
  have hn1 : generationThreshold ≤ n + 1 := hn.trans (Nat.le_succ n)
  have hfin := centralFamily_finite (scale n) (cap n)
  set V := hfin.toFinset
  have hVcoe : (V : Set Word) = centralFamily (scale n) (cap n) := Set.Finite.coe_toFinset _
  have hV : IsPrefixFree (V : Set Word) := by
    rw [hVcoe]
    exact fun x hx y hy => isPrefixFree_firstCrossing _ _ _ x hx.1 y hy.1
  have hlen : ∀ w ∈ V, w.length ≤ hb (scale n) := fun w hw =>
    length_le_hb_of_mem_firstCrossing ((Set.Finite.mem_toFinset _).1 hw).1
  have htr := residueAvg_abs_sum_liftedTransfer_refDensity_sub_le .b hV
    (mxGateLevel_le_level hn1) hlen (mxGateLevel_le_level hn)
    (centralIncrementDensity_level_le n)
  have hfeq : ∀ y, centralIncrementDensity n y = ∑ w ∈ V.attach,
      liftedTransfer w.1 (Nat.add_le_add_right (hlen w.1 w.2) _) (refDensity (level (n + 1))) y -
      refDensity (level n) (residueReduction (centralIncrementDensity_level_le n) y) := by
    intro y
    simp only [centralIncrementDensity]
    congr 1
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_attach]
    exact Finset.sum_congr rfl fun w _ => dite_eq_left_of_eq_true
      (eq_true (Nat.add_le_add_right (hlen w.1 w.2) _))
  simp only [← hfeq, hVcoe] at htr
  have hx := mxGateLevel_le_two_pow_twelve_mul_growthRatio_pow hn
  have hk : 2 ^ 12 * (growthRatio : ℝ) ^ n ≤ level n :=
    (le_max_right _ _).trans (level_late_lower hn)
  have hk1 : (level n : ℝ) ≤ level (n + 1) := by
    exact_mod_cast level_monotone (Nat.le_succ n)
  have hM1 := mxProfile_antitoneOn .b hx hk
  have hM2 := mxProfile_antitoneOn .b hx (hk.trans hk1)
  rw [Real.rpow_natCast]
  have hdef := one_sub_geomMass_centralFamily_toReal_le n
  refine htr.trans ?_
  have e := add_le_add (add_le_add hM2 hM1) hdef
  convert e using 1 <;> ring_nf

/-- **Central increment bound**. For an odd positive integer `t` and `n ≥ N_*`,
`|Z_{n+1}(t) - Z_n(t)| ≤ E_n`, the propagation majorant. -/
@[collatz_pos_dens "lem_central_increment"]
theorem abs_weightedCentralSum_succ_sub_le {t : ℤ} (hodd : Odd t) (ht : 0 < t) {n : ℕ}
    (hn : generationThreshold ≤ n) :
    |weightedCentralSum (n + 1) t - weightedCentralSum n t| ≤ propagationMajorant n := by
  classical
  have hselEnd : selEnd ≤ n := selEnd_le_generationThreshold_range.1.trans hn
  set A : ℝ := (Hhist : ℝ) * (n : ℝ) ^ (5 / 2 : ℝ) * (growthRatio : ℝ) ^ ((n : ℝ) / 2)
  have hA : 0 ≤ A := by
    have hH : (0 : ℝ) < Hhist := by exact_mod_cast Hhist_pos
    have hg := growthRatio_cast_pos
    positivity
  have step1 : |weightedCentralSum (n + 1) t - weightedCentralSum n t| ≤
      A * residueAvg (hb (scale n) + level (n + 1)) (fun y => |centralIncrementDensity n y|) := by
    rw [weightedCentralSum_succ_sub t hselEnd,
      weightedCentralSum_succ_sub_sum_residueHistogram_mul]
    refine ((Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)).trans
      (finsum_weight_mul_abs_le_Hhist hodd ht hn
        (centralIncrement_modulus_le n) subset_rfl _)
    rw [finsum_mem_eq_finite_toFinset_sum _ (centralHistories_finite _ n)]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [abs_mul, abs_of_nonneg (by exact_mod_cast (Word.weight_pos _).le)]
  rw [propagationMajorant_def]
  exact step1.trans (mul_le_mul_of_nonneg_left (residueAvg_abs_centralIncrementDensity_le hn) hA)

end CollatzPosDens
