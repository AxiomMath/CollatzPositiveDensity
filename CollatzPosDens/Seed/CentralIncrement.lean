/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.F
public import CollatzPosDens.Recipe.Growth
public import CollatzPosDens.Recipe.Varrho
public import CollatzPosDens.Recipe.Varsigma
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Seed.ZnIncrementIdentity
public import CollatzPosDens.Seed.Pairing
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.Level
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesB444
public import CollatzPosDens.FirstCrossing.LevelGate
public import CollatzPosDens.FirstCrossing.BracketDecay
public import CollatzPosDens.FirstCrossing.CentralDeficitDecay
public import CollatzPosDens.FirstCrossing.FirstCrossingFinite
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FiniteTransfer.TransferEstimate
public import CollatzPosDens.Transfer.MixingConst
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.PrefixExtension
public import CollatzPosDens.FirstCrossing.SurvivalProduct

/-!
# The central increment bound

Let `M` be an odd positive integer and `n ≥ 9200000`. Then
$$|Z_{n+1}(M) - Z_n(M)| \le F\, n^{5/2}\, \varrho^n.$$

Write `b = scale n` and `Q = hb b + level (n + 1)`. Since `b ≥ scale 444 = 16544`, the growth
step is `eb b = ⌈b/100⌉`, and `Q ≤ 2b`. By `weightedCentralSum_succ_sub`, the increment
`Z_{n+1}(M) - Z_n(M)` is `∑_{h ∈ 𝓗_n(M)} ω(h) f_n(R_h mod 3^Q)`, and
`pairing_finsum_weight_mul_abs_le` bounds its absolute value by
`(4075/56)(277/128) n^{5/2} 𝖦^n ⟨|f_n|⟩_Q`. The transfer estimate
`residueAvg_abs_sum_liftedTransfer_refDensity_sub_le`, applied to the finite prefix-free family
`centralFamily b (cap n)` with `k = level (n + 1)` and `ℓ = level n` (both at least `2^131072` by
`level_gate`), bounds `⟨|f_n|⟩_Q` by `(2/3)(C k^{-9/8} + C ℓ^{-9/8} + Δ_n)`, where
`Δ_n = 1 - 𝐩(centralFamily b (cap n))` lies in `[0, (2^121 + 1024 + 2^{-16}) ς^n]`, and
`bracket_decay_lt` bounds this by `(2/3)(28/1000)(C + 1) ς^n`. Finally `𝖦 ς = ϱ`, and
`(4075/56)(277/128)(2/3)(28/1000) = 45151/15360 < 3`, with `F = 3 (C + 1)`.

## Main results

* `CollatzPosDens.abs_weightedCentralSum_succ_sub_le`: the bound above.

## Implementation notes

The power `n^{5/2}` is the real power `(n : ℝ) ^ (5 / 2 : ℝ)`. The starting point `M` is an
integer, cast to `ℚ` as in the definition of `Z_n(M)`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open Finset InformationTheory

namespace CollatzPosDens

/-- `Q = h_{b_n} + k_{n+1} ≤ 2 b_n` once `b_n ≥ 256`. -/
private lemma centralIncrement_modulus_le (n : ℕ) (hb256 : 256 ≤ scale n) :
    hb (scale n) + level (n + 1) ≤ 2 * scale n := by
  have h := scale_succ n
  rw [eb_of_le hb256] at h
  rw [hb_eq, level_def, h]
  omega

/-- The deficit `Δ_n = 1 - 𝐩(𝒞(b_n, K_n))` is nonnegative. -/
lemma one_sub_geomMass_centralFamily_toReal_nonneg (n : ℕ) :
    0 ≤ 1 - (geomMass (centralFamily (scale n) (cap n))).toReal := by
  have := ENNReal.toReal_mono ENNReal.one_ne_top (geomMass_centralFamily_le_one (scale n) (cap n))
  rw [ENNReal.toReal_one] at this
  linarith

/-- The deficit `Δ_n = 1 - 𝐩(𝒞(b_n, K_n))` is at most `(2^121 + 1024 + 2^{-16}) ς^n`. -/
lemma one_sub_geomMass_centralFamily_toReal_le (n : ℕ) :
    1 - (geomMass (centralFamily (scale n) (cap n))).toReal ≤
      (2 ^ 121 + 1024 + 2⁻¹ ^ 16) * deficitRate ^ n := by
  have hς := deficitRate_pos
  have h := ENNReal.toReal_le_of_le_ofReal (by positivity)
    (one_sub_geomMass_centralFamily_scale_cap_le_deficitRate_pow n)
  rw [ENNReal.toReal_sub_of_le (geomMass_centralFamily_le_one _ _) ENNReal.one_ne_top,
    ENNReal.toReal_one] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  norm_num

/-- The residue average `⟨|f_n|⟩_Q` satisfies `⟨|f_n|⟩_Q ≤ (2/3)(28/1000)(C + 1) ς^n`. -/
lemma residueAvg_abs_centralIncrementDensity_le {n : ℕ} (hn : 9200000 ≤ n) :
    residueAvg (hb (scale n) + level (n + 1)) (fun y => |centralIncrementDensity n y|) ≤
      2 / 3 * (28 / 1000 * (mixingConst + 1) * deficitRate ^ n) := by
  classical
  have hfin := centralFamily_finite (scale n) (cap n)
  set V := hfin.toFinset
  have hVcoe : (V : Set Word) = centralFamily (scale n) (cap n) := Set.Finite.coe_toFinset _
  have hV : IsPrefixFree (V : Set Word) := by
    rw [hVcoe]
    exact fun x hx y hy => isPrefixFree_firstCrossing _ _ _ x hx.1 y hy.1
  have hlen : ∀ w ∈ V, w.length ≤ hb (scale n) := fun w hw =>
    length_le_hb_of_mem_firstCrossing ((Set.Finite.mem_toFinset _).1 hw).1
  have htr := residueAvg_abs_sum_liftedTransfer_refDensity_sub_le hV
    (level_gate (by omega) : 2 ^ 131072 ≤ level (n + 1)) hlen (level_gate hn)
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
  have hbr := bracket_decay_lt (by omega : 444 ≤ n) (level_monotone (Nat.le_succ n)) le_rfl
    (one_sub_geomMass_centralFamily_toReal_nonneg n) (one_sub_geomMass_centralFamily_toReal_le n)
  have hconv : ∀ k : ℕ, mixingConst / (k : ℝ) ^ (9 / 8 : ℝ) =
      mixingConst * (k : ℝ) ^ (-(9 / 8) : ℝ) := fun k => by
    rw [Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  refine htr.trans ?_
  rw [hconv, hconv]
  linarith

/-- For an odd positive integer `M` and `n ≥ 9200000`, `|Z_{n+1}(M) - Z_n(M)| ≤ F n^{5/2} ϱ^n`,
where `F = errorPrefactor` and `ϱ = errorDecayRatio`. -/
@[collatz_pos_dens "lem_central_increment"]
theorem abs_weightedCentralSum_succ_sub_le {M : ℤ} (hodd : Odd M) (hM : 0 < M) {n : ℕ}
    (hn : 9200000 ≤ n) :
    |weightedCentralSum (n + 1) M - weightedCentralSum n M| ≤
      errorPrefactor * (n : ℝ) ^ (5 / 2 : ℝ) * errorDecayRatio ^ n := by
  classical
  have hb444 : 16544 ≤ scale n := scale_444 ▸ scale_monotone (by omega : 444 ≤ n)
  set A : ℝ := 4075 / 56 * (277 / 128) * (n : ℝ) ^ (5 / 2 : ℝ) * histogramGrowth ^ n
  have hA : 0 ≤ A := by have := histogramGrowth_pos; positivity
  have step1 : |weightedCentralSum (n + 1) M - weightedCentralSum n M| ≤
      A * residueAvg (hb (scale n) + level (n + 1)) (fun y => |centralIncrementDensity n y|) := by
    rw [weightedCentralSum_succ_sub M (by omega),
      weightedCentralSum_succ_sub_sum_residueHistogram_mul]
    refine ((Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)).trans
      (pairing_finsum_weight_mul_abs_le hodd hM (by omega)
        (centralIncrement_modulus_le n (by omega)) subset_rfl _)
    rw [finsum_mem_eq_finite_toFinset_sum _ (centralHistories_finite _ n)]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [abs_mul, abs_of_nonneg (by exact_mod_cast (Word.weight_pos _).le)]
  have hC := mixingConst_pos
  have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (5 / 2 : ℝ) := by positivity
  have hvr : 0 ≤ errorDecayRatio ^ n := pow_nonneg errorDecayRatio_nonneg n
  calc |weightedCentralSum (n + 1) M - weightedCentralSum n M|
      ≤ A * (2 / 3 * (28 / 1000 * (mixingConst + 1) * deficitRate ^ n)) :=
        step1.trans (mul_le_mul_of_nonneg_left (residueAvg_abs_centralIncrementDensity_le hn) hA)
    _ = 45151 / 15360 * (mixingConst + 1) * (n : ℝ) ^ (5 / 2 : ℝ) *
          (histogramGrowth ^ n * deficitRate ^ n) := by
        simp only [A]
        ring
    _ ≤ 3 * (mixingConst + 1) * (n : ℝ) ^ (5 / 2 : ℝ) * errorDecayRatio ^ n := by
        rw [histogramGrowth_pow_mul_deficitRate_pow n]
        have : 0 ≤ (mixingConst + 1) * (n : ℝ) ^ (5 / 2 : ℝ) * errorDecayRatio ^ n := by
          positivity
        nlinarith
    _ = errorPrefactor * (n : ℝ) ^ (5 / 2 : ℝ) * errorDecayRatio ^ n := by
        rw [errorPrefactor_def]

end CollatzPosDens
