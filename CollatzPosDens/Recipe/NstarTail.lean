/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.F
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.PhBphys
public import CollatzPosDens.FirstCrossing.PhDelta
public import CollatzPosDens.Recipe.Varrho
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Recipe.MomentTail

/-!
# The central tail after the generation threshold

Let `F` be the error prefactor, `ϱ = 𝗀^{-5/8}` the error decay ratio and `N_*` the generation
threshold. Then
$$F \sum_{j \ge N_*} j^{5/2} \varrho^j < \frac{47}{32}\, 2^{-24}.$$

Since `2^δ = 𝗀`, one has `ϱ^{N_*} = 2^{-5 N_* δ / 8}`, and the definition of `N_*` gives
`5 N_* δ / 8 ≥ B_ph + 535/8 = 23 + log₂ F + 535/8`; hence `F ϱ^{N_*} ≤ 2^{-23-535/8}`. As
`N_* = 9766262 ≥ 9200000`, the tail bound `CollatzPosDens.moment_tail_lt` gives
`F ∑_{j ≥ N_*} j^{5/2} ϱ^j < 162 N_*^{5/2} 2^{-23-535/8}`, and the exact comparison
`162^8 N_*^{20} 64^8 < 47^8 2^{535}` shows `162 N_*^{5/2} 2^{-535/8} < 47/64`.

## Main results

* `CollatzPosDens.generationThreshold_central_tail_lt`: the tail series is summable and
  `F ∑_{j ≥ N_*} j^{5/2} ϱ^j < (47/32) 2^{-24}`.

## Implementation notes

The tail is the sum over the subtype `Set.Ici N_*` of `ℕ`, with `j^{5/2}` the real power of the
cast; summability is part of the conclusion, so that the bound on the `tsum` is not vacuous.
The final comparison uses the exact value `N_* = 9766262` rather than the upper bound
`N_* ≤ 13 · 10^6`; both make the eighth-power comparison true.
-/

@[expose] public section

namespace CollatzPosDens

/-- `F ϱ^{N_*} ≤ 2^{-23-535/8}`. -/
private lemma errorPrefactor_mul_pow_generationThreshold_le :
    errorPrefactor * errorDecayRatio ^ generationThreshold ≤ (2 : ℝ) ^ (-23 - 535 / 8 : ℝ) := by
  have hδ := logGrowthRate_pos
  have hN := le_generationThreshold
  rw [div_le_iff₀ (by positivity), physicalExponent_def] at hN
  rw [errorDecayRatio_pow_eq_rpow, ← rpow_logGrowthRate, ← Real.rpow_mul (by norm_num),
    show errorPrefactor = (2 : ℝ) ^ Real.logb 2 errorPrefactor from
      (Real.rpow_logb (by norm_num) (by norm_num) errorPrefactor_pos).symm,
    ← Real.rpow_add (by norm_num)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith)

set_option exponentiation.threshold 600 in
/-- `162 N_*^{5/2} 2^{-535/8} < 47/64`, via the eighth-power comparison. -/
private lemma generationThreshold_central_tail_const :
    162 * ((generationThreshold : ℝ) ^ (5 / 2 : ℝ)) * (2 : ℝ) ^ (-535 / 8 : ℝ) < 47 / 64 := by
  rw [generationThreshold_eq]
  have h0 : 0 ≤ 162 * ((9766262 : ℕ) : ℝ) ^ (5 / 2 : ℝ) * (2 : ℝ) ^ (-535 / 8 : ℝ) := by
    positivity
  refine (pow_lt_pow_iff_left₀ h0 (by norm_num) (n := 8) (by norm_num)).1 ?_
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (_ ^ (5 / 2 : ℝ)),
    ← Real.rpow_natCast ((2 : ℝ) ^ _), ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by norm_num),
    show (5 / 2 : ℝ) * ((8 : ℕ) : ℝ) = ((20 : ℕ) : ℝ) by norm_num,
    show (-535 / 8 : ℝ) * ((8 : ℕ) : ℝ) = ((-535 : ℤ) : ℝ) by norm_num,
    Real.rpow_natCast, Real.rpow_intCast]
  norm_num

/-- **Central tail after `N_*`.** The series `∑_{j ≥ N_*} j^{5/2} ϱ^j` is summable and
`F ∑_{j ≥ N_*} j^{5/2} ϱ^j < (47/32) 2^{-24}`. -/
@[collatz_pos_dens "lem_Nstar_tail"]
theorem generationThreshold_central_tail_lt :
    Summable (fun j : Set.Ici generationThreshold =>
        ((j : ℕ) : ℝ) ^ (5 / 2 : ℝ) * errorDecayRatio ^ (j : ℕ)) ∧
      errorPrefactor * ∑' j : Set.Ici generationThreshold,
          ((j : ℕ) : ℝ) ^ (5 / 2 : ℝ) * errorDecayRatio ^ (j : ℕ) <
        47 / 32 * (2 : ℝ) ^ (-24 : ℤ) := by
  obtain ⟨hs, hlt⟩ := moment_tail_lt (d := 5 / 2) (by norm_num)
    (n := generationThreshold) (by rw [generationThreshold_eq]; norm_num)
  refine ⟨hs, ?_⟩
  have hsplit : (2 : ℝ) ^ (-23 - 535 / 8 : ℝ) = (2 : ℝ) ^ (-535 / 8 : ℝ) * 2 ^ (-23 : ℤ) := by
    rw [← Real.rpow_intCast, ← Real.rpow_add (by norm_num)]
    norm_num
  calc errorPrefactor * ∑' j : Set.Ici generationThreshold,
          ((j : ℕ) : ℝ) ^ (5 / 2 : ℝ) * errorDecayRatio ^ (j : ℕ)
      < errorPrefactor * (162 * ((generationThreshold : ℝ) ^ (5 / 2 : ℝ) *
          errorDecayRatio ^ generationThreshold)) := mul_lt_mul_of_pos_left hlt errorPrefactor_pos
    _ = 162 * (generationThreshold : ℝ) ^ (5 / 2 : ℝ) *
          (errorPrefactor * errorDecayRatio ^ generationThreshold) := by ring
    _ ≤ 162 * (generationThreshold : ℝ) ^ (5 / 2 : ℝ) * (2 : ℝ) ^ (-23 - 535 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left errorPrefactor_mul_pow_generationThreshold_le (by positivity)
    _ = (162 * (generationThreshold : ℝ) ^ (5 / 2 : ℝ) * (2 : ℝ) ^ (-535 / 8 : ℝ)) *
          2 ^ (-23 : ℤ) := by rw [hsplit]; ring
    _ < 47 / 64 * 2 ^ (-23 : ℤ) :=
        mul_lt_mul_of_pos_right generationThreshold_central_tail_const (by positivity)
    _ = 47 / 32 * (2 : ℝ) ^ (-24 : ℤ) := by norm_num

end CollatzPosDens
