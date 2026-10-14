/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Clog
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.DeficitCentral
public import CollatzPosDens.FirstCrossing.FcCapRate
public import CollatzPosDens.FirstCrossing.ScalesB444
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.FirstCrossing.ScalesLateLower
public import CollatzPosDens.Recipe.Varsigma

/-!
# Decay of the central deficit along the scale sequence

Along the scales `b_j` and caps `K_j`, the geometric deficit of the central family decays at the
deficit rate `ς = 𝗀^{-3/2}`: for every `j ∈ ℕ`,
$$1 - \mathbf p(\mathcal C(b_j, K_j)) \le (1024 + 2^{-16})\,\varsigma^j.$$

First `ς^{-444} = 𝗀^{666} ≤ 2^{10}`, so for `j < 444` the bound is trivial. For `j = 444 + t`,
the scale `u = b_j` satisfies `u ≥ 16544 𝗀^t ≥ 16544 · 2^{⌊t/70⌋} > 2^{14 + ⌊t/70⌋}`, hence
`L = lg u ≥ 15 + ⌊t/70⌋ > y` with `y = 14 + t/70`, and `min(L², 32L) ≥ 30 (6 + 3t/200)`: the
quadratic `y² - (63/2) y + 261` has negative discriminant, and `32y/30 - 6 - (21/20)(y - 14)` is
positive for `y ≥ 14`. The deficit bound for the central family then gives
`1 - 𝐩(𝒞(u, K_j)) ≤ 2e^{-6} e^{-3t/200} + 2^{-(K_j+1)}`. Here `2e^{-6} ≤ 1`,
`e^{-3t/200} ≤ 𝗀^{-3t/2} = ς^t ≤ 1024 ς^j` because `log 𝗀 ≤ 1/100`, and the cap term is at most
`2^{-16} ς^j`.

## Main results

* `CollatzPosDens.one_sub_geomMass_centralFamily_scale_cap_le_deficitRate_pow`: the bound
  above.

## Implementation notes

As in `CollatzPosDens.one_sub_geomMass_centralFamily_le`, the deficit is taken in `ℝ≥0∞`
(truncated subtraction), and the real right-hand side is embedded by `ENNReal.ofReal`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- `2^{-10} ≤ ς^{444}`, i.e. `101^{666} ≤ 2^{10} · 100^{666}`. -/
private theorem centralDeficitDecay_rate_444 : (1 / 1024 : ℝ) ≤ deficitRate ^ 444 := by
  rw [show 444 = 2 * 222 from rfl, pow_mul, deficitRate_pow_two, ← pow_mul, div_pow,
    le_div_iff₀ (by positivity), div_mul_eq_mul_div, div_le_iff₀ (by norm_num), one_mul]
  have h : (101 ^ (3 * 222) : ℕ) ≤ 100 ^ (3 * 222) * 1024 := by decide +kernel
  exact_mod_cast h

/-- `e^{-3t/200} ≤ ς^t`. -/
private theorem centralDeficitDecay_exp_le (t : ℕ) :
    exp (-(3 * t / 200)) ≤ deficitRate ^ t := by
  rw [deficitRate_pow_eq_rpow, Real.rpow_def_of_pos growthRatio_cast_pos]
  apply exp_le_exp.2
  have hlog : log (growthRatio : ℝ) ≤ 1 / 100 := by
    have := Real.log_le_sub_one_of_pos growthRatio_cast_pos
    rw [growthRatio_cast] at this ⊢
    linarith
  have hlog0 : 0 ≤ log (growthRatio : ℝ) := Real.log_nonneg one_lt_growthRatio_cast.le
  have ht : (0 : ℝ) ≤ t := t.cast_nonneg
  nlinarith

/-- For `j = 444 + t`, `15 + ⌊t/70⌋ ≤ lg b_j`. -/
private theorem centralDeficitDecay_lg_scale (t : ℕ) :
    15 + t / 70 ≤ lg (scale (444 + t)) := by
  have hg : (growthRatio : ℝ) ^ t * 16544 ≤ scale (444 + t) := by
    have := scale_add_ge_growthRatio_pow_mul 444 t
    rwa [scale_444, Nat.cast_ofNat] at this
  have h2 : (2 : ℝ) ^ (t / 70) ≤ (growthRatio : ℝ) ^ t := by
    calc (2 : ℝ) ^ (t / 70) ≤ ((growthRatio : ℝ) ^ 70) ^ (t / 70) := by
          gcongr; rw [growthRatio_cast]; norm_num
      _ = (growthRatio : ℝ) ^ (70 * (t / 70)) := by rw [pow_mul]
      _ ≤ (growthRatio : ℝ) ^ t :=
          pow_le_pow_right₀ one_lt_growthRatio_cast.le (Nat.mul_div_le t 70)
  have hlt : ((2 ^ (14 + t / 70) : ℕ) : ℝ) < scale (444 + t) := by
    push_cast
    rw [pow_add]
    have : (0 : ℝ) < 2 ^ (t / 70) := by positivity
    nlinarith
  have hlt' : 2 ^ (14 + t / 70) < scale (444 + t) := by exact_mod_cast hlt
  by_contra h
  have := lg_le_iff_le_two_pow.1 (show lg (scale (444 + t)) ≤ 14 + t / 70 by omega)
  omega

/-- For `j = 444 + t`, `exp(-min(L², 32L)/30) ≤ e^{-6} e^{-3t/200}` with `L = lg b_j`. -/
private theorem centralDeficitDecay_exp_min_le (t : ℕ) :
    exp (-min ((lg (scale (444 + t)) : ℝ) ^ 2) (32 * (lg (scale (444 + t)) : ℝ)) / 30) ≤
      exp (-6) * exp (-(3 * t / 200)) := by
  rw [← exp_add]
  apply exp_le_exp.2
  have hL := centralDeficitDecay_lg_scale t
  have hdiv : t ≤ 70 * (t / 70) + 69 := by omega
  have hdivR : (t : ℝ) ≤ 70 * ((t / 70 : ℕ) : ℝ) + 69 := by exact_mod_cast hdiv
  have hLR : (15 : ℝ) + ((t / 70 : ℕ) : ℝ) ≤ lg (scale (444 + t)) := by exact_mod_cast hL
  set L : ℝ := ((lg (scale (444 + t)) : ℕ) : ℝ)
  have ht : (0 : ℝ) ≤ t := t.cast_nonneg
  set y : ℝ := 14 + (t : ℝ) / 70 with hy_def
  have hyL : y ≤ L := by rw [hy_def]; linarith
  have hy : 14 ≤ y := by rw [hy_def]; linarith [div_nonneg ht (by norm_num : (0 : ℝ) ≤ 70)]
  have ht' : (t : ℝ) = 70 * (y - 14) := by rw [hy_def]; ring
  have hm : 30 * (6 + 3 * t / 200) ≤ min (L ^ 2) (32 * L) := by
    rw [ht']
    refine le_min ?_ ?_
    · nlinarith [sq_nonneg (y - 63 / 4), mul_le_mul hyL hyL (by linarith) (by linarith)]
    · linarith
  linarith

/-- **Decay of the central deficit.** For every `j ∈ ℕ`,
`1 - 𝐩(𝒞(b_j, K_j)) ≤ (1024 + 2^{-16}) ς^j`. -/
@[collatz_pos_dens "lem_central_deficit_decay"]
theorem one_sub_geomMass_centralFamily_scale_cap_le_deficitRate_pow (j : ℕ) :
    1 - geomMass (centralFamily (scale j) (cap j)) ≤
      ENNReal.ofReal ((1024 + (2 : ℝ) ^ (-16 : ℤ)) * deficitRate ^ j) := by
  have hς := deficitRate_pos
  rcases lt_or_ge j 444 with hj | hj
  · refine tsub_le_self.trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have h1 : deficitRate ^ 444 ≤ deficitRate ^ j :=
      pow_le_pow_of_le_one deficitRate_nonneg deficitRate_le_one hj.le
    have h2 := centralDeficitDecay_rate_444
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (-16 : ℤ) * deficitRate ^ j := by positivity
    nlinarith
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hu : 16384 ≤ scale (444 + t) := by
    have := scale_monotone (show 444 ≤ 444 + t by omega)
    rw [scale_444] at this
    omega
  refine (one_sub_geomMass_centralFamily_le hu (cap (444 + t))).trans ?_
  -- the main term
  have hmain : 2 * exp (-min ((lg (scale (444 + t)) : ℝ) ^ 2)
      (32 * (lg (scale (444 + t)) : ℝ)) / 30) ≤ 1024 * deficitRate ^ (444 + t) := by
    have h3 : 2 * exp (-6) ≤ 1 := by
      have := Real.add_one_le_exp 6
      rw [exp_neg, mul_inv_le_iff₀ (exp_pos _)]
      linarith
    have h4 : deficitRate ^ t ≤ 1024 * deficitRate ^ (444 + t) := by
      rw [pow_add]
      have := centralDeficitDecay_rate_444
      have : 0 < deficitRate ^ t := by positivity
      nlinarith
    calc _ ≤ 2 * exp (-6) * exp (-(3 * t / 200)) := by
          rw [mul_assoc]
          gcongr
          exact centralDeficitDecay_exp_min_le t
      _ ≤ 1 * deficitRate ^ t :=
        mul_le_mul h3 (centralDeficitDecay_exp_le t) (exp_pos _).le zero_le_one
      _ ≤ _ := (one_mul _).le.trans h4
  -- the cap term
  have hcap : (2⁻¹ : ℝ≥0∞) ^ (cap (444 + t) + 1) =
      ENNReal.ofReal ((2 : ℝ) ^ (-((cap (444 + t) : ℤ) + 1))) := by
    rw [show -((cap (444 + t) : ℤ) + 1) = -((cap (444 + t) + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, ← inv_pow, ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  have hc := two_zpow_neg_cap_succ_le (444 + t)
  rw [hcap, add_mul, ENNReal.ofReal_add (by positivity) (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
  gcongr

end CollatzPosDens
