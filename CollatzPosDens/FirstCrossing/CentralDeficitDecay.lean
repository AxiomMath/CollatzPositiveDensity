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
deficit rate `ς = 𝗀^{-9/8}`: for every `j ∈ ℕ`,
$$1 - \mathbf p(\mathcal C(b_j, K_j)) \le (1024 + 2^{-16})\,\varsigma^j.$$

First `ς^{-444} ≤ 2^{10}`, so for `j < 444` the bound is trivial. For `j = 444 + t`, the scale
`u = b_j` satisfies `u ≥ 16544 𝗀^t ≥ 16544 · 2^{⌊t/71⌋}`, hence `L = lg u ≥ 14 + ⌊t/71⌋ ≥ y`
with `y = 13 + t/71`, and `min(L², 32L) ≥ 169 + 26t/71`. The deficit bound for the central
family then gives `1 - 𝐩(𝒞(u, K_j)) ≤ 2e^{-169/30} e^{-26t/2130} + 2^{-(K_j+1)}`. Here
`2e^{-169/30} ≤ 1`, `e^{-26t/2130} ≤ 𝗀^{-9t/8} = ς^t ≤ 1024 ς^j` because `log 𝗀 ≤ 1/100`, and the
cap term is at most `2^{-16} ς^j`.

## Main results

* `CollatzPosDens.one_sub_geomMass_centralFamily_scale_cap_le_deficitRate_pow`: the bound
  above.

## Implementation notes

As in `CollatzPosDens.one_sub_geomMass_centralFamily_le`, the deficit is taken in `ℝ≥0∞`
(truncated subtraction), and the real right-hand side is embedded by `ENNReal.ofReal`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- `2^{-10} ≤ ς^{444}`. -/
private theorem centralDeficitDecay_rate_444 : (1 / 1024 : ℝ) ≤ deficitRate ^ 444 := by
  have h : deficitRate ^ 448 ≤ deficitRate ^ 444 :=
    pow_le_pow_of_le_one deficitRate_nonneg deficitRate_le_one (by norm_num)
  refine le_trans ?_ h
  rw [show 448 = 8 * 56 from rfl, pow_mul, deficitRate_pow_eight]
  norm_num

/-- `e^{-26t/2130} ≤ ς^t`. -/
private theorem centralDeficitDecay_exp_le (t : ℕ) :
    exp (-(26 * t / 2130)) ≤ deficitRate ^ t := by
  rw [deficitRate_pow_eq_rpow, Real.rpow_def_of_pos growthRatio_cast_pos]
  apply exp_le_exp.2
  have hlog : log (growthRatio : ℝ) ≤ 1 / 100 := by
    have := Real.log_le_sub_one_of_pos growthRatio_cast_pos
    rw [growthRatio_cast] at this ⊢
    linarith
  have hlog0 : 0 ≤ log (growthRatio : ℝ) := Real.log_nonneg one_lt_growthRatio_cast.le
  have ht : (0 : ℝ) ≤ t := t.cast_nonneg
  nlinarith

/-- For `j = 444 + t`, `exp(-min(L², 32L)/30) ≤ e^{-169/30} e^{-26t/2130}` with `L = lg b_j`. -/
private theorem centralDeficitDecay_exp_min_le (t : ℕ) :
    exp (-min ((lg (scale (444 + t)) : ℝ) ^ 2) (32 * (lg (scale (444 + t)) : ℝ)) / 30) ≤
      exp (-(169 / 30)) * exp (-(26 * t / 2130)) := by
  rw [← exp_add]
  apply exp_le_exp.2
  have hL := fourteen_add_div_seventy_one_le_lg_scale t
  have hdiv : t ≤ 71 * (t / 71) + 70 := by omega
  have hdivR : (t : ℝ) ≤ 71 * ((t / 71 : ℕ) : ℝ) + 70 := by exact_mod_cast hdiv
  have hLR : (14 : ℝ) + ((t / 71 : ℕ) : ℝ) ≤ lg (scale (444 + t)) := by exact_mod_cast hL
  set L : ℝ := ((lg (scale (444 + t)) : ℕ) : ℝ)
  have ht : (0 : ℝ) ≤ t := t.cast_nonneg
  have hyL : 13 + (t : ℝ) / 71 ≤ L := by linarith
  have hy : 13 ≤ 13 + (t : ℝ) / 71 := by linarith [div_nonneg ht (by norm_num : (0 : ℝ) ≤ 71)]
  have hm : 169 + 26 * t / 71 ≤ min (L ^ 2) (32 * L) := le_min (by nlinarith) (by linarith)
  linarith

/-- For `j = 444 + t`, `2 exp(-min(L², 32L)/30) ≤ 1024 ς^j` with `L = lg b_j`. -/
private theorem centralDeficitDecay_two_exp_min_le (t : ℕ) :
    2 * exp (-min ((lg (scale (444 + t)) : ℝ) ^ 2) (32 * (lg (scale (444 + t)) : ℝ)) / 30) ≤
      1024 * deficitRate ^ (444 + t) := by
  have h3 : 2 * exp (-(169 / 30)) ≤ 1 := by
    have := Real.add_one_le_exp (169 / 30)
    rw [exp_neg, mul_inv_le_iff₀ (exp_pos _)]
    linarith
  calc _ ≤ 2 * exp (-(169 / 30)) * exp (-(26 * t / 2130)) := by
        rw [mul_assoc]
        gcongr
        exact centralDeficitDecay_exp_min_le t
    _ ≤ 1 * deficitRate ^ t :=
      mul_le_mul h3 (centralDeficitDecay_exp_le t) (exp_pos _).le zero_le_one
    _ ≤ _ := by
      rw [one_mul, pow_add]
      nlinarith [centralDeficitDecay_rate_444, pow_pos deficitRate_pos t]

/-- **Decay of the central deficit**. For every `j ∈ ℕ`, the central family at scale `scale j` and
cap `cap j` satisfies `1 - 𝐩(𝒞(b_j, K_j)) ≤ (1024 + 2^{-16}) ς^j`. -/
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
    have : (0 : ℝ) ≤ (2 : ℝ) ^ (-16 : ℤ) * deficitRate ^ j := by positivity
    nlinarith [centralDeficitDecay_rate_444]
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
  have hu : 16384 ≤ scale (444 + t) := by
    have := scale_monotone (show 444 ≤ 444 + t by omega)
    rw [scale_444] at this
    omega
  refine (one_sub_geomMass_centralFamily_le hu (cap (444 + t))).trans ?_
  have hmain := centralDeficitDecay_two_exp_min_le t
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
