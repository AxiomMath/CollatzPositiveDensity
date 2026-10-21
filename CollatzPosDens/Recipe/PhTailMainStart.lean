/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.PhEmx
public import CollatzPosDens.Recipe.PhBootUUpper
public import CollatzPosDens.Recipe.PhBootVUpper
public import CollatzPosDens.Recipe.PhLogRatio
public import CollatzPosDens.Recipe.PhLogTwo
public import CollatzPosDens.Transfer.S02Log2Bstar

/-!
# The mixing majorant at the generation threshold

At the generation threshold `N_* = 9853` the mixing part of the propagation majorant satisfies
$$\mathsf E^{\mathrm{mx}}_{N_*} < \frac{7583}{10^6}.$$

Writing `N = N_*`, `𝓗 = 𝓗_hist = 344`, `a = a_mx(b) = 29/20` and `γ = a - 1/2 = 19/20`, one
has `E_N^mx = 36 𝓗 N^{5/2} (u_b (12 log 2 + N log 𝗀) + v_b) e^Λ` with
`Λ = (log₂ B_F(b)) log 2 - 12 a log 2 - γ N log 𝗀`. The enclosures of `log 2`, `log 𝗀` and
`log₂ B_F(b)` give `Λ < -x₀` for `x₀ = 44119/10^3`; the exponential partial sum of order `20`
at `x₀/64`, raised to the `64`-th power, gives `e^{x₀} ≥ σ = 1446 · 10^16`; finally
`√N ≤ 992623/10^4`, `u_b (12 log 2 + N log 𝗀) + v_b < 9187513/10^4` by the upper bounds of
`u_b` and `v_b`, and an exact rational comparison closes the bound.

## Main results

* `CollatzPosDens.propagationMixingMajorant_generationThreshold_lt`:
  `E^mx_{N_*} < 7583 / 10^6`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The exponential lower bound `σ = 1446 · 10^16 ≤ e^{44119/10^3}`, from the partial
sum of order `20` of the exponential series at `44119/(64·10^3)`. -/
private theorem exp_tailMainStart_ge :
    (14460000000000000000 : ℝ) ≤ exp (44119 / 10 ^ 3) := by
  have hS := Real.sum_le_exp_of_nonneg (x := (44119 / 10 ^ 3 / 64 : ℝ)) (by norm_num) 21
  have hr : (1992438 / 10 ^ 6 : ℝ) ≤ exp (44119 / 10 ^ 3 / 64) := by
    refine le_trans ?_ hS
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hpow : exp (44119 / 10 ^ 3 : ℝ) = exp (44119 / 10 ^ 3 / 64) ^ 64 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hpow]
  calc (14460000000000000000 : ℝ) ≤ (1992438 / 10 ^ 6 : ℝ) ^ 64 := by norm_num
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) hr 64

/-- The exponential factor of `E^mx_{N_*}`:
`B_F(b) 2^{-12 a_mx(b)} 𝗀^{-(a_mx(b) - 1/2) N_*} < 1/σ` with `σ = 1446 · 10^16`. -/
private theorem tailMainStart_expFactor_lt :
    fourierPrefactor .b * (2 : ℝ) ^ (-(12 * (amix .b : ℝ))) *
        (growthRatio : ℝ) ^ (-(((amix .b : ℝ) - 1 / 2) * (9853 : ℕ))) <
      1 / 14460000000000000000 := by
  obtain ⟨hb0, hb⟩ := logb_two_fourierPrefactor_mem_b
  obtain ⟨l2a, l2b⟩ := log_two_mem_Ioo_d15
  obtain ⟨lg, -⟩ := log_growthRatio_mem_Ioo
  have hl2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  have hlogB : log (fourierPrefactor .b) = logb 2 (fourierPrefactor .b) * log 2 := by
    rw [logb, div_mul_cancel₀ _ hl2.ne']
  have hprod : logb 2 (fourierPrefactor .b) * log 2 <
      881188851177 / 10 ^ 10 * (693147180559946 / 10 ^ 15) := by
    calc logb 2 (fourierPrefactor .b) * log 2 < 881188851177 / 10 ^ 10 * log 2 :=
          mul_lt_mul_of_pos_right hb hl2
      _ < _ := mul_lt_mul_of_pos_left l2b (by norm_num)
  have heq : fourierPrefactor .b * (2 : ℝ) ^ (-(12 * (amix .b : ℝ))) *
        (growthRatio : ℝ) ^ (-(((amix .b : ℝ) - 1 / 2) * (9853 : ℕ))) =
      exp (log (fourierPrefactor .b) + log 2 * (-(12 * (amix .b : ℝ))) +
        log (growthRatio : ℝ) * (-(((amix .b : ℝ) - 1 / 2) * (9853 : ℕ)))) := by
    rw [exp_add, exp_add, exp_log (fourierPrefactor_pos .b), ← rpow_def_of_pos (by norm_num),
      ← rpow_def_of_pos growthRatio_cast_pos]
  rw [heq, amix_cast_b]
  have hΛ : log (fourierPrefactor .b) + log 2 * (-(12 * (29 / 20 : ℝ))) +
      log (growthRatio : ℝ) * (-((29 / 20 - 1 / 2) * ((9853 : ℕ) : ℝ))) <
        -(44119 / 10 ^ 3) := by
    rw [hlogB]; push_cast; nlinarith
  calc exp _ < exp (-(44119 / 10 ^ 3)) := exp_lt_exp.mpr hΛ
    _ = 1 / exp (44119 / 10 ^ 3) := by rw [exp_neg, one_div]
    _ ≤ 1 / 14460000000000000000 :=
        one_div_le_one_div_of_le (by norm_num) exp_tailMainStart_ge

/-- `N_*^{5/2} ≤ N_*^2 · 992623/10^4`, since `(992623/10^4)^2 ≥ N_*`. -/
private theorem tailMainStart_rpow_le :
    ((9853 : ℕ) : ℝ) ^ (5 / 2 : ℝ) ≤ (9853 : ℝ) ^ 2 * (992623 / 10 ^ 4) := by
  have hsplit : ((9853 : ℕ) : ℝ) ^ (5 / 2 : ℝ) = (9853 : ℝ) ^ 2 * sqrt 9853 := by
    rw [sqrt_eq_rpow, ← rpow_natCast, ← rpow_add (by norm_num)]; norm_num
  rw [hsplit]
  gcongr
  rw [sqrt_le_left (by norm_num)]
  norm_num

/-- **The mixing majorant at the generation threshold.** `E^mx_{N_*} < 7583 / 10^6`. -/
@[collatz_pos_dens "lem_ph_tail_main_start"]
theorem propagationMixingMajorant_generationThreshold_lt :
    propagationMixingMajorant generationThreshold < 7583 / 10 ^ 6 := by
  rw [generationThreshold_def, propagationMixingMajorant_def, Hhist_cast]
  obtain ⟨-, l2⟩ := log_two_mem_Ioo_d15
  obtain ⟨-, lg⟩ := log_growthRatio_mem_Ioo
  obtain ⟨hu0, hu1⟩ := bootU_mem_Ioo
  obtain ⟨hv0, hv1⟩ := bootV_mem_Ioo
  have hL := twelve_mul_log_two_add_mul_log_growthRatio_pos 9853
  have hLpos := bootU_mul_log_add_bootV_pos 9853
  have hLup : 12 * log 2 + ((9853 : ℕ) : ℝ) * log (growthRatio : ℝ) <
      12 * (693147180559946 / 10 ^ 15) + 9853 * (9950330853169 / 10 ^ 15) := by
    push_cast; linarith
  have hAff : bootU .b * (12 * log 2 + ((9853 : ℕ) : ℝ) * log (growthRatio : ℝ)) + bootV .b <
      9187513 / 10 ^ 4 := by
    have h1 : bootU .b * (12 * log 2 + ((9853 : ℕ) : ℝ) * log (growthRatio : ℝ)) <
        857945620 / 10 ^ 8 *
          (12 * (693147180559946 / 10 ^ 15) + 9853 * (9950330853169 / 10 ^ 15)) :=
      mul_lt_mul'' hu1 hLup hu0.le hL.le
    have h2 : (857945620 / 10 ^ 8 : ℝ) *
        (12 * (693147180559946 / 10 ^ 15) + 9853 * (9950330853169 / 10 ^ 15)) +
          624902664 / 10 ^ 8 <
        9187513 / 10 ^ 4 := by norm_num
    linarith
  have hE := tailMainStart_expFactor_lt
  have hEpos : 0 < fourierPrefactor .b * (2 : ℝ) ^ (-(12 * (amix .b : ℝ))) *
      (growthRatio : ℝ) ^ (-(((amix .b : ℝ) - 1 / 2) * (9853 : ℕ))) :=
    mul_pos (mul_pos (fourierPrefactor_pos .b) (rpow_pos_of_pos (by norm_num) _))
      (rpow_pos_of_pos growthRatio_cast_pos _)
  have hR := tailMainStart_rpow_le
  have hRpos : 0 < ((9853 : ℕ) : ℝ) ^ (5 / 2 : ℝ) := rpow_pos_of_pos (by norm_num) _
  set e := fourierPrefactor .b * (2 : ℝ) ^ (-(12 * (amix .b : ℝ))) *
      (growthRatio : ℝ) ^ (-(((amix .b : ℝ) - 1 / 2) * (9853 : ℕ))) with he
  set R := ((9853 : ℕ) : ℝ) ^ (5 / 2 : ℝ)
  set L := bootU .b * (12 * log 2 + ((9853 : ℕ) : ℝ) * log (growthRatio : ℝ)) + bootV .b
  calc 36 * (344 : ℝ) * fourierPrefactor .b * (2 : ℝ) ^ (-(12 * (amix .b : ℝ))) * R *
        (growthRatio : ℝ) ^ (-(((amix .b : ℝ) - 1 / 2) * (9853 : ℕ))) * L =
        36 * 344 * R * L * e := by rw [he]; ring
    _ ≤ 36 * 344 * ((9853 : ℝ) ^ 2 * (992623 / 10 ^ 4)) *
          (9187513 / 10 ^ 4) * e := by
        gcongr
    _ < 36 * 344 * ((9853 : ℝ) ^ 2 * (992623 / 10 ^ 4)) *
          (9187513 / 10 ^ 4) * (1 / 14460000000000000000) := by gcongr
    _ < 7583 / 10 ^ 6 := by norm_num

end CollatzPosDens
