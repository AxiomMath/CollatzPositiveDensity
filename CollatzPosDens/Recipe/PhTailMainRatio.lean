/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.PhEmx
public import CollatzPosDens.Recipe.PhLogRatio

/-!
# The ratio bound for the mixing part of the propagation majorant

For every integer `j ≥ N_* = 9853` the mixing part `E_j^mx` of the propagation majorant
decays geometrically:
$$\mathsf E^{\mathrm{mx}}_{j+1} \le \frac{990945}{10^6}\,\mathsf E^{\mathrm{mx}}_j.$$

Write `γ = a_mx(b) - 1/2 = 19/20`, `ℓ = 12 log 2`, `λ = log 𝗀`, `P = u_b ℓ + v_b > 0` and
`Q = u_b λ > 0`. The quotient `E_{j+1}^mx / E_j^mx` equals
`(1 + 1/j)^{5/2} 𝗀^{-γ} (P + (j+1)Q)/(P + jQ)`, and the affine factor is at most `1 + 1/j`
because `P ≥ 0`. Hence the quotient is at most `exp((7/2) log(1 + 1/j) - γλ) ≤ exp(-y₀)` with
`y₀ = 9097/10^6`, using `log(1 + s) ≤ s` and the enclosure
`CollatzPosDens.log_growthRatio_mem_Ioo` of `λ`. Finally `exp y₀` is bounded below by its Taylor
polynomial `S` of degree `4`, and `(990945/10^6) S ≥ 1`.

## Main results

* `CollatzPosDens.propagationMixingMajorant_succ_le`: for `N_* ≤ j`,
  `E_{j+1}^mx ≤ (990945/10^6) E_j^mx`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The ratio factor `(1 + 1/j)^{7/2} 𝗀^{-(a_mx(b) - 1/2)}` is at most `990945/10^6` for
`N_* ≤ j`. -/
private lemma one_add_inv_rpow_mul_growthRatio_rpow_le {j : ℕ} (hj : generationThreshold ≤ j) :
    (1 + 1 / (j : ℝ)) ^ (7 / 2 : ℝ) * (growthRatio : ℝ) ^ (-((amix .b : ℝ) - 1 / 2)) ≤
      990945 / 10 ^ 6 := by
  rw [generationThreshold_def] at hj
  have hj' : (9853 : ℝ) ≤ j := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < j := by linarith
  have hu : (0 : ℝ) < 1 + 1 / (j : ℝ) := by positivity
  have hlogu : log (1 + 1 / (j : ℝ)) ≤ 1 / 9853 := by
    refine (log_le_sub_one_of_pos hu).trans ?_
    rw [add_sub_cancel_left]
    exact one_div_le_one_div_of_le (by norm_num) hj'
  have hlam := (log_growthRatio_mem_Ioo).1
  rw [rpow_def_of_pos hu, rpow_def_of_pos growthRatio_cast_pos, ← exp_add, amix_cast_b]
  set y₀ : ℝ := 9097 / 10 ^ 6
  have hexp : rexp (log (1 + 1 / (j : ℝ)) * (7 / 2) +
      log (growthRatio : ℝ) * -(29 / 20 - 1 / 2)) ≤ rexp (-y₀) := by
    apply exp_le_exp.2
    simp only [y₀]
    nlinarith
  have hS := sum_le_exp_of_nonneg (x := y₀) (by positivity) 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hS
  refine hexp.trans ?_
  rw [exp_neg, inv_le_iff_one_le_mul₀ (exp_pos _)]
  have hpos : (0 : ℝ) ≤ 990945 / 10 ^ 6 := by norm_num
  refine le_trans ?_ (mul_le_mul_of_nonneg_left hS hpos)
  simp only [y₀]
  norm_num

/-- **Ratio bound for `E_j^mx`.** For every integer `j ≥ N_*`,
`E_{j+1}^mx ≤ (990945/10^6) E_j^mx`. -/
@[collatz_pos_dens "lem_ph_tail_main_ratio"]
theorem propagationMixingMajorant_succ_le {j : ℕ} (hj : generationThreshold ≤ j) :
    propagationMixingMajorant (j + 1) ≤ 990945 / 10 ^ 6 * propagationMixingMajorant j := by
  have hj1 : 1 ≤ j := le_trans (by rw [generationThreshold_def]; decide) hj
  have hjpos : (0 : ℝ) < j := by exact_mod_cast hj1
  have key := one_add_inv_rpow_mul_growthRatio_rpow_le hj
  set u : ℝ := 1 + 1 / (j : ℝ) with hu_def
  have hu : 0 < u := by positivity
  set P : ℝ := 36 * (Hhist : ℝ) * fourierPrefactor .b * (2 : ℝ) ^ (-(12 * (amix .b : ℝ)))
  have hP : 0 < P := by
    have hH : (0 : ℝ) < Hhist := by exact_mod_cast Hhist_pos
    exact mul_pos (mul_pos (mul_pos (by norm_num) hH) (fourierPrefactor_pos .b))
      (rpow_pos_of_pos (by norm_num) _)
  set g : ℝ := (growthRatio : ℝ)
  have hg : 0 < g := growthRatio_cast_pos
  set γ : ℝ := (amix .b : ℝ) - 1 / 2
  set ℓ : ℝ := 12 * log 2
  set lam : ℝ := log g
  have hℓ : 0 ≤ ℓ := mul_nonneg (by norm_num) (log_nonneg (by norm_num))
  have hL := bootU_mul_log_add_bootV_pos j
  have hU := bootU_pos .b
  have hV := bootV_pos .b
  have hcast : ((j + 1 : ℕ) : ℝ) = j * u := by
    push_cast; rw [hu_def]; field_simp
  have hpow : ((j + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) = (j : ℝ) ^ (5 / 2 : ℝ) * u ^ (5 / 2 : ℝ) := by
    rw [hcast, mul_rpow hjpos.le hu.le]
  have hgpow : g ^ (-(γ * ((j + 1 : ℕ) : ℝ))) = g ^ (-(γ * j)) * g ^ (-γ) := by
    rw [← rpow_add hg]; congr 1; push_cast; ring
  have hu72 : u ^ (7 / 2 : ℝ) = u ^ (5 / 2 : ℝ) * u := by
    rw [show (7 / 2 : ℝ) = 5 / 2 + 1 by norm_num, rpow_add hu, rpow_one]
  have haff : bootU .b * (ℓ + ((j + 1 : ℕ) : ℝ) * lam) + bootV .b ≤
      u * (bootU .b * (ℓ + j * lam) + bootV .b) := by
    rw [hu_def]; push_cast
    rw [← sub_nonneg]
    have : (1 + 1 / (j : ℝ)) * (bootU .b * (ℓ + j * lam) + bootV .b) -
        (bootU .b * (ℓ + (j + 1) * lam) + bootV .b) = (bootU .b * ℓ + bootV .b) / j := by
      field_simp; ring
    rw [this]
    exact div_nonneg (by positivity) hjpos.le
  rw [propagationMixingMajorant_def, propagationMixingMajorant_def]
  change P * ((j + 1 : ℕ) : ℝ) ^ (5 / 2 : ℝ) * g ^ (-(γ * ((j + 1 : ℕ) : ℝ))) *
      (bootU .b * (ℓ + ((j + 1 : ℕ) : ℝ) * lam) + bootV .b) ≤
    990945 / 10 ^ 6 * (P * (j : ℝ) ^ (5 / 2 : ℝ) * g ^ (-(γ * j)) *
      (bootU .b * (ℓ + j * lam) + bootV .b))
  rw [hpow, hgpow]
  have hA : 0 < P * (j : ℝ) ^ (5 / 2 : ℝ) * g ^ (-(γ * j)) :=
    mul_pos (mul_pos hP (rpow_pos_of_pos hjpos _)) (rpow_pos_of_pos hg _)
  have hu52 : 0 < u ^ (5 / 2 : ℝ) := rpow_pos_of_pos hu _
  have hgγ : 0 < g ^ (-γ) := rpow_pos_of_pos hg _
  calc P * ((j : ℝ) ^ (5 / 2 : ℝ) * u ^ (5 / 2 : ℝ)) * (g ^ (-(γ * j)) * g ^ (-γ)) *
        (bootU .b * (ℓ + ((j + 1 : ℕ) : ℝ) * lam) + bootV .b)
      = (P * (j : ℝ) ^ (5 / 2 : ℝ) * g ^ (-(γ * j))) * (u ^ (5 / 2 : ℝ) * g ^ (-γ)) *
          (bootU .b * (ℓ + ((j + 1 : ℕ) : ℝ) * lam) + bootV .b) := by ring
    _ ≤ (P * (j : ℝ) ^ (5 / 2 : ℝ) * g ^ (-(γ * j))) * (u ^ (5 / 2 : ℝ) * g ^ (-γ)) *
          (u * (bootU .b * (ℓ + j * lam) + bootV .b)) := by gcongr
    _ = (u ^ (7 / 2 : ℝ) * g ^ (-γ)) *
          (P * (j : ℝ) ^ (5 / 2 : ℝ) * g ^ (-(γ * j)) * (bootU .b * (ℓ + j * lam) + bootV .b)) := by
          rw [hu72]; ring
    _ ≤ 990945 / 10 ^ 6 *
          (P * (j : ℝ) ^ (5 / 2 : ℝ) * g ^ (-(γ * j)) * (bootU .b * (ℓ + j * lam) + bootV .b)) := by
          gcongr

end CollatzPosDens
