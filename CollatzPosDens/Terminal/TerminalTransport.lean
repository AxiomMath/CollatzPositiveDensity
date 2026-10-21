/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FcCapRate
public import CollatzPosDens.FirstCrossing.LevelLateLower
public import CollatzPosDens.FirstCrossing.ScalesLateLower
public import CollatzPosDens.Mixing.MxProfileAntitone
public import CollatzPosDens.Recipe.NstarGate
public import CollatzPosDens.Recipe.NstarRange
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Terminal.LengthRemoved
public import CollatzPosDens.Terminal.MarkedMass
public import CollatzPosDens.Terminal.S06Tj
public import CollatzPosDens.Terminal.S06UnfilteredError

/-!
# Terminal error

Let `t ≥ t_min` be an odd integer, `j ≥ J_c` (`J_c = covGen`) and `X` admissible for
generation `j`. Then the marked mass and the weighted central sum are close:
$$\bigl|\Theta_{j,X}(t) - Z_j(t)\bigr| \le \mathsf T_j,$$
where `T_j` is the terminal majorant.

By the triangle inequality,
$|\Theta_{j,X}(t) - Z_j(t)| \le |\Theta^{\circ}_{j,X}(t) - Z_j(t)|
  + |\Theta^{\circ}_{j,X}(t) - \Theta_{j,X}(t)|$.
The first term is bounded by the error of the unfiltered marked mass, and the second, which is
nonnegative, by the estimate for the mass removed by the length condition; together they are at
most `5 j^{9/2} 𝗀^{j/2} (2 𝔐_o(k_j) + (2^{116} + 2^{113}) b_j^{-6} + 2^{-(K_j+1)})`. The
three summands are then compared with those of `T_j`: the mixing profile `𝔐_o` at the original
Fourier index `o` is antitone beyond the gate level and `k_j ≥ 2^{12} 𝗀^j > n_0`; the scales
satisfy `b_j ≥ 16544 𝗀^j ≥ 2^{14} 𝗀^j`, so that
`(2^{116} + 2^{113}) b_j^{-6} ≤ (2^{32} + 2^{29}) 𝗀^{-6j}`; and the cap satisfies
`2^{-(K_j+1)} ≤ 2^{-29} 2^{-j/56}`.

## Main results

* `CollatzPosDens.abs_markedMass_sub_weightedCentralSum_le`: the bound
  `|Θ_{j,X}(t) - Z_j(t)| ≤ T_j`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For an odd integer `t ≥ t_min`, `j ≥ J_c` and `X` admissible for generation `j`, the marked
mass and the weighted central sum satisfy `|Θ_{j,X}(t) - Z_j(t)| ≤ T_j`. -/
@[collatz_pos_dens "lem_terminal_transport"]
theorem abs_markedMass_sub_weightedCentralSum_le {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) {j : ℕ} (hj : covGen ≤ j) {X : ℝ}
    (hX : IsAdmissibleScale t j X) :
    |markedMass j X t - weightedCentralSum j t| ≤ terminalMajorant j := by
  have h1 := abs_markedMassUnfiltered_sub_weightedCentralSum_le hodd ht hj hX
  have h2 := markedMassUnfiltered_sub_markedMass_le hodd ht hj X
  have h3 := markedMassUnfiltered_sub_markedMass_nonneg j X t
  have hjN : generationThreshold ≤ j := selEnd_le_generationThreshold_range.2.trans hj
  set P : ℝ := 5 * (j : ℝ) ^ (9 / 2 : ℝ) * (growthRatio : ℝ) ^ ((j : ℝ) / 2) with hP
  have hg := growthRatio_cast_pos
  have hP0 : 0 ≤ P := by positivity
  have htri : |markedMass j X t - weightedCentralSum j t| ≤
      P * (2 * mxProfile .o (level j) + 2 ^ 116 / (scale j : ℝ) ^ 6 + 2⁻¹ ^ (cap j + 1)) +
        P * (2 ^ 113 / (scale j : ℝ) ^ 6) := by
    rw [abs_le] at h1 ⊢
    constructor <;> linarith [h1.1, h1.2]
  refine htri.trans ?_
  rw [terminalMajorant_def, ← hP, ← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ hP0
  have hgj : (growthRatio : ℝ) ^ (j : ℝ) = (growthRatio : ℝ) ^ j := Real.rpow_natCast _ _
  have hmix : mxProfile .o (level j) ≤
      mxProfile .o (2 ^ 12 * (growthRatio : ℝ) ^ (j : ℝ)) := by
    rw [hgj]
    refine mxProfile_antitoneOn .o ?_ ((le_max_right _ _).trans (level_late_lower hjN))
    have hmono : (growthRatio : ℝ) ^ generationThreshold ≤ (growthRatio : ℝ) ^ j :=
      pow_le_pow_right₀ one_lt_growthRatio_cast.le hjN
    exact (mxGateLevel_lt_two_pow_twelve_mul_growthRatio_pow.trans_le
      (mul_le_mul_of_nonneg_left hmono (by norm_num))).le
  have hb : 2 ^ 14 * (growthRatio : ℝ) ^ j ≤ scale j := by
    have := scale_late_lower j
    have hgpos : 0 < (growthRatio : ℝ) ^ j := pow_pos hg j
    nlinarith
  have hdef : 2 ^ 116 / (scale j : ℝ) ^ 6 + 2 ^ 113 / (scale j : ℝ) ^ 6 ≤
      (2 ^ 32 + 2 ^ 29) * (growthRatio : ℝ) ^ (-(6 * (j : ℝ))) := by
    have e4 : (growthRatio : ℝ) ^ (-(6 * (j : ℝ))) = (((growthRatio : ℝ) ^ j) ^ 6)⁻¹ := by
      rw [Real.rpow_neg hg.le, ← pow_mul, mul_comm j 6]
      norm_cast
    have hs : 0 < 2 ^ 14 * (growthRatio : ℝ) ^ j := by positivity
    calc 2 ^ 116 / (scale j : ℝ) ^ 6 + 2 ^ 113 / (scale j : ℝ) ^ 6
        = (2 ^ 116 + 2 ^ 113) / (scale j : ℝ) ^ 6 := by rw [add_div]
      _ ≤ (2 ^ 116 + 2 ^ 113) / (2 ^ 14 * (growthRatio : ℝ) ^ j) ^ 6 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hs.le hb 6)
      _ = (2 ^ 32 + 2 ^ 29) * (((growthRatio : ℝ) ^ j) ^ 6)⁻¹ := by
        rw [mul_pow, div_eq_mul_inv, mul_inv, ← mul_assoc]
        norm_num
      _ = _ := by rw [e4]
  have hcap : (2 : ℝ)⁻¹ ^ (cap j + 1) ≤
      (2 : ℝ) ^ (-29 : ℝ) * (2 : ℝ) ^ (-((j : ℝ) / 56)) := by
    have h := two_zpow_neg_cap_succ_le j
    have e1 : (2 : ℝ)⁻¹ ^ (cap j + 1) = (2 : ℝ) ^ (-((cap j : ℤ) + 1)) := by
      rw [inv_pow, zpow_neg]; norm_cast
    have e2 : (2 : ℝ) ^ (-29 : ℝ) = (2 : ℝ) ^ (-29 : ℤ) := by
      rw [← Real.rpow_intCast]; norm_num
    rw [e1, e2]
    exact h
  calc 2 * mxProfile .o (level j) + 2 ^ 116 / (scale j : ℝ) ^ 6 + 2⁻¹ ^ (cap j + 1) +
        2 ^ 113 / (scale j : ℝ) ^ 6
      = 2 * mxProfile .o (level j) + (2 ^ 116 / (scale j : ℝ) ^ 6 +
        2 ^ 113 / (scale j : ℝ) ^ 6) + 2⁻¹ ^ (cap j + 1) := by ring
    _ ≤ _ := by gcongr

end CollatzPosDens
