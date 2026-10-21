/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.BlackSet.BkDrift
public import CollatzPosDens.BlackSet.BkAlphaBounds
public import CollatzPosDens.Case3.C3AlphaUpper
public import CollatzPosDens.Transfer.S02Xd
public import CollatzPosDens.Transfer.S02Xl
public import CollatzPosDens.Transfer.S02Wtot
public import CollatzPosDens.Transfer.S02OmegaLower
public import CollatzPosDens.Transfer.S02NearGateV

/-!
# The triangle margin at a far gap

Let `ι ∈ {o, b}` be a Fourier index, let `v < V_*(ι)` be a natural number and let `ω` be a real
number with `ω ≥ Ω_far(ι)`. Then
$$\tfrac{\omega}{32} + X_d(ι, v) + \tfrac14 X_l(ι, v) + \alpha W(ι, v) + 1
  \le \omega \, \delta_0 .$$
The allowances `X_d(ι, ·)`, `X_l(ι, ·)`, `W(ι, ·)` are nonnegative and nondecreasing in `v`, and
`α < 8 / 25`, so `Xd_add_Xl_div_four_add_totalAllowance_add_one_le_Vstar` at `V = V_*(ι)`
gives
`X_d(ι, v) + X_l(ι, v) / 4 + α W(ι, v) + 1 ≤ X_d(ι, V) + X_l(ι, V) / 4 + (8 / 25) W(ι, V) + 1
≤ 8 V`. Since `ω ≥ Ω_far(ι) ≥ 512 V`, this is at most `ω / 64`, and the left side is at most
`3 ω / 64 ≤ ω / 16 ≤ ω δ₀`, because `δ₀ = α - 1 / 4 ≥ 1 / 16`.

## Main results

* `CollatzPosDens.two_mul_rpow_add_mul_alpha_add_one_le_mul_drift`: the inequality above.

## References

* Mazur, §10.1 ("Scalar facts").
-/

@[expose] public section

namespace CollatzPosDens

/-- **The triangle margin at a far gap**: if `v < V_*(ι)` and `ω ≥ Ω_far(ι)`, then
`ω / 32 + X_d(ι, v) + X_l(ι, v) / 4 + α W(ι, v) + 1 ≤ ω δ₀`. -/
@[collatz_pos_dens "lem_c3_margin"]
theorem two_mul_rpow_add_mul_alpha_add_one_le_mul_drift (ι : FIndex) {v : ℕ} (hv : v < Vstar ι)
    {ω : ℝ} (hω : (omegaFar ι : ℝ) ≤ ω) :
    ω / 32 + (Xd ι v : ℝ) + 1 / 4 * (Xl ι v : ℝ) + alpha * (totalAllowance ι v : ℝ) + 1 ≤
      ω * drift := by
  have h512 : 512 * Vstar ι ≤ omegaFar ι :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (max_le_omegaFar ι))
  have hω512 : 512 * (Vstar ι : ℝ) ≤ ω := le_trans (by exact_mod_cast h512) hω
  have hgate :
      ((Xd ι (Vstar ι) + Xl ι (Vstar ι) / 4 + 8 / 25 * totalAllowance ι (Vstar ι) + 1 : ℚ) : ℝ) ≤
      ((8 * (Vstar ι : ℚ) : ℚ) : ℝ) := by
    exact_mod_cast Xd_add_Xl_div_four_add_totalAllowance_add_one_le_Vstar ι
  push_cast at hgate
  have hXd : (Xd ι v : ℝ) ≤ Xd ι (Vstar ι) := by exact_mod_cast Xd_mono ι hv.le
  have hXl : (Xl ι v : ℝ) ≤ Xl ι (Vstar ι) := by exact_mod_cast Xl_mono ι hv.le
  have hW : (totalAllowance ι v : ℝ) ≤ totalAllowance ι (Vstar ι) := by
    exact_mod_cast totalAllowance_mono ι hv.le
  have hW0 : (0 : ℝ) ≤ totalAllowance ι v := by exact_mod_cast (totalAllowance_pos ι v).le
  have hα : alpha ≤ 8 / 25 := alpha_lt_eight_div_twentyfive.le
  have hα0 : 0 ≤ alpha := by linarith [five_div_sixteen_le_alpha]
  have hαW : alpha * (totalAllowance ι v : ℝ) ≤ 8 / 25 * totalAllowance ι (Vstar ι) :=
    mul_le_mul hα hW hW0 (by norm_num)
  have hd : (1 : ℝ) / 16 ≤ drift := by
    rw [drift_def]
    linarith [five_div_sixteen_le_alpha]
  have hω0 : 0 ≤ ω := le_trans (by linarith [((Vstar ι).cast_nonneg : (0 : ℝ) ≤ Vstar ι)]) hω512
  have hωd := mul_le_mul_of_nonneg_left hd hω0
  generalize (Xd ι (Vstar ι) : ℝ) = a at *
  generalize (Xl ι (Vstar ι) : ℝ) = b at *
  generalize (totalAllowance ι (Vstar ι) : ℝ) = c at *
  generalize (Vstar ι : ℝ) = V at *
  linarith

end CollatzPosDens
