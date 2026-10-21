/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Monotone.MoLogSqrt
public import CollatzPosDens.Transfer.MxGate

/-!
# An upper bound for the logarithm beyond the mixing gate level

This file proves that $\log x \le x^{1/8}$ for every real $x \ge n_0$, where
$n_0 = 2^{80}$ is the mixing gate level `CollatzPosDens.mxGateLevel`.

Applying $\log y \le \sqrt y$ at $y = x^{1/16}$ gives $\log x = 16 \log(x^{1/16}) \le 16 x^{1/32}$,
and $16 \le n_0^{3/32} = (2^{80})^{3/32} \le x^{3/32}$, so
$16 x^{1/32} \le x^{3/32} x^{1/32} = x^{1/8}$.

## Main results

* `CollatzPosDens.log_le_rpow_one_div_eight`: for `n₀ ≤ x`, `Real.log x ≤ x ^ (1 / 8)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every real `x ≥ n₀` (the mixing gate level, `n₀ = 2 ^ 80`), `log x ≤ x ^ (1 / 8)`. -/
@[collatz_pos_dens "lem_mx_sh_log_upper"]
theorem log_le_rpow_one_div_eight {x : ℝ} (hx : (mxGateLevel : ℝ) ≤ x) :
    Real.log x ≤ x ^ (1 / 8 : ℝ) := by
  rw [mxGateLevel_def, Nat.cast_pow, Nat.cast_ofNat] at hx
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have hlog : Real.log x = 16 * Real.log (x ^ (1 / 16 : ℝ)) := by
    rw [Real.log_rpow hx0]; ring
  have hsqrt : Real.sqrt (x ^ (1 / 16 : ℝ)) = x ^ (1 / 32 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
  have h1 : Real.log x ≤ 16 * x ^ (1 / 32 : ℝ) := by
    rw [hlog, ← hsqrt]
    exact mul_le_mul_of_nonneg_left (log_le_sqrt (by positivity)) (by norm_num)
  have h16 : (16 : ℝ) ≤ x ^ (3 / 32 : ℝ) := by
    have h2 : (16 : ℝ) ≤ (2 ^ 80 : ℝ) ^ (3 / 32 : ℝ) := by
      rw [show (2 ^ 80 : ℝ) = (2 : ℝ) ^ (80 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
      calc (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) := by norm_num
        _ ≤ (2 : ℝ) ^ ((80 : ℝ) * (3 / 32)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    exact h2.trans (Real.rpow_le_rpow (by positivity) hx (by norm_num))
  calc Real.log x ≤ 16 * x ^ (1 / 32 : ℝ) := h1
    _ ≤ x ^ (3 / 32 : ℝ) * x ^ (1 / 32 : ℝ) :=
      mul_le_mul_of_nonneg_right h16 (by positivity)
    _ = x ^ (1 / 8 : ℝ) := by rw [← Real.rpow_add hx0]; norm_num

end CollatzPosDens
