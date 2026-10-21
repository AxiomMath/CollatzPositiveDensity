/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Eventual decrease of a damped logarithm

For `ε > 0` the function `x ↦ x ^ (-ε) * log x` is decreasing on `[e^{1/ε}, ∞)`: if `1 < x ≤ y`
and `ε log x ≥ 1`, then `y ^ (-ε) log y ≤ x ^ (-ε) log x`.

Writing `t = y / x ≥ 1`, the bound `e^u ≥ 1 + u` gives `t ^ ε ≥ 1 + ε log t`, hence
`t ^ ε log x ≥ log x + ε log x log t ≥ log x + log t = log y`; multiplying by
`x ^ (-ε) t ^ (-ε) = y ^ (-ε)` gives the claim.

## Main results

* `CollatzPosDens.rpow_neg_mul_log_le_of_one_le_mul_log`: the monotonicity statement.

## Implementation notes

The hypothesis `0 < ε` is not assumed: it follows from `1 < x` and `1 ≤ ε log x`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- For `1 < x ≤ y` with `1 ≤ ε log x`, `y ^ (-ε) log y ≤ x ^ (-ε) log x`: the damped logarithm
`x ↦ x ^ (-ε) log x` is antitone beyond `e^{1/ε}`. -/
@[collatz_pos_dens "lem_mx_sh_log_power_antitone"]
theorem rpow_neg_mul_log_le_of_one_le_mul_log {ε x y : ℝ} (hx : 1 < x) (hxy : x ≤ y)
    (hεx : 1 ≤ ε * log x) : y ^ (-ε) * log y ≤ x ^ (-ε) * log x := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < log x := log_pos hx
  set t := y / x with ht
  have ht1 : 1 ≤ t := (one_le_div hx0).2 hxy
  have ht0 : 0 < t := by linarith
  have hy : y = x * t := by rw [ht]; field_simp
  have hlt : 0 ≤ log t := log_nonneg ht1
  have hly : log y = log x + log t := by rw [hy, log_mul hx0.ne' ht0.ne']
  have hexp : 1 + ε * log t ≤ t ^ ε := by
    rw [rpow_def_of_pos ht0, mul_comm (log t) ε]
    linarith [add_one_le_exp (ε * log t)]
  have key : log y ≤ t ^ ε * log x := by
    have h1 : log t ≤ ε * log x * log t := by nlinarith
    nlinarith
  have hyε : y ^ (-ε) = x ^ (-ε) * t ^ (-ε) := by
    rw [hy, mul_rpow hx0.le ht0.le]
  have htε : t ^ (-ε) * t ^ ε = 1 := by
    rw [← rpow_add ht0]; simp
  have hxε : 0 < x ^ (-ε) := rpow_pos_of_pos hx0 _
  have htε0 : 0 < t ^ (-ε) := rpow_pos_of_pos ht0 _
  calc y ^ (-ε) * log y = x ^ (-ε) * (t ^ (-ε) * log y) := by rw [hyε]; ring
    _ ≤ x ^ (-ε) * (t ^ (-ε) * (t ^ ε * log x)) := by gcongr
    _ = x ^ (-ε) * log x := by
      rw [← mul_assoc (t ^ (-ε)), htε, one_mul]

end CollatzPosDens
