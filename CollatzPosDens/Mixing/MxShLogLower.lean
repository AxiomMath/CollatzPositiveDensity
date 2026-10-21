/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxLog2Bounds
public import CollatzPosDens.Transfer.MxGate

/-!
# A lower bound for the logarithm beyond the mixing gate level

This file proves that $\frac{160}{3} \le \log x$ for every real $x \ge n_0$, where
$n_0 = 2^{80}$ is the mixing gate level `CollatzPosDens.mxGateLevel`.

Since $\log$ is increasing,
$\log x \ge \log n_0 = 80 \log 2 > 80 \cdot 0.693 = 55.44 \ge \frac{160}{3}$, using
`CollatzPosDens.log_two_bounds`.

## Main results

* `CollatzPosDens.le_log_of_two_pow_eighty_le`: for `n₀ ≤ x`, `160 / 3 ≤ Real.log x`.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every real `x ≥ n₀` (the mixing gate level, `n₀ = 2 ^ 80`), `160 / 3 ≤ log x`. -/
@[collatz_pos_dens "lem_mx_sh_log_lower"]
theorem le_log_of_two_pow_eighty_le {x : ℝ} (hx : (mxGateLevel : ℝ) ≤ x) :
    (160 / 3 : ℝ) ≤ Real.log x := by
  rw [mxGateLevel_def, Nat.cast_pow, Nat.cast_ofNat] at hx
  have h80 : Real.log ((2 : ℝ) ^ 80) ≤ Real.log x :=
    Real.log_le_log (by positivity) hx
  rw [Real.log_pow] at h80
  have h2 := log_two_bounds.1
  push_cast at h80
  linarith

end CollatzPosDens
