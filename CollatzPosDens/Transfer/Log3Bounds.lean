/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import CollatzPosDens.Attr

/-!
# Elementary bounds on `log₂ 3`

This file proves the two-sided rational bound
$$\frac{79}{50} \le \log_2 3 \le \frac{317}{200}.$$
Clearing denominators, the lower bound is equivalent to $2^{158} \le 3^{100}$ and the upper
bound to $3^{200} \le 2^{317}$; both are exact integer comparisons.

## Main results

* `CollatzPosDens.logb_two_three_bounds`: `79 / 50 ≤ logb 2 3 ∧ logb 2 3 ≤ 317 / 200`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The elementary bounds `79 / 50 ≤ log₂ 3 ≤ 317 / 200`. -/
@[collatz_pos_dens "lem_s03_log3_bounds"]
theorem logb_two_three_bounds :
    (79 / 50 : ℝ) ≤ logb 2 3 ∧ logb 2 3 ≤ 317 / 200 := by
  have h2 : (0 : ℝ) < log 2 := log_pos (by norm_num)
  rw [logb, le_div_iff₀ h2, div_le_iff₀ h2]
  have hn : (3 : ℕ) ^ 200 ≤ 2 ^ 317 := by
    rw [show 317 = 200 + 117 from rfl, pow_add]
    norm_num
  have h₁ := log_le_log (by positivity)
    (by exact_mod_cast (by norm_num : (2 : ℕ) ^ 158 ≤ 3 ^ 100) : (2 : ℝ) ^ 158 ≤ 3 ^ 100)
  have h₂ := log_le_log (by positivity) (by exact_mod_cast hn : (3 : ℝ) ^ 200 ≤ 2 ^ 317)
  simp only [log_pow, Nat.cast_ofNat] at h₁ h₂
  constructor <;> linarith

end CollatzPosDens
