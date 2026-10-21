/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Terminal.S06CountGate

/-!
# The logarithm of the clipping level of the count

For every integer `t ≥ 1`, `log (countLevel t) ≤ 256 (1 + log t)`. With `a = 18693/10000` and
`h = 1 + log t`, one has `countLevel t ≤ 2 countX t` and
`log (countX t) = (420 log 2 + log t + log h) / a`; the bounds `log h ≤ log t` and `log 2 ≤ 1`
give `log (countLevel t) ≤ (1 + 420/a) + (2/a) log t ≤ 256 h`.

## Main results

* `CollatzPosDens.log_countLevel_le`: `log (countLevel t) ≤ 256 (1 + log t)` for `t ≥ 1`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The logarithm of the clipping level satisfies `log (countLevel t) ≤ 256 (1 + log t)` for
every `t ≥ 1`. -/
@[collatz_pos_dens "lem_s06_count_log"]
theorem log_countLevel_le {t : ℕ} (ht : 1 ≤ t) :
    Real.log (countLevel t) ≤ 256 * (1 + Real.log t) := by
  have hx := countX_pos ht
  have hy := Real.log_natCast_nonneg t
  have hn : 0 < (countLevel t : ℝ) := by exact_mod_cast countLevel_pos ht
  have h1 : Real.log (countLevel t) ≤ Real.log 2 + Real.log (countX t) := by
    rw [← Real.log_mul (by norm_num) hx.ne']
    exact Real.log_le_log hn (countLevel_le_two_mul ht)
  have h2 : Real.log (1 + Real.log t) ≤ Real.log t := by
    linarith [Real.log_le_sub_one_of_pos (show 0 < 1 + Real.log t by linarith)]
  have h3 : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have h4 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [log_countX ht, amix_cast_o] at h1
  linarith

end CollatzPosDens
