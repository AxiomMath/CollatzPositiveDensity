/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope

/-!
# The inset margin

For a real number `ε` with `0 < ε < 1/27`, the quotient `log(1/ε) / log 9` exceeds `3/2`. Since
`1/ε > 27` and the logarithm is strictly increasing, `log(1/ε) > log 27`; as `27² = 729 = 9³`,
`log 27 = (3/2) log 9`, and dividing by `log 9 > 0` gives `3/2 < log(1/ε) / log 9`.

## Main results

* `CollatzPosDens.three_halves_lt_log_inv_div_log_nine`: `3/2 < log(1/ε) / log 9` for
  `0 < ε < 1/27`.

## Implementation notes

We write `log 27 = 3 log 3` and `log 9 = 2 log 3` rather than passing through `27² = 9³`; the two
are the same identity.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Inset margin.** If `0 < ε < 1/27`, then `3/2 < log(1/ε) / log 9`. -/
@[collatz_pos_dens "lem_bk_inset"]
theorem three_halves_lt_log_inv_div_log_nine {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < 1 / 27) :
    (3 / 2 : ℝ) < Real.log (1 / ε) / Real.log 9 := by
  have h27 : Real.log 27 < Real.log (1 / ε) := by
    apply Real.log_lt_log (by norm_num)
    rw [lt_div_iff₀ hε_pos]
    linarith
  have h27' : Real.log 27 = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ 3 by norm_num, Real.log_pow]; norm_num
  have h9 := log_nine_eq_two_mul_log_three
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [lt_div_iff₀ (by rw [h9]; positivity)]
  linarith

end CollatzPosDens
