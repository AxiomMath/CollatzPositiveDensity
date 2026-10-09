/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.X0
public import CollatzPosDens.Recipe.Tower
public import CollatzPosDens.Recipe.PhConductor
public import CollatzPosDens.Recipe.PhCutoffChain
public import CollatzPosDens.Recipe.PhEndpoint

/-!
# A tower bound for the cutoff

This file proves that the cutoff `X_0 = cutoff` satisfies `1024 X_0 < tow_4(140214)`.

Write `Y_1 = log₂(1024 X_0)`, `Y_2 = log₂ Y_1` and `Y_3 = log₂ Y_2`. The bounds
`logb_logb_logb_logb_cutoff_lt`, `logb_conductor_add_one_lt` and
`sixteen_add_generationThreshold_mul_logGrowthRate_lt` together give `log₂ Y_3 < 140214`.
Since `1024 X_0 ≥ 1024`, every `Y_i` is positive, so exponentiating four times (using that
`x ↦ 2 ^ x` is increasing and `2 ^ (log₂ y) = y` for `y > 0`) yields `Y_3 < tow_1(140214)`,
`Y_2 < tow_2(140214)`, `Y_1 < tow_3(140214)` and finally `1024 X_0 < tow_4(140214)`.

## Main results

* `CollatzPosDens.thousand_twenty_four_mul_cutoff_lt_tower`:
  `1024 X_0 < tow_4(140214)`.

## Implementation notes

The tower is never evaluated: each exponentiation step only compares a real number with the
cast of `2 ^ n` for a symbolic natural number `n`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- If `4 < x` and `log₂ log₂ log₂ log₂ x < t`, then `x < tow_4(t)`. -/
private lemma lt_tower_four_of_logb_lt {x : ℝ} {t : ℕ} (hx : 4 < x)
    (h : logb 2 (logb 2 (logb 2 (logb 2 x))) < t) : x < ((tower 4 t : ℕ) : ℝ) := by
  have hY1 : (2 : ℝ) < logb 2 x := by
    rw [lt_logb_iff_rpow_lt (by norm_num) (by linarith)]
    norm_num; linarith
  have hY2 : (1 : ℝ) < logb 2 (logb 2 x) := by
    rw [lt_logb_iff_rpow_lt (by norm_num) (by linarith)]
    norm_num; linarith
  have hY3 : (0 : ℝ) < logb 2 (logb 2 (logb 2 x)) := logb_pos (by norm_num) hY2
  exact lt_tower_succ_of_logb_lt (by linarith) <| lt_tower_succ_of_logb_lt (by linarith) <|
    lt_tower_succ_of_logb_lt (by linarith) <| lt_tower_succ_of_logb_lt hY3 (by simpa using h)

/-- The cutoff `X_0` satisfies `1024 X_0 < tow_4(140214)`. -/
@[collatz_pos_dens "lem_X0_tower"]
theorem thousand_twenty_four_mul_cutoff_lt_tower : 1024 * cutoff < tower 4 140214 := by
  have hchain := logb_logb_logb_logb_cutoff_lt
  have hcond := logb_conductor_add_one_lt
  have hend := sixteen_add_generationThreshold_mul_logGrowthRate_lt
  have hx : (4 : ℝ) < ((1024 * cutoff : ℕ) : ℝ) := by
    have : 1 ≤ cutoff := cutoff_pos
    exact_mod_cast (by omega : 4 < 1024 * cutoff)
  have h : logb 2 (logb 2 (logb 2 (logb 2 ((1024 * cutoff : ℕ) : ℝ)))) <
      ((140214 : ℕ) : ℝ) := by
    push_cast; linarith
  exact Nat.cast_lt.mp (lt_tower_four_of_logb_lt hx h)

end CollatzPosDens
