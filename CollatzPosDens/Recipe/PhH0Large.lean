/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Recipe.QstarGe
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The seed bound is large

The seed bound `𝓜 = 4 ^ (19 + 3 ^ q_*)` satisfies `log₂ 𝓜 > 10 ^ 12`.

Indeed `log₂ 𝓜 = 2 (19 + 3 ^ q_*) > 2 · 3 ^ q_*`, and `q_* ≥ 9 N_* ≥ 26` since
`N_* = 9766262`; finally `2 · 3 ^ 26 > 10 ^ 12`.

## Main results

* `CollatzPosDens.logb_two_seedBound_eq`: `log₂ 𝓜 = 2 (19 + 3 ^ q_*)`.
* `CollatzPosDens.logb_two_seedBound_gt`: `10 ^ 12 < log₂ 𝓜`.

## Implementation notes

`log₂` is `Real.logb 2` applied to the real cast of the natural number `𝓜`.
-/

@[expose] public section

namespace CollatzPosDens

/-- `log₂ 𝓜 = 2 (19 + 3 ^ q_*)`. -/
theorem logb_two_seedBound_eq :
    Real.logb 2 (seedBound : ℝ) = 2 * (19 + 3 ^ conductor : ℕ) := by
  rw [seedBound_def, Nat.cast_pow, Real.logb_pow, show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num,
    Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
  ring

/-- The seed bound is large: `log₂ 𝓜 > 10 ^ 12`. -/
@[collatz_pos_dens "lem_ph_h0_large"]
theorem logb_two_seedBound_gt : (10 : ℝ) ^ 12 < Real.logb 2 (seedBound : ℝ) := by
  rw [logb_two_seedBound_eq]
  have h : 3 ^ 26 ≤ 3 ^ conductor :=
    Nat.pow_le_pow_right (by norm_num) (by have := le_conductor; omega)
  have h' : (10 : ℕ) ^ 12 < 2 * (19 + 3 ^ conductor) := by omega
  exact_mod_cast h'

end CollatzPosDens
