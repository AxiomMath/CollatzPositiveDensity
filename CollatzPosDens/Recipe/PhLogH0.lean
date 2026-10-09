/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Qstar
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Recipe.QstarGe
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Iterated logarithm of the seed bound

We prove `log₂ log₂ 𝓜 ≤ 2 + q_* log₂ 3`, where `𝓜 = 4 ^ (19 + 3 ^ q_*)` is the seed bound and
`q_*` the conductor.

Indeed `log₂ 𝓜 = 38 + 2 · 3 ^ q_* ≤ 4 · 3 ^ q_*` as soon as `3 ^ q_* ≥ 19`, which holds since
`q_* ≥ 9 N_* ≥ 9`; taking `log₂` gives `log₂ log₂ 𝓜 ≤ 2 + q_* log₂ 3`.

## Main results

* `CollatzPosDens.logb_logb_seedBoundOf_le`: `log₂ log₂ (4 ^ (19 + 3 ^ q)) ≤ 2 + q log₂ 3`
  for every `q ≥ 3`.
* `CollatzPosDens.logb_logb_seedBound_le`: `log₂ log₂ 𝓜 ≤ 2 + q_* log₂ 3`.

## Implementation notes

The inequality only uses `3 ^ q ≥ 19`, i.e. `q ≥ 3`, so it is first proved for the parametric
expression `seedBoundOf q` with `q ≥ 3`, and the statement is its instance at `q = q_*`.
-/

@[expose] public section

namespace CollatzPosDens

/-- `log₂ log₂ (4 ^ (19 + 3 ^ q)) ≤ 2 + q log₂ 3` for every `q ≥ 3`. -/
theorem logb_logb_seedBoundOf_le {q : ℕ} (hq : 3 ≤ q) :
    Real.logb 2 (Real.logb 2 (seedBoundOf q : ℝ)) ≤ 2 + q * Real.logb 2 3 := by
  have h19 : (3 : ℝ) ^ 3 ≤ 3 ^ q := pow_le_pow_right₀ (by norm_num) hq
  have hlog : Real.logb 2 (seedBoundOf q : ℝ) = 38 + 2 * 3 ^ q := by
    rw [seedBoundOf_def]
    push_cast
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, Real.logb_pow, Real.logb_self_eq_one
      (by norm_num)]
    push_cast
    ring
  rw [hlog]
  calc Real.logb 2 (38 + 2 * 3 ^ q) ≤ Real.logb 2 (2 ^ (2 : ℕ) * 3 ^ q) :=
        Real.logb_le_logb_of_le (by norm_num) (by positivity) (by nlinarith)
    _ = 2 + q * Real.logb 2 3 := by
        rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
          Real.logb_self_eq_one (by norm_num)]
        push_cast
        ring

/-- The iterated logarithm of the seed bound `𝓜 = seedBound` satisfies
`log₂ log₂ 𝓜 ≤ 2 + q_* log₂ 3`, where `q_* = conductor`. -/
@[collatz_pos_dens "lem_ph_log_h0"]
theorem logb_logb_seedBound_le :
    Real.logb 2 (Real.logb 2 (seedBound : ℝ)) ≤ 2 + conductor * Real.logb 2 3 := by
  rw [seedBound_eq_seedBoundOf]
  exact logb_logb_seedBoundOf_le (by have := le_conductor; omega)

end CollatzPosDens
