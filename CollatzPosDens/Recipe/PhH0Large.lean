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

For every endpoint `s ≥ 1`, the seed bound `𝓜(s) = s · 2 ^ (38 + 4 · 3 ^ q_*)` satisfies
`log₂ 𝓜(s) > 10 ^ 12`.

Indeed `log₂ 𝓜(s) = log₂ s + 38 + 4 · 3 ^ q_* ≥ 4 · 3 ^ q_*` since `log₂ s ≥ 0`, and
`q_* ≥ 9 N_* ≥ 26` since `N_* = 9766262`; finally `4 · 3 ^ 26 > 10 ^ 12`.

## Main results

* `CollatzPosDens.logb_two_seedBound_eq`: `log₂ 𝓜(s) = log₂ s + (38 + 4 · 3 ^ q_*)`.
* `CollatzPosDens.logb_two_seedBound_gt`: `10 ^ 12 < log₂ 𝓜(s)` for every `s ≥ 1`.

## Implementation notes

`log₂` is `Real.logb 2` applied to the real cast of the natural number `𝓜(s)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `log₂ 𝓜(s) = log₂ s + (38 + 4 · 3 ^ q_*)` for `s ≥ 1`. -/
theorem logb_two_seedBound_eq {s : ℕ} (hs : 0 < s) :
    Real.logb 2 (seedBound s : ℝ) = Real.logb 2 s + (38 + 4 * 3 ^ conductor : ℕ) := by
  have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  rw [seedBound_eq_two_pow, Nat.cast_mul, Real.logb_mul hs' (by positivity), Nat.cast_pow,
    Real.logb_pow, Nat.cast_ofNat, Real.logb_self_eq_one (by norm_num), mul_one]

/-- The seed bound is large: `log₂ 𝓜(s) > 10 ^ 12` for every
`s ≥ 1`. -/
@[collatz_pos_dens "lem_ph_h0_large"]
theorem logb_two_seedBound_gt {s : ℕ} (hs : 0 < s) :
    (10 : ℝ) ^ 12 < Real.logb 2 (seedBound s : ℝ) := by
  rw [logb_two_seedBound_eq hs]
  have h0 : 0 ≤ Real.logb 2 (s : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hs)
  have h : 3 ^ 26 ≤ 3 ^ conductor :=
    Nat.pow_le_pow_right (by norm_num) (by have := le_conductor; omega)
  have h' : (10 : ℕ) ^ 12 < 38 + 4 * 3 ^ conductor := by omega
  have h'' : (10 : ℝ) ^ 12 < ((38 + 4 * 3 ^ conductor : ℕ) : ℝ) := by exact_mod_cast h'
  linarith

end CollatzPosDens
