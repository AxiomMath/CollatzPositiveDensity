/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Jstar
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.Clog
public import CollatzPosDens.Recipe.NValue
public import CollatzPosDens.Recipe.NtValue
public import CollatzPosDens.Recipe.PhH0Large
public import CollatzPosDens.Recipe.PhMLog
public import CollatzPosDens.Transfer.Log2C
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Upper bound for the final generation threshold

The final generation threshold
`J_* = max (N_* + N_t) (max (200 * max (lg m - 1, 0)) (20 * 10 ^ 9))` is small compared with the
binary logarithm `h_0 = log₂ 𝓜` of the seed bound: `J_* < 1000 log₂ 𝓜`.

Indeed `N_* + N_t < 10 ^ 12 < h_0` and `20 * 10 ^ 9 < h_0`; moreover
`max (lg m - 1, 0) ≤ log₂ m < 8/9 h_0 + log₂ C + 92 < h_0`, so each term of the maximum is less
than `1000 h_0`.

## Main results

* `CollatzPosDens.finalGenerationThreshold_lt_logb_seedBound`: `J_* < 1000 log₂ 𝓜`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The positive part of `lg u - 1` is at most `log₂ u`, for every natural number `u`
(with `log₂ 0 = 0`). -/
private theorem lg_sub_one_le_logb_two (u : ℕ) : ((lg u - 1 : ℕ) : ℝ) ≤ Real.logb 2 u := by
  rcases Nat.lt_or_ge (lg u) 2 with h | h
  · have h0 : lg u - 1 = 0 := by omega
    rw [h0, Nat.cast_zero]
    rcases Nat.eq_zero_or_pos u with hu | hu
    · simp [hu]
    · exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hu)
  · have hlt : 2 ^ (lg u - 1) < u := by
      by_contra hc
      have := lg_le_of_le_two_pow (Nat.le_of_not_lt hc)
      omega
    have hlt' : (2 : ℝ) ^ (lg u - 1) < u := by exact_mod_cast hlt
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hlt'.le
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this

end CollatzPosDens

namespace CollatzPosDens

open Real

/-- The final generation threshold is less than a thousand times the binary logarithm of the seed
bound: `J_* < 1000 log₂ 𝓜`. -/
@[collatz_pos_dens "lem_s04_J_le"]
theorem finalGenerationThreshold_lt_logb_seedBound :
    (finalGenerationThreshold : ℝ) < 1000 * logb 2 (seedBound : ℝ) := by
  have hh := logb_two_seedBound_gt
  have hm := logb_two_modulusExponent_lt
  obtain ⟨c1, c2, c3⟩ := logb_two_mixingConst_mem
  have hlg := lg_sub_one_le_logb_two modulusExponent
  rw [finalGenerationThreshold_def, generationThreshold_eq, terminalThreshold_eq]
  push_cast [Nat.cast_max]
  refine max_lt (by linarith) (max_lt ?_ (by linarith))
  linarith

end CollatzPosDens
