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

For an endpoint `s ≥ 1`, the final generation threshold
`J_*(s) = max (N_* + N_t) (max (200 * max (lg m(s) - 1, 0)) (20 * 10 ^ 9))` is small compared
with the binary logarithm `H = log₂ 𝓜(s)` of the seed bound: `J_*(s) < 200 log₂ 𝓜(s)`.

Indeed `H > 10 ^ 12`, so `N_* + N_t < 200 · 10 ^ 12 < 200 H` and `20 · 10 ^ 9 < 200 H`; moreover
`max (lg m - 1, 0) ≤ log₂ m < 8/9 H + log₂ C + 92 < H`, so the middle term is less than `200 H`.

## Main results

* `CollatzPosDens.finalGenerationThreshold_lt_logb_seedBound`: `J_*(s) < 200 log₂ 𝓜(s)` for
  `s ≥ 1`.

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

/-- **Lemma.** For every endpoint `s ≥ 1`, the final generation threshold is less than two
hundred times the binary logarithm of the seed bound: `J_*(s) < 200 log₂ 𝓜(s)`. -/
@[collatz_pos_dens "lem_s04_J_le"]
theorem finalGenerationThreshold_lt_logb_seedBound {s : ℕ} (hs : 0 < s) :
    (finalGenerationThreshold s : ℝ) < 200 * logb 2 (seedBound s : ℝ) := by
  have hh := logb_two_seedBound_gt hs
  have hm := logb_two_modulusExponent_lt hs
  obtain ⟨c1, c2, c3⟩ := logb_two_mixingConst_mem
  have hlg := lg_sub_one_le_logb_two (modulusExponent s)
  rw [finalGenerationThreshold_def, generationThreshold_eq, terminalThreshold_eq]
  push_cast [Nat.cast_max]
  refine max_lt (by linarith) (max_lt ?_ (by linarith))
  linarith

end CollatzPosDens
