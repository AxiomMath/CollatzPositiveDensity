/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Texp
public import CollatzPosDens.Recipe.Bht
public import CollatzPosDens.Recipe.Erec
public import CollatzPosDens.Recipe.CalM
public import CollatzPosDens.Recipe.PhH0Large
public import CollatzPosDens.Recipe.JLe
public import CollatzPosDens.FirstCrossing.ScalesUpper
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Upper bound for the height exponent

The height exponent `B_ht = 𝓔(J_*) + ⌊2 b_{J_*}/3⌋` satisfies `log₂ B_ht < 2100 log₂ 𝓜`.

Since `t(u) ≤ u` and the scales are nondecreasing, `𝓔(J) ≤ J (17 + J + b_J)`, so
`B_ht ≤ (J + 1)(17 + J + b_J)`. The upper growth of the scales gives
`b_J < 201 𝗀^J ≤ 2^(8 + J)`, hence `B_ht < 2^(9 + 2J)`. Finally `J_* < 1000 log₂ 𝓜`, and
`log₂ 𝓜 = 2 (19 + 3^{q_*})` is a natural number, so `9 + 2 J_* < 2100 log₂ 𝓜`.

## Main results

* `CollatzPosDens.erec_le_mul_scale`: `𝓔(j) ≤ j (17 + j + b_j)`.
* `CollatzPosDens.heightExponentOf_lt_two_pow`: `𝓔(J) + ⌊2 b_J/3⌋ < 2^(9 + 2J)`.
* `CollatzPosDens.logb_two_heightExponent_lt`: `log₂ B_ht < 2100 log₂ 𝓜`.

## Implementation notes

Rather than bounding `b_J` by `2^(8 + Jδ)` with `δ = log₂ 𝗀 < 1/69` and then `J δ < 15 h_0`,
the cruder estimate `𝗀 ≤ 2`, i.e. `b_J < 2^(8 + J)`, is used. Together with `J_* < 1000 h_0` it
already gives `log₂ B_ht < 9 + 2000 h_0 < 2100 h_0`, so the lower bound on the scales and the
finer bounds on `δ` are not needed.

## References

* [Mazur, *Collatz positive density*], Section 16.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exponent recurrence is bounded by `𝓔(j) ≤ j (17 + j + b_j)`. -/
theorem erec_le_mul_scale (j : ℕ) : erec j ≤ j * (17 + j + scale j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [erec_succ]
    have ht := texp_le_self (scale j)
    have hs : scale j ≤ scale (j + 1) := scale_monotone (Nat.le_succ j)
    have hd : j / 32 ≤ j := Nat.div_le_self _ _
    have h1 : j * (17 + j + scale j) ≤ j * (17 + (j + 1) + scale (j + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    calc erec j + 17 + j / 32 + texp (scale j)
        ≤ j * (17 + (j + 1) + scale (j + 1)) + (17 + (j + 1) + scale (j + 1)) := by omega
      _ = (j + 1) * (17 + (j + 1) + scale (j + 1)) := by ring

/-- The scales satisfy `b_j < 2^(8 + j)`. -/
theorem scale_lt_two_pow_eight_add (j : ℕ) : scale j < 2 ^ (8 + j) := by
  have h := scale_lt_mul_growthRatio_pow j
  have hg : (growthRatio : ℝ) ^ j ≤ 2 ^ j :=
    pow_le_pow_left₀ growthRatio_cast_pos.le (by rw [growthRatio_cast]; norm_num) j
  have : (scale j : ℝ) < 2 ^ (8 + j) := by
    rw [pow_add]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) j]
  exact_mod_cast this

/-- For every `J`, `𝓔(J) + ⌊2 b_J/3⌋ < 2^(9 + 2J)`. -/
theorem heightExponentOf_lt_two_pow (J : ℕ) : heightExponentOf J < 2 ^ (9 + 2 * J) := by
  rw [heightExponentOf_def]
  have he := erec_le_mul_scale J
  have hs := scale_lt_two_pow_eight_add J
  have hd : 2 * scale J / 3 ≤ scale J := by omega
  have hJ : J + 1 ≤ 2 ^ J := Nat.lt_two_pow_self
  have h8 : 17 + J ≤ 2 ^ (8 + J) := by
    rw [pow_add]
    omega
  calc erec J + 2 * scale J / 3 ≤ (J + 1) * (17 + J + scale J) := by nlinarith
    _ < 2 ^ J * (2 ^ (8 + J) + 2 ^ (8 + J)) :=
      Nat.mul_lt_mul_of_le_of_lt hJ (by omega) (by positivity)
    _ = 2 ^ (9 + 2 * J) := by ring

/-- The height exponent `B_ht` satisfies `log₂ B_ht < 2100 log₂ 𝓜`. -/
@[collatz_pos_dens "lem_s04_Bht_le"]
theorem logb_two_heightExponent_lt :
    Real.logb 2 (heightExponent : ℝ) < 2100 * Real.logb 2 (seedBound : ℝ) := by
  set H : ℕ := 2 * (19 + 3 ^ conductor) with hH
  have hM : Real.logb 2 (seedBound : ℝ) = H := by
    rw [logb_two_seedBound_eq, hH]
    push_cast
    ring
  have hJ : finalGenerationThreshold < 1000 * H := by
    have := finalGenerationThreshold_lt_logb_seedBound
    rw [hM] at this
    exact_mod_cast this
  have hH1 : 1 ≤ H := by omega
  have hB : heightExponent < 2 ^ (2100 * H) := by
    rw [heightExponent_eq_heightExponentOf]
    exact (heightExponentOf_lt_two_pow _).trans_le (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [hM]
  rcases Nat.eq_zero_or_pos heightExponent with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.logb_zero]
    have : (1 : ℝ) ≤ H := by exact_mod_cast hH1
    linarith
  · have hB' : (heightExponent : ℝ) < (2 : ℝ) ^ (2100 * H) := by exact_mod_cast hB
    have := Real.logb_lt_logb (b := 2) (by norm_num) (by exact_mod_cast hpos) hB'
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at this
    exact_mod_cast this

end CollatzPosDens
