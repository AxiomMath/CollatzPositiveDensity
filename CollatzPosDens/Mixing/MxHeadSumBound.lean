/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxWindowLowPos
public import CollatzPosDens.Transfer.Log3Bounds

/-!
# Valuation sums of heads are bounded

Let `n ≥ 2^80000`, `k, l ∈ ℕ` and `h ∈ Hd(n, k, l)`. Then `l < 4n`.

## Main results

* `CollatzPosDens.lt_four_mul_of_mem_mxHeadGate`: `l < 4n` for every member of `Hd(n, k, l)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Valuation sums of heads are bounded.** For `n ≥ 2^80000` and `h ∈ Hd(n, k, l)`,
`l < 4n`. -/
@[collatz_pos_dens "lem_mx_head_sum_bound"]
theorem lt_four_mul_of_mem_mxHeadGate {n k l : ℕ} (hn : 2 ^ 80000 ≤ n) {h : Word}
    (hh : h ∈ mxHeadGate n k l) : l < 4 * n := by
  obtain ⟨hlen, ⟨hlow, -⟩, ⟨htake, -, hl⟩, hprod⟩ := mem_mxHeadGate.1 hh
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_two_pow.trans hn
  -- the window forces `k ≥ 1`
  have hq : (0 : ℝ) < (mxWindowLow n : ℝ) := by
    have := mxWindowLow_pos_bound hn
    linarith
  have hq' : (0 : ℤ) < mxWindowLow n := by exact_mod_cast hq
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, t, rfl⟩ : ∃ a t, h = a :: t := by
    cases h with
    | nil => simp at hlen
    | cons a t => exact ⟨a, t, rfl⟩
  -- the first letter is at most the level, which is below `n log₂ 3`
  have ha : ((a : ℕ) : ℝ) ≤ mxLevel n := by
    refine le_trans ?_ htake
    rw [List.take_succ_cons, Word.valSum_cons]
    exact_mod_cast Nat.le_add_right _ _
  have hlog : 0 ≤ Real.logb 2 (n : ℝ) := Real.logb_nonneg one_lt_two hn1
  have hlv : mxLevel n < n * Real.logb 2 3 := by
    rw [mxLevel_def]
    linarith
  -- the product condition gives `2^l < 3^n 2^a`
  have hoff : ((2 : ℚ) ^ (a : ℕ))⁻¹ ≤ off (a :: t) := by
    rw [off_cons]
    have := off_nonneg t
    have h2 : (0 : ℚ) < ((2 : ℚ) ^ (a : ℕ))⁻¹ := by positivity
    nlinarith
  have hQ : (2 : ℚ) ^ l < 3 ^ n * 2 ^ (a : ℕ) := by
    have h2 : (0 : ℚ) < (2 : ℚ) ^ (a : ℕ) := by positivity
    have h3 : (2 : ℚ) ^ l * ((2 : ℚ) ^ (a : ℕ))⁻¹ < 3 ^ n :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hoff (by positivity)) hprod
    rwa [← div_eq_mul_inv, div_lt_iff₀ h2] at h3
  have hR : (2 : ℝ) ^ l < 3 ^ n * 2 ^ (a : ℕ) := by exact_mod_cast hQ
  have hL : (l : ℝ) < n * Real.logb 2 3 + (a : ℕ) := by
    have := Real.logb_lt_logb one_lt_two (by positivity) hR
    rwa [Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
      Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one, mul_one] at this
  have h317 := (logb_two_three_bounds).2
  have hn0 : (0 : ℝ) ≤ n := by linarith
  exact_mod_cast (by nlinarith : (l : ℝ) < 4 * n)

end CollatzPosDens
