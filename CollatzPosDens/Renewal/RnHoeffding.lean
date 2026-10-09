/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# A Hoeffding bound for the symmetric binomial distribution

For every integer `n ≥ 1` and real `u ≥ 0`, the total weight under the symmetric binomial
law `k ↦ (n choose k) 2⁻ⁿ` of the integers `0 ≤ k ≤ n` with `|k - n/2| ≥ u` is at most
`2 exp(-2u²/n)`.

The proof is the Chernoff argument. The moment generating function of the centred law is
`∑ₖ (n choose k) 2⁻ⁿ e^{t(k - n/2)} = cosh(t/2)ⁿ`, by the binomial theorem, and
`cosh x ≤ e^{x²/2}`. On the set `|k - n/2| ≥ u` one has, for `λ ≥ 0`,
`1 ≤ e^{λ(k - n/2) - λu} + e^{-λ(k - n/2) - λu}`, so the weight of the set is at most
`2 e^{-λu} cosh(λ/2)ⁿ ≤ 2 e^{-λu + λ²n/8}`; take `λ = 4u/n`.

## Main results

* `CollatzPosDens.sum_choose_div_two_pow_mul_exp`: the moment generating function
  `∑ₖ (n choose k) 2⁻ⁿ e^{t(k - n/2)} = cosh(t/2)ⁿ`.
* `CollatzPosDens.binomial_tail_hoeffding`: the two-sided tail bound.

## Implementation notes

Rather than bounding the tails `k - n/2 ≥ u` and `k - n/2 ≤ -u` separately and identifying
them through the reflection `k ↦ n - k`, both tails are bounded at once by the pointwise
inequality `1 ≤ e^{λ(x - u)} + e^{λ(-x - u)}` for `|x| ≥ u`, together with the evenness of
`cosh`; this gives the same constant `2`.
-/

@[expose] public section

namespace CollatzPosDens

open Finset Real

/-- The moment generating function of the centred symmetric binomial law:
`∑ₖ (n choose k) 2⁻ⁿ e^{t(k - n/2)} = cosh(t/2)ⁿ`. -/
theorem sum_choose_div_two_pow_mul_exp (n : ℕ) (t : ℝ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℝ) / 2 ^ n * exp (t * ((k : ℝ) - n / 2)) =
      cosh (t / 2) ^ n := by
  rw [cosh_eq, div_pow, add_pow, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [← exp_nat_mul, ← exp_nat_mul, ← exp_add, Nat.cast_sub hk]
  field_simp
  ring_nf

/-- **Hoeffding's inequality for the symmetric binomial law.** For `n ≥ 1` and `u ≥ 0`,
the weight `∑ (n choose k) 2⁻ⁿ` over `0 ≤ k ≤ n` with `|k - n/2| ≥ u` is at most
`2 exp(-2u²/n)`. -/
@[collatz_pos_dens "lem_rn_hoeffding"]
theorem binomial_tail_hoeffding (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 ≤ u) :
    ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => u ≤ |(k : ℝ) - n / 2|),
      (n.choose k : ℝ) / 2 ^ n ≤ 2 * exp (-(2 * u ^ 2 / n)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set l : ℝ := 4 * u / n with hl
  have hl0 : 0 ≤ l := by positivity
  calc ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => u ≤ |(k : ℝ) - n / 2|),
        (n.choose k : ℝ) / 2 ^ n
      ≤ ∑ k ∈ (range (n + 1)).filter (fun k : ℕ => u ≤ |(k : ℝ) - n / 2|),
        (n.choose k : ℝ) / 2 ^ n * (exp (-(l * u)) * exp (l * ((k : ℝ) - n / 2)) +
          exp (-(l * u)) * exp (-l * ((k : ℝ) - n / 2))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk := (Finset.mem_filter.mp hk).2
        refine le_mul_of_one_le_right (by positivity) ?_
        rw [← exp_add, ← exp_add]
        rcases le_abs'.mp hk with h | h
        · have : 0 ≤ -(l * u) + -l * ((k : ℝ) - n / 2) := by nlinarith
          have := add_one_le_exp (-(l * u) + -l * ((k : ℝ) - n / 2))
          have := exp_pos (-(l * u) + l * ((k : ℝ) - n / 2))
          linarith
        · have : 0 ≤ -(l * u) + l * ((k : ℝ) - n / 2) := by nlinarith
          have := add_one_le_exp (-(l * u) + l * ((k : ℝ) - n / 2))
          have := exp_pos (-(l * u) + -l * ((k : ℝ) - n / 2))
          linarith
    _ ≤ ∑ k ∈ range (n + 1),
        (n.choose k : ℝ) / 2 ^ n * (exp (-(l * u)) * exp (l * ((k : ℝ) - n / 2)) +
          exp (-(l * u)) * exp (-l * ((k : ℝ) - n / 2))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
    _ = exp (-(l * u)) * (cosh (l / 2) ^ n + cosh (-l / 2) ^ n) := by
        rw [← sum_choose_div_two_pow_mul_exp, ← sum_choose_div_two_pow_mul_exp, mul_add,
          Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => by ring
    _ = 2 * (exp (-(l * u)) * cosh (l / 2) ^ n) := by
        rw [neg_div, cosh_neg]; ring
    _ ≤ 2 * (exp (-(l * u)) * exp ((l / 2) ^ 2 / 2) ^ n) := by
        gcongr
        exact cosh_le_exp_half_sq _
    _ = 2 * exp (-(2 * u ^ 2 / n)) := by
        rw [← exp_nat_mul, ← exp_add, hl]
        congr 2
        field_simp
        ring

end CollatzPosDens
