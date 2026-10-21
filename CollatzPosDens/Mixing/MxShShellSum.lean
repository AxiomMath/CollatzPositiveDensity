/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShShellWidth

/-!
# The shell sum

For every integer `J ≥ 4`,
$$\sum_{j=0}^{J} \sqrt{(W_j + 2)\min(1, 2^{4-j})} < 3J,$$
where `W_j = shShellWidth j` is the width of the `j`-th offset shell.

For `j ≤ 4` the radicands are `3, 3, 4, 6, 10`, and `√3 < 7/4`, `√4 = 2`, `√6 < 5/2`,
`√10 < 13/4` bound the first five terms by `45/4`. For `j ≥ 5` the radicand is
`(2^{j-1} + 2) 2^{4-j} = 8 + 2^{5-j} ≤ 9`, so each later term is at most `3`. Hence the sum is
less than `45/4 + 3(J - 4) = 3J - 3/4`.

## Main results

* `CollatzPosDens.sum_sqrt_shShellWidth_lt`: the shell sum bound.

## Implementation notes

The power `2^{4-j}` is the integer power `(2 : ℝ) ^ (4 - j : ℤ)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The shell-sum term for `j ≥ 5` is at most `3`. -/
private theorem sqrt_shShellWidth_term_le_three (i : ℕ) :
    Real.sqrt (((shShellWidth (i + 5) : ℝ) + 2) * min 1 ((2 : ℝ) ^ (4 - ((i + 5 : ℕ) : ℤ)))) ≤
      3 := by
  have hz : (2 : ℝ) ^ (4 - ((i + 5 : ℕ) : ℤ)) = ((2 : ℝ) ^ (i + 1))⁻¹ := by
    rw [show (4 - ((i + 5 : ℕ) : ℤ)) = -((i + 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast]
  have hp : (1 : ℝ) ≤ 2 ^ (i + 1) := one_le_pow₀ one_le_two
  have hmin : min 1 ((2 : ℝ) ^ (4 - ((i + 5 : ℕ) : ℤ))) = ((2 : ℝ) ^ (i + 1))⁻¹ := by
    rw [hz]
    exact min_eq_right (inv_le_one_of_one_le₀ hp)
  rw [hmin, shShellWidth_succ, Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  have h2 : ((2 ^ (i + 4) : ℕ) : ℝ) = 8 * 2 ^ (i + 1) := by push_cast; ring
  rw [h2, add_mul, mul_assoc, mul_inv_cancel₀ (by positivity), mul_one]
  have : 2 * ((2 : ℝ) ^ (i + 1))⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ one_le_two (by omega)
  nlinarith

/-- The first five terms of the shell sum add up to less than `45/4`. -/
private theorem sum_sqrt_shShellWidth_range_five_lt :
    ∑ j ∈ range 5,
        Real.sqrt (((shShellWidth j : ℝ) + 2) * min 1 ((2 : ℝ) ^ (4 - (j : ℤ)))) < 45 / 4 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num [shShellWidth]
  have h3 : Real.sqrt 3 < 7 / 4 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have h6 : Real.sqrt 6 < 5 / 2 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have h10 : Real.sqrt 10 < 13 / 4 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  linarith

/-- **The shell sum.** For every integer `J ≥ 4`,
`∑_{j=0}^{J} √((W_j + 2) min(1, 2^{4-j})) < 3J`. -/
@[collatz_pos_dens "lem_mx_sh_shell_sum"]
theorem sum_sqrt_shShellWidth_lt {J : ℕ} (hJ : 4 ≤ J) :
    ∑ j ∈ range (J + 1),
        Real.sqrt (((shShellWidth j : ℝ) + 2) * min 1 ((2 : ℝ) ^ (4 - (j : ℤ)))) < 3 * J := by
  suffices h : ∑ j ∈ range (J + 1),
      Real.sqrt (((shShellWidth j : ℝ) + 2) * min 1 ((2 : ℝ) ^ (4 - (j : ℤ)))) <
        3 * J - 3 / 4 by linarith
  induction J, hJ using Nat.le_induction with
  | base =>
    have := sum_sqrt_shShellWidth_range_five_lt
    norm_num at this ⊢
    linarith
  | succ m hm ih =>
    rw [Finset.sum_range_succ]
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 4 := ⟨m - 4, by omega⟩
    have h5 := sqrt_shShellWidth_term_le_three i
    rw [show i + 5 = i + 4 + 1 by rfl] at h5
    push_cast at ih h5 ⊢
    linarith

end CollatzPosDens
