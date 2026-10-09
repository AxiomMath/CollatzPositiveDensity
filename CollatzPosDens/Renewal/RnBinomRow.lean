/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnBinomCentral
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The maximal binomial weight of a row

This file proves that every binomial probability of row `n` satisfies
$$\Bigl(\binom{n}{k} 2^{-n}\Bigr)^2 \le \frac{2}{3n+2}.$$
The largest coefficient of row `n` is $\binom{n}{\lfloor n/2 \rfloor}$. For `n = 2m` this is the
central binomial coefficient and the bound is $\frac{1}{3m+1} = \frac{2}{3n+2}$. For `n = 2m+1`,
$\binom{2m+2}{m+1} = 2\binom{2m+1}{m}$, so
$\binom{2m+1}{m} 2^{-(2m+1)} = \binom{2m+2}{m+1} 4^{-(m+1)}$,
whose square is at most $\frac{1}{3m+4} \le \frac{2}{3n+2}$.

## Main results

* `CollatzPosDens.choose_div_two_pow_sq_le`: for `n k : ℕ`,
  `(n.choose k / 2^n)^2 ≤ 2 / (3n+2)`.
* `CollatzPosDens.intChoose_div_two_pow_sq_le`: the same bound for an integer index `k`,
  with the convention $\binom{n}{k} = 0$ for `k < 0`.

## Implementation notes

For an integer index `k`, the coefficient $\binom{n}{k}$ is taken to be `0` outside `[0, n]`.
Since `Nat.choose` already vanishes for `k > n`, the integer-indexed coefficient is
`if 0 ≤ k then n.choose k.toNat else 0`, and the bound reduces to the natural-number statement.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Nat

/-- **Maximal binomial weight of a row**: for all `n k : ℕ`,
`(n.choose k / 2^n)^2 ≤ 2 / (3n+2)`. -/
@[collatz_pos_dens "lem_rn_binom_row"]
theorem choose_div_two_pow_sq_le (n k : ℕ) :
    ((n.choose k : ℝ) / 2 ^ n) ^ 2 ≤ 2 / (3 * n + 2) := by
  have hmid : (n.choose k : ℝ) ≤ n.choose (n / 2) := by exact_mod_cast Nat.choose_le_middle k n
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [show 2 * m / 2 = m by omega, ← Nat.centralBinom_eq_two_mul_choose] at hmid
    rw [show (2 : ℝ) ^ (2 * m) = 4 ^ m by rw [pow_mul]; norm_num]
    calc (((2 * m).choose k : ℝ) / 4 ^ m) ^ 2 ≤ ((centralBinom m : ℝ) / 4 ^ m) ^ 2 := by
          gcongr
      _ ≤ 1 / (3 * (m : ℝ) + 1) := centralBinom_div_four_pow_sq_le m
      _ = 2 / (3 * ((2 * m : ℕ) : ℝ) + 2) := by
          push_cast
          field_simp
  · rw [show (2 * m + 1) / 2 = m by omega] at hmid
    have hcb : centralBinom (m + 1) = 2 * (2 * m + 1).choose m := by
      rw [Nat.centralBinom_eq_two_mul_choose, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
        Nat.choose_succ_succ, ← Nat.choose_symm_half m]
      ring
    have hcbR : ((2 * m + 1).choose m : ℝ) / 2 ^ (2 * m + 1)
        = (centralBinom (m + 1) : ℝ) / 4 ^ (m + 1) := by
      rw [hcb, show (4 : ℝ) ^ (m + 1) = 2 * 2 ^ (2 * m + 1) by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ]
        ring]
      push_cast
      field_simp
    calc (((2 * m + 1).choose k : ℝ) / 2 ^ (2 * m + 1)) ^ 2
        ≤ (((2 * m + 1).choose m : ℝ) / 2 ^ (2 * m + 1)) ^ 2 := by gcongr
      _ = ((centralBinom (m + 1) : ℝ) / 4 ^ (m + 1)) ^ 2 := by rw [hcbR]
      _ ≤ 1 / (3 * ((m + 1 : ℕ) : ℝ) + 1) := centralBinom_div_four_pow_sq_le (m + 1)
      _ ≤ 2 / (3 * ((2 * m + 1 : ℕ) : ℝ) + 2) := by
          push_cast
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          linarith

/-- **Maximal binomial weight of a row**, integer index: for `n : ℕ` and `k : ℤ`, with
$\binom{n}{k} = 0$ for `k < 0`, `(binom(n, k) / 2^n)^2 ≤ 2 / (3n+2)`. -/
@[collatz_pos_dens "lem_rn_binom_row"]
theorem intChoose_div_two_pow_sq_le (n : ℕ) (k : ℤ) :
    (((if 0 ≤ k then n.choose k.toNat else 0 : ℕ) : ℝ) / 2 ^ n) ^ 2 ≤ 2 / (3 * n + 2) := by
  split_ifs
  · exact choose_div_two_pow_sq_le n k.toNat
  · simp only [Nat.cast_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    positivity

end CollatzPosDens
