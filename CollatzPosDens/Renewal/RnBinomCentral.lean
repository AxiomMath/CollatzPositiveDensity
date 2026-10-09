/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity
public import CollatzPosDens.Attr

/-!
# An upper bound for the square of the normalized central binomial coefficient

This file proves that for every `m : ℕ`,
$$\Bigl(\binom{2m}{m} 4^{-m}\Bigr)^2 \le \frac{1}{3m+1}.$$
Writing $\beta_m = \binom{2m}{m} 4^{-m}$, one shows $(3m+1)\beta_m^2 \le 1$ by induction, using
$\beta_{m+1} = \beta_m \frac{2m+1}{2m+2}$ and
$(3m+4)(2m+1)^2 \le (3m+1)(2m+2)^2$.

## Main results

* `CollatzPosDens.three_mul_add_one_mul_centralBinom_sq_le`: the integer form
  `(3m+1) * (centralBinom m)^2 ≤ 16^m`.
* `CollatzPosDens.centralBinom_div_four_pow_sq_le`: the bound
  `(centralBinom m / 4^m)^2 ≤ 1 / (3m+1)`.

## Implementation notes

The induction is carried out in `ℕ`, in the cleared-denominator form
$(3m+1)\binom{2m}{m}^2 \le 16^m$, and transferred to `ℝ` at the end.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Nat

/-- The denominator-free form of the central binomial bound:
`(3m+1) * (centralBinom m)^2 ≤ 16^m`. -/
theorem three_mul_add_one_mul_centralBinom_sq_le (m : ℕ) :
    (3 * m + 1) * centralBinom m ^ 2 ≤ 16 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h := succ_mul_centralBinom_succ m
    set c := centralBinom m
    set c' := centralBinom (m + 1)
    have key : (m + 1) ^ 2 * ((3 * (m + 1) + 1) * c' ^ 2) ≤ (m + 1) ^ 2 * 16 ^ (m + 1) := by
      have e : (m + 1) ^ 2 * ((3 * (m + 1) + 1) * c' ^ 2)
          = 4 * ((3 * m + 4) * (2 * m + 1) ^ 2) * c ^ 2 := by
        have : ((m + 1) * c') ^ 2 = (2 * (2 * m + 1) * c) ^ 2 := by rw [h]
        nlinarith [this]
      rw [e, pow_succ]
      calc 4 * ((3 * m + 4) * (2 * m + 1) ^ 2) * c ^ 2
          ≤ 4 * (4 * (m + 1) ^ 2 * (3 * m + 1)) * c ^ 2 := by
            have : (3 * m + 4) * (2 * m + 1) ^ 2 ≤ 4 * (m + 1) ^ 2 * (3 * m + 1) := by
              nlinarith
            exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ this)
        _ = 16 * (m + 1) ^ 2 * ((3 * m + 1) * c ^ 2) := by ring
        _ ≤ 16 * (m + 1) ^ 2 * 16 ^ m := Nat.mul_le_mul_left _ ih
        _ = (m + 1) ^ 2 * (16 ^ m * 16) := by ring
    exact Nat.le_of_mul_le_mul_left key (by positivity)

/-- For every `m : ℕ`, `(centralBinom m / 4^m)^2 ≤ 1 / (3m+1)`. -/
@[collatz_pos_dens "lem_rn_binom_central"]
theorem centralBinom_div_four_pow_sq_le (m : ℕ) :
    ((centralBinom m : ℝ) / 4 ^ m) ^ 2 ≤ 1 / (3 * m + 1) := by
  have hx : (0 : ℝ) < 3 * m + 1 := by positivity
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  have hN : ((3 * m + 1 : ℕ) : ℝ) * (centralBinom m : ℝ) ^ 2 ≤ ((16 ^ m : ℕ) : ℝ) := by
    exact_mod_cast three_mul_add_one_mul_centralBinom_sq_le m
  push_cast at hN
  have h16 : (16 : ℝ) ^ m = (4 ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [h16] at hN
  rw [div_pow, le_div_iff₀ hx, div_mul_eq_mul_div, div_le_one (by positivity)]
  linarith

end CollatzPosDens
