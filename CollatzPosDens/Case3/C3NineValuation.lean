/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.NumberTheory.Multiplicity

/-!
# The `2`-adic valuation of `9 ^ 2 ^ j - 1`

For every `j : ℕ`, the largest power of `2` dividing `9 ^ 2 ^ j - 1` is `2 ^ (j + 3)`. For `j = 0`
this is `9 - 1 = 8`. For `j ≥ 1` it is the lifting-the-exponent lemma at the prime `2`: for odd
`x > 1` and even `n ≠ 0`, `v₂ (x ^ n - 1) + 1 = v₂ (x + 1) + v₂ (x - 1) + v₂ n`, which with
`x = 9`, `n = 2 ^ j` reads `v₂ (9 ^ 2 ^ j - 1) + 1 = 1 + 3 + j`.

## Main results

* `CollatzPosDens.padicValNat_two_nine_pow_two_pow_sub_one`: `v₂ (9 ^ 2 ^ j - 1) = j + 3`.
* `CollatzPosDens.two_pow_dvd_nine_pow_two_pow_sub_one`: `2 ^ (j + 3) ∣ 9 ^ 2 ^ j - 1`.
* `CollatzPosDens.not_two_pow_dvd_nine_pow_two_pow_sub_one`: `¬ 2 ^ (j + 4) ∣ 9 ^ 2 ^ j - 1`.

## Implementation notes

Rather than inducting on `j` through `9 ^ 2 ^ (j + 1) - 1 = (9 ^ 2 ^ j - 1)(9 ^ 2 ^ j + 1)`, the
step `j ≥ 1` is taken from the lifting-the-exponent lemma `padicValNat.pow_two_sub_one`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The `2`-adic valuation of `9 ^ 2 ^ j - 1` is `j + 3`: the largest power of `2` dividing
`9 ^ 2 ^ j - 1` is `2 ^ (j + 3)`. -/
@[collatz_pos_dens "lem_c3_nine_valuation"]
theorem padicValNat_two_nine_pow_two_pow_sub_one (j : ℕ) :
    padicValNat 2 (9 ^ 2 ^ j - 1) = j + 3 := by
  rcases j with _ | j
  · rw [pow_zero, pow_one, show (9 - 1 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow]
  · have h := padicValNat.pow_two_sub_one (x := 9) (n := 2 ^ (j + 1)) (by norm_num)
      (by decide) (by positivity) ((Nat.even_pow' j.succ_ne_zero).2 even_two)
    rw [padicValNat.prime_pow, show (9 + 1 : ℕ) = 2 * 5 by norm_num,
      show (9 - 1 : ℕ) = 2 ^ 3 by norm_num, padicValNat.prime_pow,
      padicValNat.mul (by norm_num) (by norm_num), padicValNat.self (by norm_num),
      padicValNat.eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 5)] at h
    omega

/-- `2 ^ (j + 3)` divides `9 ^ 2 ^ j - 1`. -/
theorem two_pow_dvd_nine_pow_two_pow_sub_one (j : ℕ) : 2 ^ (j + 3) ∣ 9 ^ 2 ^ j - 1 := by
  rw [← padicValNat_two_nine_pow_two_pow_sub_one j]
  exact pow_padicValNat_dvd

/-- `2 ^ (j + 4)` does not divide `9 ^ 2 ^ j - 1`. -/
theorem not_two_pow_dvd_nine_pow_two_pow_sub_one (j : ℕ) : ¬ 2 ^ (j + 4) ∣ 9 ^ 2 ^ j - 1 := by
  have hne : 9 ^ 2 ^ j - 1 ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow (by positivity) (by norm_num))
  rw [show j + 4 = padicValNat 2 (9 ^ 2 ^ j - 1) + 1 by
    rw [padicValNat_two_nine_pow_two_pow_sub_one]]
  exact pow_succ_padicValNat_not_dvd hne

end CollatzPosDens
