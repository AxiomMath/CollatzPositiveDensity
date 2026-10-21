/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkExitWidth

/-!
# A power bound for the exit width

For every `s ∈ ℕ` the exit width `f_s = ⌊(5s + 16) / 16⌋` satisfies `9 ^ f_s ≤ 9 * 2 ^ s`.
Indeed `16 f_s ≤ 5s + 16`, and `9 ^ 5 = 59049 ≤ 65536 = 2 ^ 16`, so
`(9 ^ f_s) ^ 16 ≤ 9 ^ (5s + 16) = 9 ^ 16 (9 ^ 5) ^ s ≤ 9 ^ 16 (2 ^ 16) ^ s = (9 * 2 ^ s) ^ 16`,
and taking sixteenth roots gives the claim.

## Main results

* `CollatzPosDens.nine_pow_bkExitWidth_le`: `9 ^ f_s ≤ 9 * 2 ^ s`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `9 ^ f_s ≤ 9 * 2 ^ s` for every `s ∈ ℕ`. -/
@[collatz_pos_dens "lem_bk_exit_width_pow"]
theorem nine_pow_bkExitWidth_le (s : ℕ) : 9 ^ bkExitWidth s ≤ 9 * 2 ^ s := by
  refine (Nat.pow_le_pow_iff_left (n := 16) (by norm_num)).1 ?_
  calc (9 ^ bkExitWidth s) ^ 16 = 9 ^ (16 * bkExitWidth s) := by rw [← pow_mul, mul_comm]
    _ ≤ 9 ^ (5 * s + 16) := Nat.pow_le_pow_right (by norm_num) (sixteen_mul_bkExitWidth_le s)
    _ = 9 ^ 16 * (9 ^ 5) ^ s := by rw [pow_add, pow_mul, mul_comm]
    _ ≤ 9 ^ 16 * (2 ^ 16) ^ s :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by norm_num) s)
    _ = (9 * 2 ^ s) ^ 16 := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm s]

end CollatzPosDens
