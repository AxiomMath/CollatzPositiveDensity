/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapUpper
public import CollatzPosDens.Case3.C3H17CapUp
public import CollatzPosDens.Case3.C3H17Node
public import CollatzPosDens.Case3.C3H17Table

/-!
# Periodicity of the height-seventeen cost table

The cost table `ct_{c,o}(m)` is periodic in `m` with period `2^17`. The majorant `U^η_c(θ)`
depends on `θ` only through the numbers `(a_j - a_i) θ` modulo `1`, where `a_j - a_i` are
integers, so `U^η_c(θ + n) = U^η_c(θ)` for every integer `n`, and the same holds for the grid
majorant `Ū_c`. By downward induction on `h`, the rounded future costs satisfy
`cf⁺_h(z + k 2^17) = cf⁺_h(z)`: the arguments `z / 2^{h+d}` with `h + d ≤ 17` change by
integers, and `9 (z + k 2^17) = 9 z + 9 k 2^17`. In the table, `m / 2^o` with `o ≤ 17` changes by
an integer and `9 m` by a multiple of `2^17`.

## Main results

* `CollatzPosDens.trCapUpper_add_intCast`, `CollatzPosDens.c3H17CapUp_add_intCast`: the
  majorants are `1`-periodic.
* `CollatzPosDens.c3H17Node_add_mul_two_pow`: `cf⁺_h(z + k 2^17) = cf⁺_h(z)`.
* `CollatzPosDens.c3H17Table_add_mul_two_pow`: `ct_{c,o}(m + k 2^17) = ct_{c,o}(m)` for `o ≤ 17`.
* `CollatzPosDens.c3H17Table_add_two_pow`: `ct_{c,o}(m + 2^17) = ct_{c,o}(m)` for `o ≤ 17`.

## Implementation notes

The periodicity holds for all integers `c`, `m` and all `o ≤ 17`, without the restrictions
`2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and `m` odd under which the table is used, and for every integer
multiple of `2^17`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The cosine bound is `1`-periodic. -/
theorem trCapCosBound_add_intCast (η x : ℚ) (n : ℤ) :
    trCapCosBound η (x + n) = trCapCosBound η x := by
  unfold trCapCosBound
  rw [Int.fract_add_intCast, round_add_intCast]
  push_cast
  ring_nf

/-- The radicand is `1`-periodic in `θ`. -/
theorem trCapRadicand_add_intCast (t : ℕ) (η θ : ℚ) (n : ℤ) :
    trCapRadicand t η (θ + n) = trCapRadicand t η θ := by
  unfold trCapRadicand
  congr 3
  refine sum_congr rfl fun j _ => sum_congr rfl fun i _ => ?_
  have : (((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ i - 1)) * (θ + n) =
      (((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ i - 1)) * θ + ((((2 : ℤ) ^ j - 2 ^ i) * n : ℤ) : ℚ) := by
    push_cast
    ring
  rw [this, trCapCosBound_add_intCast]

/-- The rational majorant `U^η_c(θ)` is `1`-periodic in `θ`. -/
theorem trCapUpper_add_intCast (c : ℤ) (η θ : ℚ) (n : ℤ) :
    trCapUpper c η (θ + n) = trCapUpper c η θ := by
  unfold trCapUpper
  rw [trCapRadicand_add_intCast]

/-- The grid majorant `Ū_c(θ)` is `1`-periodic in `θ`. -/
theorem c3H17CapUp_add_intCast (c : ℤ) (θ : ℚ) (n : ℤ) :
    c3H17CapUp c (θ + n) = c3H17CapUp c θ := by
  rw [c3H17CapUp_eq_trCapUpper, c3H17CapUp_eq_trCapUpper, trCapUpper_add_intCast]

/-- For `e ≤ 17`, `(z + k 2^17) / 2^e` and `z / 2^e` differ by an integer. -/
private theorem intCast_add_mul_two_pow_div {e : ℤ} (he : e ≤ 17) (z k : ℤ) :
    ((z + k * 2 ^ 17 : ℤ) : ℚ) / 2 ^ e =
      (z : ℚ) / 2 ^ e + ((k * 2 ^ (17 - e).toNat : ℤ) : ℚ) := by
  have h2 : (2 : ℚ) ^ (17 : ℕ) = 2 ^ e * 2 ^ ((17 - e).toNat : ℕ) := by
    rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      ← zpow_add₀ two_ne_zero]
    norm_num
  push_cast
  rw [show (131072 : ℚ) = 2 ^ (17 : ℕ) by norm_num, h2]
  field_simp

/-- The rounded future costs are periodic: `cf⁺_h(z + k 2^17) = cf⁺_h(z)`. -/
theorem c3H17Node_add_mul_two_pow (h z k : ℤ) :
    c3H17Node h (z + k * 2 ^ 17) = c3H17Node h z := by
  rcases le_or_gt 15 h with hh | hh
  · rw [c3H17Node_of_le hh, c3H17Node_of_le hh]
  rw [c3H17Node_of_lt hh, c3H17Node_of_lt hh]
  refine congrArg (fun s : ℚ => (⌈(10 ^ 8 : ℚ) * (1 - s)⌉ : ℚ) / 10 ^ 8)
    (sum_congr rfl fun d hd => ?_)
  have hd' := Finset.mem_Icc.mp hd
  have h9 : 9 * (z + k * 2 ^ 17) = 9 * z + 9 * k * 2 ^ 17 := by ring
  rw [intCast_add_mul_two_pow_div (by omega), c3H17CapUp_add_intCast, h9]
  split_ifs
  · rw [c3H17Node_add_mul_two_pow (h + d) (9 * z) (9 * k)]
  · rfl
termination_by (15 - h).toNat
decreasing_by
  simp only [Finset.mem_Icc] at *
  omega

/-- The cost table is periodic: `ct_{c,o}(m + k 2^17) = ct_{c,o}(m)` for `o ≤ 17`. -/
theorem c3H17Table_add_mul_two_pow (c : ℤ) {o : ℤ} (ho : o ≤ 17) (m k : ℤ) :
    c3H17Table c o (m + k * 2 ^ 17) = c3H17Table c o m := by
  have h9 : 9 * (m + k * 2 ^ 17) = 9 * m + 9 * k * 2 ^ 17 := by ring
  unfold c3H17Table
  rw [intCast_add_mul_two_pow_div ho, c3H17CapUp_add_intCast, h9, c3H17Node_add_mul_two_pow]

/-- The cost table is periodic with period `2^17`: `ct_{c,o}(m + 2^17) = ct_{c,o}(m)` for
`o ≤ 17`, in particular for `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and odd `m`. -/
@[collatz_pos_dens "lem_c3_h17_table_period"]
theorem c3H17Table_add_two_pow (c : ℤ) {o : ℤ} (ho : o ≤ 17) (m : ℤ) :
    c3H17Table c o (m + 2 ^ 17) = c3H17Table c o m := by
  simpa using c3H17Table_add_mul_two_pow c ho m 1

end CollatzPosDens
