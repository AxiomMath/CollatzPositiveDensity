/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Second moment of the binomial coefficients

For every `N : ℕ`,
$$\sum_{i=0}^{N} \binom{N}{i} (2i - N)^2 = N \, 2^N,$$
i.e. a sum of `N` independent uniform signs `±1` has variance `N`.

## Main results

* `CollatzPosDens.sum_range_choose_succ_mul`: Pascal's rule for weighted binomial sums.
* `CollatzPosDens.sum_range_choose_mul_two_mul_sub_sq`: the identity
  `∑_{i=0}^N C(N, i) (2i - N)^2 = N 2^N`, in any commutative ring.

## Implementation notes

The identity is stated in an arbitrary commutative ring `R`, with `i` and `N` cast into `R`, so
that it applies verbatim over `ℤ`, `ℚ` and `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Pascal's rule for weighted binomial sums:
`∑_{i ≤ N+1} C(N+1, i) f(i) = ∑_{i ≤ N} C(N, i) (f(i) + f(i+1))`. -/
theorem sum_range_choose_succ_mul {R : Type*} [CommSemiring R] (N : ℕ) (f : ℕ → R) :
    ∑ i ∈ range (N + 2), ((N + 1).choose i : R) * f i =
      ∑ i ∈ range (N + 1), (N.choose i : R) * (f i + f (i + 1)) := by
  have h₁ : ∑ i ∈ range (N + 1), (N.choose (i + 1) : R) * f (i + 1) + f 0 =
      ∑ i ∈ range (N + 1), (N.choose i : R) * f i := by
    rw [sum_range_succ, sum_range_succ' (fun i => (N.choose i : R) * f i)]
    simp
  simp_rw [mul_add]
  rw [sum_range_succ', sum_add_distrib, ← h₁]
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, sum_add_distrib, Nat.choose_zero_right,
    Nat.cast_one, one_mul]
  ring

/-- **Second moment of the binomial coefficients**: `∑_{i=0}^N C(N, i) (2i - N)^2 = N 2^N`. -/
@[collatz_pos_dens "lem_mx_sh_binom_variance"]
theorem sum_range_choose_mul_two_mul_sub_sq (R : Type*) [CommRing R] (N : ℕ) :
    ∑ i ∈ range (N + 1), (N.choose i : R) * (2 * (i : R) - N) ^ 2 = (N : R) * 2 ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show N + 1 + 1 = N + 2 from rfl, sum_range_choose_succ_mul]
    have h : ∀ i ∈ range (N + 1),
        (N.choose i : R) * ((2 * (i : R) - ((N + 1 : ℕ) : R)) ^ 2 +
          (2 * ((i + 1 : ℕ) : R) - ((N + 1 : ℕ) : R)) ^ 2) =
        2 * ((N.choose i : R) * (2 * (i : R) - N) ^ 2) + 2 * (N.choose i : R) := by
      intro i _
      push_cast
      ring
    rw [sum_congr rfl h, sum_add_distrib, ← mul_sum, ← mul_sum, ih, ← Nat.cast_sum,
      Nat.sum_range_choose]
    push_cast
    ring

end CollatzPosDens
