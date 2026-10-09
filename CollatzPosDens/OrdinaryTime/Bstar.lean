/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The scale sums `B_*(n)`

For $n \in \mathbb{N}$ the scale sum is the partial sum of the scales
$$B_*(n) = \sum_{j=0}^{n} b_j,$$
where $b_j$ is `CollatzPosDens.scale j`, defined by $b_0 = 9$ and $b_{j+1} = b_j + e_{b_j}$.

## Main definitions

* `CollatzPosDens.scaleSum`: `B_*(n) = ∑_{j=0}^{n} b_j`.

## Main results

* `CollatzPosDens.scaleSum_zero`, `CollatzPosDens.scaleSum_succ`: the recursion
  `B_*(0) = b_0`, `B_*(n + 1) = B_*(n) + b_{n+1}`.
* `CollatzPosDens.scaleSum_strictMono`: `B_*` is strictly increasing.
* `CollatzPosDens.scale_le_scaleSum`: `b_n ≤ B_*(n)`.
* `CollatzPosDens.nine_mul_le_scaleSum`: `9 (n + 1) ≤ B_*(n)`.

## Implementation notes

The inclusive upper bound `n` is encoded as the sum over `Finset.range (n + 1)`, and the value
is a natural number.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale sum `B_*(n) = ∑_{j=0}^{n} b_j`, the sum of the first `n + 1` scales. -/
@[collatz_pos_dens "def_s07_Bstar"]
def scaleSum (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), scale j

/-- Unfolding `B_*(n)` as a sum over `Finset.range (n + 1)`. -/
theorem scaleSum_def (n : ℕ) : scaleSum n = ∑ j ∈ Finset.range (n + 1), scale j := rfl

/-- `B_*(0) = b_0`. -/
@[simp]
theorem scaleSum_zero : scaleSum 0 = scale 0 := by
  simp [scaleSum]

/-- `B_*(n + 1) = B_*(n) + b_{n+1}`. -/
theorem scaleSum_succ (n : ℕ) : scaleSum (n + 1) = scaleSum n + scale (n + 1) := by
  rw [scaleSum, Finset.sum_range_succ, ← scaleSum]

/-- `B_*` is strictly increasing, since every scale is positive. -/
theorem scaleSum_strictMono : StrictMono scaleSum :=
  strictMono_nat_of_lt_succ fun n => by
    rw [scaleSum_succ]
    exact Nat.lt_add_of_pos_right (scale_pos _)

/-- `B_*` is nondecreasing. -/
theorem scaleSum_monotone : Monotone scaleSum :=
  scaleSum_strictMono.monotone

/-- The last scale is at most the scale sum: `b_n ≤ B_*(n)`. -/
theorem scale_le_scaleSum (n : ℕ) : scale n ≤ scaleSum n := by
  cases n with
  | zero => simp
  | succ n => rw [scaleSum_succ]; exact Nat.le_add_left _ _

/-- `B_*(n)` is positive. -/
theorem scaleSum_pos (n : ℕ) : 0 < scaleSum n :=
  (scale_pos n).trans_le (scale_le_scaleSum n)

/-- Each of the `n + 1` summands is at least `b_0 = 9`, so `9 (n + 1) ≤ B_*(n)`. -/
theorem nine_mul_le_scaleSum (n : ℕ) : 9 * (n + 1) ≤ scaleSum n := by
  have h := Finset.card_nsmul_le_sum (Finset.range (n + 1)) scale 9
    fun j _ => nine_le_scale j
  rw [Finset.card_range, nsmul_eq_mul, Nat.cast_id] at h
  rw [scaleSum, mul_comm]
  exact h

end CollatzPosDens
