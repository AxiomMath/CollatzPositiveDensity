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

For $n \in \mathbb{N}$ the scale sum is the partial sum of the scales `CollatzPosDens.scale` up to
index $n$,
$$B_*(n) = \sum_{j=0}^{n} b_j.$$

## Main definitions

* `CollatzPosDens.scaleSum`: `B_*(n) = ∑_{j=0}^{n} b_j`.

## Main results

* `CollatzPosDens.scaleSum_zero`, `CollatzPosDens.scaleSum_succ`: the recursion
  `B_*(0) = b_0`, `B_*(n + 1) = B_*(n) + b_{n+1}`.
* `CollatzPosDens.scaleSum_monotone`, `CollatzPosDens.scaleSum_strictMono`: `B_*` is strictly
  increasing.
* `CollatzPosDens.scale_le_scaleSum`: `b_n ≤ B_*(n)`.
* `CollatzPosDens.scaleSum_pos`: `0 < B_*(n)`.

## Implementation notes

The sum is over `Finset.range (n + 1)`, the indices `0 ≤ j ≤ n`, and takes values in `ℕ`.
-/
@[expose] public section

namespace CollatzPosDens

/-- The scale sum `B_*(n) = ∑_{j=0}^{n} b_j`. -/
@[collatz_pos_dens "def_s07_Bstar"]
def scaleSum (n : ℕ) : ℕ := ∑ j ∈ Finset.range (n + 1), scale j

/-- Unfolding `B_*(n)` as a sum over `Finset.range (n + 1)`. -/
theorem scaleSum_def (n : ℕ) : scaleSum n = ∑ j ∈ Finset.range (n + 1), scale j := rfl

/-- `B_*(0) = b_0`. -/
@[simp]
theorem scaleSum_zero : scaleSum 0 = scale 0 := by
  simp [scaleSum]

/-- `B_*(n + 1) = B_*(n) + b_{n+1}`. -/
theorem scaleSum_succ (n : ℕ) : scaleSum (n + 1) = scaleSum n + scale (n + 1) :=
  Finset.sum_range_succ _ _

/-- `B_*` is nondecreasing. -/
theorem scaleSum_monotone : Monotone scaleSum := fun _ _ h =>
  Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (Nat.succ_le_succ h))

/-- `B_*` is strictly increasing, since every scale is positive. -/
theorem scaleSum_strictMono : StrictMono scaleSum :=
  strictMono_nat_of_lt_succ fun n => by
    rw [scaleSum_succ]; exact Nat.lt_add_of_pos_right (scale_pos _)

/-- The last scale is at most the scale sum: `b_n ≤ B_*(n)`. -/
theorem scale_le_scaleSum (n : ℕ) : scale n ≤ scaleSum n :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ n)

/-- `B_*(n)` is positive. -/
theorem scaleSum_pos (n : ℕ) : 0 < scaleSum n :=
  (scale_pos n).trans_le (scale_le_scaleSum n)

end CollatzPosDens
