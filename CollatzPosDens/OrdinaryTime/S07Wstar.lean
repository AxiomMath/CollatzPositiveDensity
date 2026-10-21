/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.Width
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The width sums `W_*(n)`

For $n \in \mathbb{N}$ the width sum is the total width of the scales of the generations
$0 \le j \le n - 1$,
$$W_*(n) = \sum_{j=0}^{n-1} \mathrm{wd}(b_j),$$
the empty sum $0$ if $n = 0$, where $b_j$ is the scale `CollatzPosDens.scale j` and
$\mathrm{wd}$ is the width `CollatzPosDens.wd`.

## Main definitions

* `CollatzPosDens.widthSum`: `W_*(n) = ∑_{j=0}^{n-1} wd(b_j)`.

## Main results

* `CollatzPosDens.widthSum_zero`, `CollatzPosDens.widthSum_succ`: the recursion
  `W_*(0) = 0`, `W_*(n + 1) = W_*(n) + wd(b_n)`.
* `CollatzPosDens.widthSum_monotone`: `W_*` is monotone.
* `CollatzPosDens.widthSum_le_sum_three_mul_div_five`: `W_*(n) ≤ ∑_{j=0}^{n-1} ⌊3 b_j / 5⌋`.
* `CollatzPosDens.widthSum_le_sum_scale`: `W_*(n) ≤ ∑_{j=0}^{n-1} b_j`.

## Implementation notes

The range $0 \le j \le n - 1$ is encoded as `Finset.range n`, which is empty for `n = 0`, so the
convention for `n = 0` holds definitionally. The value is a natural number.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The width sum `W_*(n) = ∑_{j=0}^{n-1} wd(b_j)` (the empty sum `0` if `n = 0`), the total
width of the scales of generations `j < n`. -/
@[collatz_pos_dens "def_s07_Wstar"]
noncomputable def widthSum (n : ℕ) : ℕ := ∑ j ∈ range n, wd (scale j)

/-- Unfolding `W_*(n)` as a sum over `Finset.range n`. -/
theorem widthSum_def (n : ℕ) : widthSum n = ∑ j ∈ range n, wd (scale j) := rfl

/-- `W_*(0) = 0`. -/
@[simp]
theorem widthSum_zero : widthSum 0 = 0 := sum_range_zero _

/-- `W_*(n + 1) = W_*(n) + wd(b_n)`. -/
theorem widthSum_succ (n : ℕ) : widthSum (n + 1) = widthSum n + wd (scale n) :=
  sum_range_succ _ _

/-- `W_*` is monotone. -/
theorem widthSum_monotone : Monotone widthSum := fun _ _ h =>
  sum_le_sum_of_subset (range_subset_range.2 h)

/-- `W_*(n) ≤ ∑_{j=0}^{n-1} ⌊3 b_j / 5⌋`. -/
theorem widthSum_le_sum_three_mul_div_five (n : ℕ) :
    widthSum n ≤ ∑ j ∈ range n, 3 * scale j / 5 :=
  sum_le_sum fun _ _ => (wd_le_floor_sub_one _).trans (Nat.sub_le _ _)

/-- `W_*(n)` is at most the sum of the scales of generations `j < n`. -/
theorem widthSum_le_sum_scale (n : ℕ) : widthSum n ≤ ∑ j ∈ range n, scale j :=
  sum_le_sum fun _ _ => (wd_lt_self (scale_pos _)).le

end CollatzPosDens
