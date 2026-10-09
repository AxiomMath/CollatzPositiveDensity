/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.DepthWidth
public import CollatzPosDens.FirstCrossing.Scales
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The width sums `W_*(n)`

For $n \in \mathbb{N}$ the width sum is the total depth half-width of the first $n$ scales,
$$W_*(n) = \sum_{j=0}^{n-1} \mathrm{dw}(b_j),$$
where $b_j$ are the scales of the first-crossing argument and $\mathrm{dw}$ is the depth
half-width of a central block.

## Main definitions

* `CollatzPosDens.widthSum`: `W_*(n) = ∑_{j=0}^{n-1} dw(b_j)`.

## Main results

* `CollatzPosDens.widthSum_zero`, `CollatzPosDens.widthSum_succ`: the recursion
  `W_*(0) = 0`, `W_*(n + 1) = W_*(n) + dw(b_n)`.
* `CollatzPosDens.widthSum_monotone`: `W_*` is monotone.
* `CollatzPosDens.widthSum_le_sum_three_mul_div_five`: `W_*(n) ≤ ∑_{j<n} ⌊3 b_j / 5⌋`.
* `CollatzPosDens.widthSum_le_sum_scale`: `W_*(n) ≤ ∑_{j<n} b_j`.

## Implementation notes

The exclusive upper bound `n - 1` is encoded as the sum over `Finset.range n`, so that
`W_*(0) = 0` is the empty sum. The value is a natural number.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The width sum `W_*(n) = ∑_{j=0}^{n-1} dw(b_j)`, the total depth half-width of the first
`n` scales. -/
@[collatz_pos_dens "def_s07_Wstar"]
noncomputable def widthSum (n : ℕ) : ℕ := ∑ j ∈ range n, dw (scale j)

/-- Unfolding `W_*(n)` as a sum over `Finset.range n`. -/
theorem widthSum_def (n : ℕ) : widthSum n = ∑ j ∈ range n, dw (scale j) := rfl

/-- `W_*(0) = 0`. -/
@[simp]
theorem widthSum_zero : widthSum 0 = 0 := rfl

/-- `W_*(n + 1) = W_*(n) + dw(b_n)`. -/
theorem widthSum_succ (n : ℕ) : widthSum (n + 1) = widthSum n + dw (scale n) :=
  sum_range_succ _ _

/-- `W_*` is monotone. -/
theorem widthSum_monotone : Monotone widthSum := fun _ _ h =>
  sum_le_sum_of_subset (range_subset_range.2 h)

/-- `W_*(n) ≤ ∑_{j<n} ⌊3 b_j / 5⌋`. -/
theorem widthSum_le_sum_three_mul_div_five (n : ℕ) :
    widthSum n ≤ ∑ j ∈ range n, 3 * scale j / 5 :=
  sum_le_sum fun _ _ => dw_le_three_mul_div_five _

/-- `W_*(n)` is at most the sum of the first `n` scales. -/
theorem widthSum_le_sum_scale (n : ℕ) : widthSum n ≤ ∑ j ∈ range n, scale j :=
  sum_le_sum fun _ _ => dw_le_self _

end CollatzPosDens
