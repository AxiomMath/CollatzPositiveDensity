/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic

/-!
# Straddle weights

For `t ∈ ℕ` and `j ∈ ℤ` the straddle weight is
`p_t(j) = binom(t + 1, 2j + 1) 2^{-t}` when `j ≥ 0`, and `p_t(j) = 0` when `j < 0`.
It is the total weight of the words `(c_1, …, c_{j+1})` with letters `≥ 2` whose
partial sums straddle the height `t`, that is `c_1 + ⋯ + c_j ≤ t < c_1 + ⋯ + c_{j+1}`.

## Main definitions

* `CollatzPosDens.straddleWeight t j`: the straddle weight `p_t(j)`.

## Main results

* `CollatzPosDens.straddleWeight_of_nonneg`, `CollatzPosDens.straddleWeight_of_neg`:
  the two cases of the definition.
* `CollatzPosDens.straddleWeight_natCast`: the value at a natural index.
* `CollatzPosDens.straddleWeight_nonneg`: the weights are nonnegative.

## Implementation notes

The weight takes values in `ℝ` and its index lies in `ℤ`, so that differences of indices need
no casts and a negative index simply gives weight `0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The straddle weight `p_t(j) = binom(t + 1, 2j + 1) 2^{-t}` for `j ≥ 0`, and `0` for `j < 0`. -/
@[collatz_pos_dens "def_rn_cross_p"]
noncomputable def straddleWeight (t : ℕ) (j : ℤ) : ℝ :=
  if 0 ≤ j then ((t + 1).choose (2 * j.toNat + 1) : ℝ) / 2 ^ t else 0

/-- For `j ≥ 0`, the straddle weight is `p_t(j) = binom(t + 1, 2j + 1) 2^{-t}`. -/
theorem straddleWeight_of_nonneg (t : ℕ) {j : ℤ} (hj : 0 ≤ j) :
    straddleWeight t j = ((t + 1).choose (2 * j.toNat + 1) : ℝ) / 2 ^ t := by
  simp [straddleWeight, hj]

/-- For `j < 0`, the straddle weight `p_t(j)` vanishes. -/
theorem straddleWeight_of_neg (t : ℕ) {j : ℤ} (hj : j < 0) : straddleWeight t j = 0 := by
  simp [straddleWeight, not_le.2 hj]

/-- At a natural index `j`, the straddle weight is `p_t(j) = binom(t + 1, 2j + 1) 2^{-t}`. -/
@[simp]
theorem straddleWeight_natCast (t j : ℕ) :
    straddleWeight t j = ((t + 1).choose (2 * j + 1) : ℝ) / 2 ^ t := by
  simp [straddleWeight]

/-- The straddle weights are nonnegative: `0 ≤ p_t(j)`. -/
theorem straddleWeight_nonneg (t : ℕ) (j : ℤ) : 0 ≤ straddleWeight t j := by
  unfold straddleWeight
  split_ifs
  · exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg zero_le_two _)
  · exact le_rfl

end CollatzPosDens
