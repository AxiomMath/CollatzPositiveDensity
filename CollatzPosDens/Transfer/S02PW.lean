/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Xwc
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The many-white Taylor sum `P_W(ι)`

For a Fourier index `ι`, let `x_W(ι) > 0` be the many-white exponent `CollatzPosDens.xW`. The
exponential series at `x_W(ι)` has nonnegative terms, so its degree-20 partial sum
`P_W(ι) = ∑_{j=0}^{20} x_W(ι)^j / j!` is a rational lower bound for `e^{x_W(ι)}`, and `1 / P_W(ι)`
is a rational upper bound for the damping factor `e^{-x_W(ι)}`. One has `P_W(o) = 126.2981262561…`
and `P_W(b) = 87.9359744815…`.

## Main definitions

* `CollatzPosDens.PW`: the rational number `P_W(ι) = ∑_{j=0}^{20} x_W(ι)^j / j!`.

## Main results

* `CollatzPosDens.one_le_PW`, `CollatzPosDens.PW_pos`: `0 < 1 ≤ P_W(ι)`.
* `CollatzPosDens.PW_o_gt`, `CollatzPosDens.PW_o_lt`: `126.298126 < P_W(o) < 126.298127`.
* `CollatzPosDens.PW_b_gt`, `CollatzPosDens.PW_b_lt`: `87.935974 < P_W(b) < 87.935975`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The many-white Taylor sum `P_W(ι) := ∑_{j=0}^{20} x_W(ι)^j / j! ∈ ℚ` of the Fourier index
`ι`. -/
@[collatz_pos_dens "def_s02_PW"]
def PW (ι : FIndex) : ℚ := ∑ j ∈ Finset.range 21, xW ι ^ j / (j.factorial : ℚ)

/-- Unfolding lemma for the many-white Taylor sum. -/
theorem PW_def (ι : FIndex) : PW ι = ∑ j ∈ Finset.range 21, xW ι ^ j / (j.factorial : ℚ) := rfl

/-- The many-white Taylor sum is at least `1`, its constant term. -/
theorem one_le_PW (ι : FIndex) : 1 ≤ PW ι := by
  rw [PW_def, Finset.sum_range_succ']
  have h : 0 ≤ ∑ j ∈ Finset.range 20, xW ι ^ (j + 1) / ((j + 1).factorial : ℚ) :=
    Finset.sum_nonneg fun j _ => div_nonneg (pow_nonneg (xW_pos ι).le _) (Nat.cast_nonneg _)
  simpa using h

/-- The many-white Taylor sum is positive. -/
theorem PW_pos (ι : FIndex) : 0 < PW ι := zero_lt_one.trans_le (one_le_PW ι)

/-- The many-white Taylor sum at the original index satisfies `126.298126 < P_W(o)`. -/
theorem PW_o_gt : (126298126 / 1000000 : ℚ) < PW .o := by
  rw [PW_def, xW_o]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- The many-white Taylor sum at the original index satisfies `P_W(o) < 126.298127`. -/
theorem PW_o_lt : PW .o < (126298127 / 1000000 : ℚ) := by
  rw [PW_def, xW_o]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- The many-white Taylor sum at the bootstrap index satisfies `87.935974 < P_W(b)`. -/
theorem PW_b_gt : (87935974 / 1000000 : ℚ) < PW .b := by
  rw [PW_def, xW_b]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- The many-white Taylor sum at the bootstrap index satisfies `P_W(b) < 87.935975`. -/
theorem PW_b_lt : PW .b < (87935975 / 1000000 : ℚ) := by
  rw [PW_def, xW_b]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

end CollatzPosDens
