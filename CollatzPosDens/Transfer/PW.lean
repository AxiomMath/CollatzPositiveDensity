/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.Lc
public import CollatzPosDens.Transfer.Z
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The many-white Taylor sum `P_W`

The white-term exponent is `x_W = 101 z_* - A_* ℓ_c`, built from the constants `zStar`, `Aexp`
and `lc`. Since `x_W > 0`, the exponential series at `x_W` has nonnegative terms, so its
degree-20 partial sum `P_W = ∑_{j=0}^{20} x_W^j / j!` is a rational lower bound for `e^{x_W}`,
and `1 / P_W` is a rational upper bound for the damping factor `e^{-x_W}`.

## Main definitions

* `CollatzPosDens.PW`: the rational number `P_W = ∑_{j=0}^{20} (101 z_* - A_* ℓ_c)^j / j!`.

## Main results

* `CollatzPosDens.PW_exponent_eq`: `101 z_* - A_* ℓ_c = 126992817/409600000`.
* `CollatzPosDens.PW_exponent_pos`: `0 < 101 z_* - A_* ℓ_c`.
* `CollatzPosDens.one_le_PW`, `CollatzPosDens.PW_pos`: `0 < 1 ≤ P_W`.
* `CollatzPosDens.lt_PW`, `CollatzPosDens.PW_lt`: the enclosure
  `1.363481093 < P_W < 1.363481094`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The many-white Taylor sum `P_W := ∑_{j=0}^{20} (101 z_* - A_* ℓ_c)^j / j! ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_PW"]
def PW : ℚ := ∑ j ∈ Finset.range 21, (101 * zStar - Aexp * lc) ^ j / (j.factorial : ℚ)

/-- Unfolding lemma for the many-white Taylor sum. -/
theorem PW_def :
    PW = ∑ j ∈ Finset.range 21, (101 * zStar - Aexp * lc) ^ j / (j.factorial : ℚ) := rfl

/-- The value of the white-term exponent `x_W = 101 z_* - A_* ℓ_c`. -/
theorem PW_exponent_eq : 101 * zStar - Aexp * lc = 126992817 / 409600000 := by
  simp only [zStar_eq, Aexp_eq, lc_eq]
  norm_num

/-- The white-term exponent `x_W = 101 z_* - A_* ℓ_c` is positive. -/
theorem PW_exponent_pos : 0 < 101 * zStar - Aexp * lc := by
  rw [PW_exponent_eq]
  norm_num

/-- The many-white Taylor sum is at least `1`, its constant term. -/
theorem one_le_PW : 1 ≤ PW := by
  rw [PW_def, Finset.sum_range_succ']
  have h : 0 ≤ ∑ j ∈ Finset.range 20,
      (101 * zStar - Aexp * lc) ^ (j + 1) / ((j + 1).factorial : ℚ) :=
    Finset.sum_nonneg fun j _ => div_nonneg (pow_nonneg PW_exponent_pos.le _) (Nat.cast_nonneg _)
  simpa using h

/-- The many-white Taylor sum is positive. -/
theorem PW_pos : 0 < PW := zero_lt_one.trans_le one_le_PW

/-- The many-white Taylor sum satisfies `1.363481093 < P_W`. -/
theorem lt_PW : (1363481093 / 1000000000 : ℚ) < PW := by
  rw [PW_def, PW_exponent_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- The many-white Taylor sum satisfies `P_W < 1.363481094`. -/
theorem PW_lt : PW < (1363481094 / 1000000000 : ℚ) := by
  rw [PW_def, PW_exponent_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

end CollatzPosDens
