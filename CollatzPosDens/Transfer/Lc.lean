/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The continuation logarithm `ℓ_c`

The continuation logarithm is the positive rational constant `ℓ_c = 157263/100000`. It is a
rational upper bound for `log (400/83)`: the degree-20 partial sum of the exponential series at
`ℓ_c` already exceeds `400/83`.

## Main definitions

* `CollatzPosDens.lc`: the continuation logarithm `ℓ_c = 157263/100000 : ℚ`.

## Main results

* `CollatzPosDens.lc_eq`: the value `ℓ_c = 157263/100000`.
* `CollatzPosDens.lc_cast`: the value of `(ℓ_c : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.lc_pos`: `0 < ℓ_c`.
* `CollatzPosDens.lc_expPartialSum_gt`: `400/83 < ∑_{j=0}^{20} ℓ_c^j / j!`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The continuation logarithm `ℓ_c := 157263/100000 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_lc"]
def lc : ℚ := 157263 / 100000

/-- The value of the continuation logarithm. -/
@[simp]
theorem lc_eq : lc = 157263 / 100000 := rfl

/-- The value of the continuation logarithm cast into a division ring of characteristic zero. -/
theorem lc_cast {K : Type*} [DivisionRing K] [CharZero K] : (lc : K) = 157263 / 100000 := by
  simp

/-- The continuation logarithm is positive. -/
theorem lc_pos : 0 < lc := by norm_num

/-- The degree-20 partial sum of the exponential series at `ℓ_c` exceeds `400/83`. -/
theorem lc_expPartialSum_gt :
    (400 / 83 : ℚ) < ∑ j ∈ Finset.range 21, lc ^ j / (j.factorial : ℚ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, lc_eq]
  norm_num

end CollatzPosDens
