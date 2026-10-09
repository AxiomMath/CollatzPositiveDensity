/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The trace reserve `L_*`

The trace reserve is the positive rational constant `L_* = 7046129 / 2^20 = 7046129 / 1048576`,
approximately `6.71971`. This file records its exact value, its cast into any division ring of
characteristic zero, and the bounds `0 < L_* < 7`.

## Main definitions

* `CollatzPosDens.Lstar`: the trace reserve `L_* = 7046129 / 2^20 : ℚ`.

## Main results

* `CollatzPosDens.Lstar_eq`: the value `L_* = 7046129 / 1048576`.
* `CollatzPosDens.Lstar_eq_div_two_pow`: the value `L_* = 7046129 / 2^20`.
* `CollatzPosDens.Lstar_cast`: the value of `(L_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Lstar_pos`: `0 < L_*`.
* `CollatzPosDens.Lstar_lt_seven`: `L_* < 7`.

## Implementation notes

`L_*` is a plain rational constant, so that numerical comparisons involving it can be evaluated
exactly by `norm_num`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The trace reserve `L_* := 7046129 / 2^20 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_trace_reserve"]
def Lstar : ℚ := 7046129 / 2 ^ 20

/-- The value of the trace reserve. -/
@[simp]
theorem Lstar_eq : Lstar = 7046129 / 1048576 := by
  norm_num [Lstar]

/-- The value of the trace reserve, with the denominator written as a power of two. -/
theorem Lstar_eq_div_two_pow : Lstar = 7046129 / 2 ^ 20 := rfl

/-- The value of the trace reserve cast into a division ring of characteristic zero. -/
theorem Lstar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (Lstar : K) = 7046129 / 1048576 := by
  simp [Lstar_eq]

/-- The trace reserve is positive. -/
theorem Lstar_pos : 0 < Lstar := by norm_num

/-- The trace reserve is less than `7`. -/
theorem Lstar_lt_seven : Lstar < 7 := by norm_num

end CollatzPosDens
