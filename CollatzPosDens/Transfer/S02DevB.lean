/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The drift-free generating-function base

For each Fourier index `ι : FIndex`, the drift-free generating-function base `devB ι` is a
rational constant greater than `1`: `devB .o = 51 / 50` and `devB .b = 43 / 42`.

## Main definitions

* `CollatzPosDens.devB`: the base `devB ι : ℚ`, with `devB .o = 51 / 50` and
  `devB .b = 43 / 42`.

## Main results

* `CollatzPosDens.devB_o`, `CollatzPosDens.devB_b`: the two values.
* `CollatzPosDens.devB_cast_o`, `CollatzPosDens.devB_cast_b`: the two values cast into a
  division ring of characteristic zero.
* `CollatzPosDens.devB_pos`, `CollatzPosDens.devB_nonneg`: `devB ι` is positive.
* `CollatzPosDens.one_lt_devB`: `1 < devB ι`.
* `CollatzPosDens.devB_inv_o`, `CollatzPosDens.devB_inv_b`: `(devB .o)⁻¹ = 50 / 51` and
  `(devB .b)⁻¹ = 42 / 43`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The drift-free generating-function base `devB ι ∈ ℚ`: `devB .o = 51 / 50` and
`devB .b = 43 / 42`. -/
@[collatz_pos_dens "def_s02_dev_b"]
def devB : FIndex → ℚ
  | .o => 51 / 50
  | .b => 43 / 42

/-- The value of `devB` at the original index `o`. -/
@[simp]
theorem devB_o : devB .o = 51 / 50 := rfl

/-- The value of `devB` at the bootstrap index `b`. -/
@[simp]
theorem devB_b : devB .b = 43 / 42 := rfl

/-- The value of `devB .o` cast into a division ring of characteristic zero. -/
theorem devB_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (devB .o : K) = 51 / 50 := by
  simp [devB_o]

/-- The value of `devB .b` cast into a division ring of characteristic zero. -/
theorem devB_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (devB .b : K) = 43 / 42 := by
  simp [devB_b]

/-- `devB ι` is positive. -/
theorem devB_pos (ι : FIndex) : 0 < devB ι := by
  cases ι <;> norm_num

/-- `devB ι` is nonnegative. -/
theorem devB_nonneg (ι : FIndex) : 0 ≤ devB ι := (devB_pos ι).le

/-- The drift-free generating-function base exceeds `1`. -/
theorem one_lt_devB (ι : FIndex) : 1 < devB ι := by
  cases ι <;> norm_num

/-- The inverse of the drift-free generating-function base at the original index. -/
theorem devB_inv_o : (devB .o)⁻¹ = 50 / 51 := by norm_num

/-- The inverse of the drift-free generating-function base at the bootstrap index. -/
theorem devB_inv_b : (devB .b)⁻¹ = 42 / 43 := by norm_num

end CollatzPosDens
