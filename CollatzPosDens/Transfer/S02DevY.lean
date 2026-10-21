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
# The vertical generating-function point `y_dv`

For each Fourier index `ι ∈ 𝔍 = {o, b}` the vertical generating-function point is the rational
constant `y_dv(ι)`, slightly larger than `1`: `y_dv(o) = 169/168` and `y_dv(b) = 144/143`.

## Main definitions

* `CollatzPosDens.devY`: `y_dv(ι) : ℚ` for `ι ∈ 𝔍 = {o, b}`, with `y_dv(o) = 169/168` and
  `y_dv(b) = 144/143`.

## Main results

* `CollatzPosDens.devY_o`, `CollatzPosDens.devY_b`: the two values.
* `CollatzPosDens.devY_cast_o`, `CollatzPosDens.devY_cast_b`: the two values cast into a
  division ring of characteristic zero.
* `CollatzPosDens.devY_pos`, `CollatzPosDens.devY_nonneg`: `y_dv(ι)` is positive.
* `CollatzPosDens.one_lt_devY`, `CollatzPosDens.devY_lt_two`: `1 < y_dv(ι) < 2`.
* `CollatzPosDens.devY_inv_o`, `CollatzPosDens.devY_inv_b`: `y_dv(o)⁻¹ = 168/169` and
  `y_dv(b)⁻¹ = 143/144`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The vertical generating-function point `y_dv(ι) ∈ ℚ`: `y_dv(o) := 169/168` and
`y_dv(b) := 144/143`. -/
@[collatz_pos_dens "def_s02_dev_y"]
def devY : FIndex → ℚ
  | .o => 169 / 168
  | .b => 144 / 143

/-- The value of `y_dv` at the original index `o`. -/
@[simp]
theorem devY_o : devY .o = 169 / 168 := rfl

/-- The value of `y_dv` at the bootstrap index `b`. -/
@[simp]
theorem devY_b : devY .b = 144 / 143 := rfl

/-- The value of `y_dv(o)` cast into a division ring of characteristic zero. -/
theorem devY_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (devY .o : K) = 169 / 168 := by
  simp [devY_o]

/-- The value of `y_dv(b)` cast into a division ring of characteristic zero. -/
theorem devY_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (devY .b : K) = 144 / 143 := by
  simp [devY_b]

/-- `y_dv(ι)` is positive. -/
theorem devY_pos (ι : FIndex) : 0 < devY ι := by
  cases ι <;> norm_num

/-- `y_dv(ι)` is nonnegative. -/
theorem devY_nonneg (ι : FIndex) : 0 ≤ devY ι := (devY_pos ι).le

/-- The vertical generating-function point exceeds `1`. -/
theorem one_lt_devY (ι : FIndex) : 1 < devY ι := by
  cases ι <;> norm_num

/-- The vertical generating-function point is less than `2`. -/
theorem devY_lt_two (ι : FIndex) : devY ι < 2 := by
  cases ι <;> norm_num

/-- The inverse of the vertical generating-function point at the original index. -/
theorem devY_inv_o : (devY .o)⁻¹ = 168 / 169 := by norm_num

/-- The inverse of the vertical generating-function point at the bootstrap index. -/
theorem devY_inv_b : (devY .b)⁻¹ = 143 / 144 := by norm_num

end CollatzPosDens
