/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The overshoot deviation error `U_o(ι)`

For each Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the overshoot deviation error is the positive
rational constant `U_o(ι)`, with
`U_o(o) = 295143990568991 / 10^20` and `U_o(b) = 743222777209534 / 10^20`.
It is the twenty-digit decimal ceiling of `9 (25/27)^{X_o(ι)}`, where `X_o(ι)` is the overshoot
allowance `CollatzPosDens.overshootAllowance ι`, with `X_o(o) = 194` and `X_o(b) = 182`.

## Main definitions

* `CollatzPosDens.Uo`: the overshoot deviation error `U_o(ι) : ℚ`.

## Main results

* `CollatzPosDens.Uo_o`, `CollatzPosDens.Uo_b`: the values of `U_o(o)` and `U_o(b)`.
* `CollatzPosDens.Uo_cast_o`, `CollatzPosDens.Uo_cast_b`: the same values cast into any
  division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Uo_pos`: `0 < U_o(ι)` for every `ι`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The overshoot deviation error `U_o(ι) ∈ ℚ`: `U_o(o) := 295143990568991 / 10^20` and
`U_o(b) := 743222777209534 / 10^20`. -/
@[collatz_pos_dens "def_s02_Uo"]
def Uo : FIndex → ℚ
  | .o => 295143990568991 / 10 ^ 20
  | .b => 743222777209534 / 10 ^ 20

/-- The value of the overshoot deviation error at the original index. -/
@[simp]
theorem Uo_o : Uo .o = 295143990568991 / 10 ^ 20 := rfl

/-- The value of the overshoot deviation error at the bootstrap index. -/
@[simp]
theorem Uo_b : Uo .b = 743222777209534 / 10 ^ 20 := rfl

/-- The value of the overshoot deviation error at the original index, cast into a division ring of
characteristic zero. -/
theorem Uo_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (Uo .o : K) = 295143990568991 / 10 ^ 20 := by
  rw [Uo_o, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofNat]

/-- The value of the overshoot deviation error at the bootstrap index, cast into a division ring of
characteristic zero. -/
theorem Uo_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (Uo .b : K) = 743222777209534 / 10 ^ 20 := by
  rw [Uo_b, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofNat]

/-- The overshoot deviation error is positive. -/
theorem Uo_pos (ι : FIndex) : 0 < Uo ι := by
  cases ι <;> norm_num

end CollatzPosDens
