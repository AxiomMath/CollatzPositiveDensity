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
# The vertical deviation error `U_v(ι)`

For each Fourier parameter index `ι : FIndex`, the vertical deviation error is the positive
rational constant `U_v(ι)`, with `U_v(o) = 13370061336019939 / 10^20` and
`U_v(b) = 27986092430721741 / 10^20`. It is the twenty-digit decimal ceiling of
`devY ι ^ (-Xl ι 0)`, that is of `(168/169)^1503` and of `(143/144)^1174`, and bounds the vertical
part of the fresh deviation mass.

## Main definitions

* `CollatzPosDens.Uv`: the vertical deviation error `U_v(ι) : ℚ`.

## Main results

* `CollatzPosDens.Uv_o`, `CollatzPosDens.Uv_b`: the values of `U_v(o)` and `U_v(b)`.
* `CollatzPosDens.Uv_cast_o`, `CollatzPosDens.Uv_cast_b`: the same values cast into any
  division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Uv_pos`: `0 < U_v(ι)` for every `ι`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The vertical deviation error `U_v(ι) ∈ ℚ`: `U_v(o) := 13370061336019939 / 10^20` and
`U_v(b) := 27986092430721741 / 10^20`. -/
@[collatz_pos_dens "def_s02_Uv"]
def Uv : FIndex → ℚ
  | .o => 13370061336019939 / 10 ^ 20
  | .b => 27986092430721741 / 10 ^ 20

/-- The value of the vertical deviation error at the original index. -/
@[simp]
theorem Uv_o : Uv .o = 13370061336019939 / 10 ^ 20 := rfl

/-- The value of the vertical deviation error at the bootstrap index. -/
@[simp]
theorem Uv_b : Uv .b = 27986092430721741 / 10 ^ 20 := rfl

/-- The value of the vertical deviation error at the original index, cast into a division ring of
characteristic zero. -/
theorem Uv_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (Uv .o : K) = 13370061336019939 / 10 ^ 20 := by
  rw [Uv_o, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofNat]

/-- The value of the vertical deviation error at the bootstrap index, cast into a division ring of
characteristic zero. -/
theorem Uv_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (Uv .b : K) = 27986092430721741 / 10 ^ 20 := by
  rw [Uv_b, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofNat]

/-- The vertical deviation error is positive. -/
theorem Uv_pos (ι : FIndex) : 0 < Uv ι := by
  cases ι <;> norm_num

end CollatzPosDens
