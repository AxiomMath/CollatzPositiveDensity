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
# The drift-free deviation error `U_d(ι)`

For each Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the drift-free deviation error is the positive
rational constant `U_d(ι)`, with
`U_d(o) = 6230745211954701 / 10^20` and `U_d(b) = 13539748627993287 / 10^20`.
It is the twenty-digit decimal ceiling of the drift-free deviation tail
`2 b_dv(ι)^{-4 X_d(ι, 0)}`, that is of `2 (50/51)^524` and of `2 (42/43)^408`.

## Main definitions

* `CollatzPosDens.Ud`: the drift-free deviation error `U_d(ι) : ℚ`.

## Main results

* `CollatzPosDens.Ud_o`, `CollatzPosDens.Ud_b`: the values of `U_d(o)` and `U_d(b)`.
* `CollatzPosDens.Ud_cast_o`, `CollatzPosDens.Ud_cast_b`: the same values cast into any
  division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Ud_pos`: `0 < U_d(ι)` for every `ι`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The drift-free deviation error `U_d(ι) ∈ ℚ`: `U_d(o) := 6230745211954701 / 10^20` and
`U_d(b) := 13539748627993287 / 10^20`. -/
@[collatz_pos_dens "def_s02_Ud"]
def Ud : FIndex → ℚ
  | .o => 6230745211954701 / 10 ^ 20
  | .b => 13539748627993287 / 10 ^ 20

/-- The value of the drift-free deviation error at the original index. -/
@[simp]
theorem Ud_o : Ud .o = 6230745211954701 / 10 ^ 20 := rfl

/-- The value of the drift-free deviation error at the bootstrap index. -/
@[simp]
theorem Ud_b : Ud .b = 13539748627993287 / 10 ^ 20 := rfl

/-- The value of the drift-free deviation error at the original index, cast into a division ring of
characteristic zero. -/
theorem Ud_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (Ud .o : K) = 6230745211954701 / 10 ^ 20 := by
  rw [Ud_o, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofNat]

/-- The value of the drift-free deviation error at the bootstrap index, cast into a division ring
of characteristic zero. -/
theorem Ud_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (Ud .b : K) = 13539748627993287 / 10 ^ 20 := by
  rw [Ud_b, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofNat]

/-- The drift-free deviation error is positive. -/
theorem Ud_pos (ι : FIndex) : 0 < Ud ι := by
  cases ι <;> norm_num

end CollatzPosDens
