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
# The decay exponent `A_*(ι)`

For each Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the decay exponent is the positive rational
constant `A_*(ι)`, with `A_*(o) = 21193/10000` and `A_*(b) = 17/10`. It is the exponent of the
Fourier decay of the parameter set `ι`.

## Main definitions

* `CollatzPosDens.Aexp`: the decay exponent `A_*(ι) : ℚ`.

## Main results

* `CollatzPosDens.Aexp_o`, `CollatzPosDens.Aexp_b`: the values `A_*(o) = 21193/10000` and
  `A_*(b) = 17/10`.
* `CollatzPosDens.Aexp_cast_o`, `CollatzPosDens.Aexp_cast_b`: the same values cast into any
  division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.Aexp_pos`, `CollatzPosDens.one_lt_Aexp`, `CollatzPosDens.Aexp_lt_three`: the
  bounds `0 < 1 < A_*(ι) < 3` for every `ι`.
* `CollatzPosDens.two_lt_Aexp_o`, `CollatzPosDens.Aexp_b_lt_two`: `A_*(b) < 2 < A_*(o)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The decay exponent `A_*(ι) ∈ ℚ` of the Fourier parameter set `ι`: `A_*(o) = 21193/10000` and
`A_*(b) = 17/10`. -/
@[collatz_pos_dens "def_s02_Aexp"]
def Aexp : FIndex → ℚ
  | .o => 21193 / 10000
  | .b => 17 / 10

/-- The value of the decay exponent at the original index. -/
@[simp]
theorem Aexp_o : Aexp .o = 21193 / 10000 := rfl

/-- The value of the decay exponent at the bootstrap index. -/
@[simp]
theorem Aexp_b : Aexp .b = 17 / 10 := rfl

/-- The value of the decay exponent at the original index, cast into a division ring of
characteristic zero. -/
theorem Aexp_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (Aexp .o : K) = 21193 / 10000 := by
  simp [Aexp_o]

/-- The value of the decay exponent at the bootstrap index, cast into a division ring of
characteristic zero. -/
theorem Aexp_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (Aexp .b : K) = 17 / 10 := by
  simp [Aexp_b]

/-- The decay exponent is positive. -/
theorem Aexp_pos (ι : FIndex) : 0 < Aexp ι := by
  cases ι <;> norm_num

/-- The decay exponent exceeds `1`. -/
theorem one_lt_Aexp (ι : FIndex) : 1 < Aexp ι := by
  cases ι <;> norm_num

/-- The decay exponent is below `3`. -/
theorem Aexp_lt_three (ι : FIndex) : Aexp ι < 3 := by
  cases ι <;> norm_num

/-- The decay exponent of the original parameter set exceeds `2`. -/
theorem two_lt_Aexp_o : 2 < Aexp .o := by norm_num

/-- The decay exponent of the bootstrap parameter set is below `2`. -/
theorem Aexp_b_lt_two : Aexp .b < 2 := by norm_num

end CollatzPosDens
