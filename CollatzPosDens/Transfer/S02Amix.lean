/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.S02Aexp

/-!
# The profile exponent `a_mx(ι)`

For each Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the profile exponent is the rational constant
`a_mx(ι) := A_*(ι) - 1/4`, where `A_*(ι)` is the decay exponent `CollatzPosDens.Aexp`. Its values
are `a_mx(o) = 18693/10000` and `a_mx(b) = 29/20`. It is the exponent of the propagation mixing
profile of the parameter set `ι`.

## Main definitions

* `CollatzPosDens.amix`: the profile exponent `a_mx(ι) := A_*(ι) - 1/4 : ℚ`.

## Main results

* `CollatzPosDens.amix_o`, `CollatzPosDens.amix_b`: the values `a_mx(o) = 18693/10000` and
  `a_mx(b) = 29/20`.
* `CollatzPosDens.amix_cast_o`, `CollatzPosDens.amix_cast_b`: the same values cast into any
  division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.amix_pos`, `CollatzPosDens.one_lt_amix`, `CollatzPosDens.amix_lt_two`,
  `CollatzPosDens.amix_lt_Aexp`: the bounds `0 < 1 < a_mx(ι) < 2` and `a_mx(ι) < A_*(ι)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The profile exponent `a_mx(ι) := A_*(ι) - 1/4 ∈ ℚ`, the exponent of the propagation mixing
profile of the Fourier parameter set `ι`. -/
@[collatz_pos_dens "def_s02_amix"]
def amix (ι : FIndex) : ℚ := Aexp ι - 1 / 4

/-- The profile exponent is the decay exponent minus `1/4`. -/
theorem amix_eq_Aexp_sub (ι : FIndex) : amix ι = Aexp ι - 1 / 4 := rfl

/-- The value of the profile exponent at the original index. -/
@[simp]
theorem amix_o : amix .o = 18693 / 10000 := by
  rw [amix_eq_Aexp_sub, Aexp_o]; norm_num

/-- The value of the profile exponent at the bootstrap index. -/
@[simp]
theorem amix_b : amix .b = 29 / 20 := by
  rw [amix_eq_Aexp_sub, Aexp_b]; norm_num

/-- The value of the profile exponent at the original index, cast into a division ring of
characteristic zero. -/
theorem amix_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (amix .o : K) = 18693 / 10000 := by
  simp [amix_o]

/-- The value of the profile exponent at the bootstrap index, cast into a division ring of
characteristic zero. -/
theorem amix_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (amix .b : K) = 29 / 20 := by
  simp [amix_b]

/-- The profile exponent is positive. -/
theorem amix_pos (ι : FIndex) : 0 < amix ι := by
  cases ι <;> norm_num

/-- The profile exponent exceeds `1`. -/
theorem one_lt_amix (ι : FIndex) : 1 < amix ι := by
  cases ι <;> norm_num

/-- The profile exponent is below `2`. -/
theorem amix_lt_two (ι : FIndex) : amix ι < 2 := by
  cases ι <;> norm_num

/-- The profile exponent is below the decay exponent. -/
theorem amix_lt_Aexp (ι : FIndex) : amix ι < Aexp ι := by
  cases ι <;> norm_num

end CollatzPosDens
