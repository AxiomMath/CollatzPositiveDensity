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
# The two-passage correction `Ω_*`

The two-passage correction is the explicit positive rational constant
`Ω_* = 17900546471008806829928229500985832153923 / 14265091358720000000000000000000000000000000`,
approximately `0.001254851…`. It is subtracted from the square of the single-passage survival
`1 - d_*`, where `d_* = CollatzPosDens.dStar`, to give the two-passage rate
`ϱ_* = (1 - d_*)^2 - Ω_*`, which is `CollatzPosDens.rhoStar`.

## Main definitions

* `CollatzPosDens.omegaStar`: the two-passage correction `Ω_* ∈ ℚ`.

## Main results

* `CollatzPosDens.omegaStar_eq`: the value of `Ω_*`.
* `CollatzPosDens.omegaStar_cast`: the value of `(Ω_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.omegaStar_pos`, `CollatzPosDens.omegaStar_lt_one`: `0 < Ω_* < 1`.

## Implementation notes

The constant is defined in `ℚ` so that downstream inequalities involving it can be decided by
`norm_num`; it is cast to `ℝ` where it is used analytically.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The two-passage correction
`Ω_* := 17900546471008806829928229500985832153923 / 14265091358720000000000000000000000000000000`
in `ℚ`. -/
@[collatz_pos_dens "def_s02_Omega"]
def omegaStar : ℚ :=
  17900546471008806829928229500985832153923 / 14265091358720000000000000000000000000000000

/-- The value of the two-passage correction. -/
@[simp]
theorem omegaStar_eq :
    omegaStar =
      17900546471008806829928229500985832153923 /
        14265091358720000000000000000000000000000000 := rfl

/-- The value of the two-passage correction cast into a division ring of characteristic zero. -/
theorem omegaStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (omegaStar : K) =
      17900546471008806829928229500985832153923 /
        14265091358720000000000000000000000000000000 := by
  rw [omegaStar_eq]; push_cast; rfl

/-- The two-passage correction is positive. -/
theorem omegaStar_pos : 0 < omegaStar := by
  rw [omegaStar_eq]; norm_num

/-- The two-passage correction is less than one. -/
theorem omegaStar_lt_one : omegaStar < 1 := by
  rw [omegaStar_eq]; norm_num

end CollatzPosDens
