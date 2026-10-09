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
# The white Fourier penalty

This file defines the white Fourier penalty `z_* = 21/500`, a positive rational constant
measuring the Fourier decay gained per white letter of a Collatz word.

## Main definitions

* `CollatzPosDens.zStar`: the rational number `z_* = 21/500`.

## Main results

* `CollatzPosDens.zStar_eq`: the value `z_* = 21/500`.
* `CollatzPosDens.zStar_cast`: the value of `(z_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.zStar_pos`: `0 < z_*`.

## Implementation notes

The constant is defined in `ℚ` so that rational expressions in it can be evaluated exactly;
its image in `ℝ` is computed by `zStar_cast`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The white Fourier penalty `z_* := 21/500 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_z"]
def zStar : ℚ := 21 / 500

/-- The value of the white Fourier penalty. -/
@[simp]
theorem zStar_eq : zStar = 21 / 500 := rfl

/-- The value of the white Fourier penalty cast into a division ring of characteristic zero. -/
theorem zStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (zStar : K) = 21 / 500 := by
  simp [zStar_eq]

/-- The white Fourier penalty is positive. -/
theorem zStar_pos : 0 < zStar := by norm_num

/-- The white Fourier penalty is nonnegative. -/
theorem zStar_nonneg : 0 ≤ zStar := zStar_pos.le

/-- The white Fourier penalty lies below `1`. -/
theorem zStar_lt_one : zStar < 1 := by norm_num

end CollatzPosDens
