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

The white Fourier penalty is the positive rational constant `z_* = 133/3125`, the Fourier
cancellation paid at a white point. It appears in exponential factors `e^{-λ z_*}` and in
rational bounds built from it.

## Main definitions

* `CollatzPosDens.zStar`: the rational number `z_* = 133/3125`.

## Main results

* `CollatzPosDens.zStar_eq`: the value `z_* = 133/3125`.
* `CollatzPosDens.zStar_cast`: the value of `(z_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.zStar_pos`: `0 < z_*`.

## Implementation notes

The constant is kept in `ℚ`, so that the rational sums built from it can be evaluated
exactly; real-valued uses cast it to `ℝ` and rewrite with `zStar_cast`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The white Fourier penalty `z_* := 133/3125 ∈ ℚ`, the cancellation at a white point. -/
@[collatz_pos_dens "def_s02_z"]
def zStar : ℚ := 133 / 3125

/-- The value of the white Fourier penalty. -/
@[simp]
theorem zStar_eq : zStar = 133 / 3125 := rfl

/-- The value of the white Fourier penalty cast into a division ring of characteristic zero. -/
theorem zStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (zStar : K) = 133 / 3125 := by
  simp [zStar_eq]

/-- The white Fourier penalty is positive. -/
theorem zStar_pos : 0 < zStar := by norm_num

/-- The white Fourier penalty is nonnegative. -/
theorem zStar_nonneg : 0 ≤ zStar := zStar_pos.le

/-- The white Fourier penalty lies below `1`. -/
theorem zStar_lt_one : zStar < 1 := by norm_num

end CollatzPosDens
