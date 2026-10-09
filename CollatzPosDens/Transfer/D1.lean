/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.W

/-!
# The exit threshold `D_1`

The exit threshold is the rational constant `D_1 = (256 A_* / w_*)^2 + 2`, built from the decay
exponent `A_* = 10241/4096` and the near-top tilt allowance `w_* = 63/2500`. Since
`256 A_* / w_* = 914375/36`, its value is `D_1 = 836081643217/1296 ≈ 6.45 · 10^8`.

## Main definitions

* `CollatzPosDens.D1`: the exit threshold `D_1 = (256 A_* / w_*)^2 + 2 : ℚ`.

## Main results

* `CollatzPosDens.D1_def`: the defining formula in terms of `A_*` and `w_*`.
* `CollatzPosDens.D1_eq`: the value `D_1 = 836081643217/1296`.
* `CollatzPosDens.D1_cast`: the value of `(D_1 : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.two_lt_D1`, `CollatzPosDens.D1_pos`,
  `CollatzPosDens.D1_lt`: the bounds `0 < 2 < D_1 < 645124725`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The exit threshold `D_1 := (256 A_* / w_*)^2 + 2 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_D1"]
def D1 : ℚ := (256 * Aexp / wStar) ^ 2 + 2

/-- The defining formula of the exit threshold. -/
theorem D1_def : D1 = (256 * Aexp / wStar) ^ 2 + 2 := rfl

/-- The value of the exit threshold. -/
@[simp]
theorem D1_eq : D1 = 836081643217 / 1296 := by
  norm_num [D1_def]

/-- The value of the exit threshold cast into a division ring of characteristic zero. -/
theorem D1_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (D1 : K) = 836081643217 / 1296 := by
  simp [D1_eq]

/-- The exit threshold exceeds `2`. -/
theorem two_lt_D1 : 2 < D1 := by norm_num

/-- The exit threshold is positive. -/
theorem D1_pos : 0 < D1 := by norm_num

/-- The exit threshold is below `645124725`. -/
theorem D1_lt : D1 < 645124725 := by norm_num

end CollatzPosDens
