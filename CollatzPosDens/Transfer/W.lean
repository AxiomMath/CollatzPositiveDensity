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
# The near-top tilt allowance `w_*`

The near-top tilt allowance is the positive rational constant `w_* = 63/2500`. It satisfies
`0 < w_* ≤ 1/32`, and with `CollatzPosDens.zStar = 21/500` it satisfies
`zStar - w_*/2 = 147/5000 ≥ 0`.

## Main definitions

* `CollatzPosDens.wStar`: the near-top tilt allowance `w_* = 63/2500 : ℚ`.

## Main results

* `CollatzPosDens.wStar_eq`: the value `w_* = 63/2500`.
* `CollatzPosDens.wStar_cast`: the value of `(w_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.wStar_pos`: `0 < w_*`.
* `CollatzPosDens.wStar_le_one_div_32`: `w_* ≤ 1/32`, and hence
  `CollatzPosDens.wStar_le_one`: `w_* ≤ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The near-top tilt allowance `w_* := 63/2500 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_w"]
def wStar : ℚ := 63 / 2500

/-- The value of the near-top tilt allowance. -/
@[simp]
theorem wStar_eq : wStar = 63 / 2500 := rfl

/-- The value of the near-top tilt allowance cast into a division ring of characteristic zero. -/
theorem wStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (wStar : K) = 63 / 2500 := by
  simp [wStar_eq]

/-- The near-top tilt allowance is positive. -/
theorem wStar_pos : 0 < wStar := by norm_num

/-- The near-top tilt allowance is at most `1/32`. -/
theorem wStar_le_one_div_32 : wStar ≤ 1 / 32 := by norm_num

/-- The near-top tilt allowance is at most `1`. -/
theorem wStar_le_one : wStar ≤ 1 := by norm_num

end CollatzPosDens
