/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum

/-!
# The colour scale `ε_*`

The colour scale is the positive rational constant `ε_* = 37037/10⁶`. It is the angle threshold
separating black from white points: a lattice point in the lower half is white when its angle
exceeds `ε_*` in absolute value, and black otherwise. The geometry of the black set is valid for
every colouring parameter `0 < ε < 1/27`, and the construction uses `ε = ε_*`, which lies in that
range since `37037 · 27 = 999999 < 10⁶`.

## Main definitions

* `CollatzPosDens.epsStar`: the colour scale `ε_* = 37037/10⁶ : ℚ`.

## Main results

* `CollatzPosDens.epsStar_eq`: the value `ε_* = 37037/10⁶`.
* `CollatzPosDens.epsStar_cast`: the value of `(ε_* : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.epsStar_pos`: `0 < ε_*`.
* `CollatzPosDens.epsStar_lt_one_div_27`: `ε_* < 1/27`, and hence
  `CollatzPosDens.epsStar_lt_one_div_four`: `ε_* < 1/4`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The colour scale `ε_* := 37037/10⁶ ∈ ℚ_{>0}`, the angle threshold separating black from
white points. -/
@[collatz_pos_dens "def_eps_star"]
def epsStar : ℚ := 37037 / 10 ^ 6

/-- The value of the colour scale. -/
@[simp]
theorem epsStar_eq : epsStar = 37037 / 10 ^ 6 := rfl

/-- The value of the colour scale cast into a division ring of characteristic zero. -/
theorem epsStar_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (epsStar : K) = 37037 / 10 ^ 6 := by
  simp [Rat.cast_pow]

/-- The colour scale is positive. -/
theorem epsStar_pos : 0 < epsStar := by norm_num

/-- The colour scale lies below `1/27`, the range of validity of the black-set geometry. -/
theorem epsStar_lt_one_div_27 : epsStar < 1 / 27 := by norm_num

/-- The colour scale lies below `1/4`. -/
theorem epsStar_lt_one_div_four : epsStar < 1 / 4 := by norm_num

end CollatzPosDens
