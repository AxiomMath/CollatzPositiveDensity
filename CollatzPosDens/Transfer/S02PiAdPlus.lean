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
# The rounded adaptive packing sum `Π⁺_ad(ι)`

For each Fourier parameter index `ι ∈ 𝔍 = {o, b}`, the rounded adaptive packing sum is the
positive rational constant `Π⁺_ad(ι)`, with `Π⁺_ad(o) = 117855141445251/10^16 ≈ 0.01179` and
`Π⁺_ad(b) = 172936863842033/10^16 ≈ 0.01729`. It is an explicit upper rounding of the adaptive
packing sum `Π_ad(ι)`, a finite sum of explicit rationals.

## Main definitions

* `CollatzPosDens.piAdPlus`: the rounded adaptive packing sum `Π⁺_ad(ι) : ℚ`.

## Main results

* `CollatzPosDens.piAdPlus_o`, `CollatzPosDens.piAdPlus_b`: the values of `Π⁺_ad(o)` and
  `Π⁺_ad(b)`.
* `CollatzPosDens.piAdPlus_cast_o`, `CollatzPosDens.piAdPlus_cast_b`: the same values cast into
  any division ring of characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.piAdPlus_pos`: `0 < Π⁺_ad(ι)`.
* `CollatzPosDens.piAdPlus_lt_one`: `Π⁺_ad(ι) < 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The rounded adaptive packing sum `Π⁺_ad(ι) ∈ ℚ` of the Fourier parameter set `ι`, an
explicit upper rounding of the adaptive packing sum: `Π⁺_ad(o) = 117855141445251/10^16` and
`Π⁺_ad(b) = 172936863842033/10^16`. -/
@[collatz_pos_dens "def_s02_Pi_ad_plus"]
def piAdPlus : FIndex → ℚ
  | .o => 117855141445251 / 10 ^ 16
  | .b => 172936863842033 / 10 ^ 16

/-- The value of the rounded adaptive packing sum at the original index. -/
@[simp]
theorem piAdPlus_o : piAdPlus .o = 117855141445251 / 10 ^ 16 := rfl

/-- The value of the rounded adaptive packing sum at the bootstrap index. -/
@[simp]
theorem piAdPlus_b : piAdPlus .b = 172936863842033 / 10 ^ 16 := rfl

/-- The value of the rounded adaptive packing sum at the original index, cast into a division
ring of characteristic zero. -/
theorem piAdPlus_cast_o {K : Type*} [DivisionRing K] [CharZero K] :
    (piAdPlus .o : K) = 117855141445251 / 10 ^ 16 := by
  rw [piAdPlus_o]; norm_num

/-- The value of the rounded adaptive packing sum at the bootstrap index, cast into a division
ring of characteristic zero. -/
theorem piAdPlus_cast_b {K : Type*} [DivisionRing K] [CharZero K] :
    (piAdPlus .b : K) = 172936863842033 / 10 ^ 16 := by
  rw [piAdPlus_b]; norm_num

/-- The rounded adaptive packing sum is positive. -/
theorem piAdPlus_pos (ι : FIndex) : 0 < piAdPlus ι := by
  cases ι <;> norm_num

/-- The rounded adaptive packing sum is less than one. -/
theorem piAdPlus_lt_one (ι : FIndex) : piAdPlus ι < 1 := by
  cases ι <;> norm_num

end CollatzPosDens
