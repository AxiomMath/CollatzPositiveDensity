/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.D1

/-!
# The point threshold `D_pt`

The point threshold is the rational constant `D_pt = 2 D_1 + 344`, where `D_1` is the exit
threshold. Since `D_1 = 836081643217/1296`, its value is `D_pt = 836081866129/648 ≈ 1.29 · 10^9`,
in particular `D_pt < 2^31`.

## Main definitions

* `CollatzPosDens.Dpt`: the point threshold `D_pt = 2 D_1 + 344 : ℚ`.

## Main results

* `CollatzPosDens.Dpt_def`: the defining formula in terms of `D_1`.
* `CollatzPosDens.Dpt_eq`: the value `D_pt = 836081866129/648`.
* `CollatzPosDens.Dpt_cast`: the value of `(D_pt : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.D1_lt_Dpt`, `CollatzPosDens.Dpt_pos`, `CollatzPosDens.Dpt_lt`:
  the bounds `0 < D_1 < D_pt < 2^31`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The point threshold `D_pt := 2 D_1 + 344 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_Dpt"]
def Dpt : ℚ := 2 * D1 + 344

/-- The defining formula of the point threshold. -/
theorem Dpt_def : Dpt = 2 * D1 + 344 := rfl

/-- The value of the point threshold. -/
@[simp]
theorem Dpt_eq : Dpt = 836081866129 / 648 := by
  norm_num [Dpt_def, D1_eq]

/-- The value of the point threshold cast into a division ring of characteristic zero. -/
theorem Dpt_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (Dpt : K) = 836081866129 / 648 := by
  simp [Dpt_eq]

/-- The exit threshold is below the point threshold. -/
theorem D1_lt_Dpt : D1 < Dpt := by
  norm_num

/-- The point threshold is positive. -/
theorem Dpt_pos : 0 < Dpt := by norm_num

/-- The point threshold is below `2 ^ 31`. -/
theorem Dpt_lt : Dpt < 2 ^ 31 := by norm_num

end CollatzPosDens
