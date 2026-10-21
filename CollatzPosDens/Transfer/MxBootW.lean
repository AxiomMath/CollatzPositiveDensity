/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxChainRatio

/-!
# The quadratic coefficient of the bootstrap profile

The propagation mixing profile of the bootstrap index carries the term `w_b x⁻²`, whose
coefficient is the rational constant `w_b := 15 / (c_bt ^ 2 - 1)`, where `c_bt` is the ratio
`CollatzPosDens.bootChainRatio` of the bootstrap chaining. Its value is
`w_b = 15000000/164241`, in particular `w_b > 0`.

## Main definitions

* `CollatzPosDens.bootW`: the coefficient `w_b := 15 / (c_bt ^ 2 - 1) : ℚ`.

## Main results

* `CollatzPosDens.bootW_val`, `CollatzPosDens.bootW_cast`: `w_b = 15000000/164241`, in `ℚ` and
  cast into a division ring of characteristic zero.
* `CollatzPosDens.bootW_pos`: `0 < w_b`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The quadratic coefficient of the bootstrap profile, `w_b := 15 / (c_bt ^ 2 - 1) ∈ ℚ`. -/
@[collatz_pos_dens "def_mx_boot_w"]
def bootW : ℚ := 15 / (bootChainRatio ^ 2 - 1)

/-- The defining formula of the quadratic coefficient of the bootstrap profile. -/
theorem bootW_eq : bootW = 15 / (bootChainRatio ^ 2 - 1) := rfl

/-- The value of the quadratic coefficient of the bootstrap profile. -/
theorem bootW_val : bootW = 15000000 / 164241 := by
  rw [bootW_eq, bootChainRatio_sq_sub_one]; norm_num

/-- The value of the quadratic coefficient of the bootstrap profile, cast into a division ring of
characteristic zero. -/
@[simp]
theorem bootW_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (bootW : K) = 15000000 / 164241 := by
  rw [bootW_val]; norm_num

/-- The quadratic coefficient of the bootstrap profile is positive. -/
theorem bootW_pos : 0 < bootW := by
  rw [bootW_val]; norm_num

end CollatzPosDens
