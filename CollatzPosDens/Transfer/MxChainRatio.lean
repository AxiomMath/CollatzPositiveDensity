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
# The ratio of the bootstrap chaining

The bootstrap chaining compares the propagation mixing profile at two scales whose ratio is at
least the rational constant `c_bt := 1079/1000`. This file defines `c_bt` and records the
elementary facts `1 < c_bt` and `c_bt ^ 2 - 1 = 164241/10^6 > 0`.

## Main definitions

* `CollatzPosDens.bootChainRatio`: the ratio `c_bt := 1079/1000 : ℚ`.

## Main results

* `CollatzPosDens.bootChainRatio_cast`: the value of `c_bt` cast into a division ring of
  characteristic zero.
* `CollatzPosDens.bootChainRatio_pos`, `CollatzPosDens.one_lt_bootChainRatio`: `0 < 1 < c_bt`.
* `CollatzPosDens.bootChainRatio_sq_sub_one`, `CollatzPosDens.bootChainRatio_sq_sub_one_pos`:
  `c_bt ^ 2 - 1 = 164241/1000000 > 0`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The ratio of the bootstrap chaining, `c_bt := 1079/1000 ∈ ℚ`. -/
@[collatz_pos_dens "def_mx_chain_ratio"]
def bootChainRatio : ℚ := 1079 / 1000

/-- The defining value of the ratio of the bootstrap chaining. -/
theorem bootChainRatio_eq : bootChainRatio = 1079 / 1000 := rfl

/-- The value of the ratio of the bootstrap chaining, cast into a division ring of characteristic
zero. -/
@[simp]
theorem bootChainRatio_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (bootChainRatio : K) = 1079 / 1000 := by
  rw [bootChainRatio_eq]; norm_num

/-- The ratio of the bootstrap chaining is positive. -/
theorem bootChainRatio_pos : 0 < bootChainRatio := by
  rw [bootChainRatio_eq]; norm_num

/-- The ratio of the bootstrap chaining exceeds `1`. -/
theorem one_lt_bootChainRatio : 1 < bootChainRatio := by
  rw [bootChainRatio_eq]; norm_num

/-- The square of the ratio of the bootstrap chaining, minus one. -/
theorem bootChainRatio_sq_sub_one : bootChainRatio ^ 2 - 1 = 164241 / 1000000 := by
  rw [bootChainRatio_eq]; norm_num

/-- The square of the ratio of the bootstrap chaining minus one is positive. -/
theorem bootChainRatio_sq_sub_one_pos : 0 < bootChainRatio ^ 2 - 1 := by
  rw [bootChainRatio_sq_sub_one]; norm_num

end CollatzPosDens
