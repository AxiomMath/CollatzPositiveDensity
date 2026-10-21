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
# The packing mass coefficient `q_pack`

The packing mass coefficient is the rational constant
$$\mathsf q_{\mathrm{pack}} := \frac{1527079}{5000000} = 0.3054158.$$

## Main definitions

* `CollatzPosDens.qPack`: the packing mass coefficient `q_pack = 1527079/5000000 : ℚ`.

## Main results

* `CollatzPosDens.qPack_eq`: the value `q_pack = 1527079/5000000`.
* `CollatzPosDens.qPack_cast`: the value of `(q_pack : K)` in any division ring of
  characteristic zero, e.g. `ℝ`.
* `CollatzPosDens.qPack_pos`: `0 < q_pack`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The packing mass coefficient `q_pack := 1527079/5000000 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_qpack"]
def qPack : ℚ := 1527079 / 5000000

/-- The value of the packing mass coefficient. -/
@[simp]
theorem qPack_eq : qPack = 1527079 / 5000000 := rfl

/-- The value of the packing mass coefficient cast into a division ring of characteristic
zero. -/
theorem qPack_cast {K : Type*} [DivisionRing K] [CharZero K] :
    (qPack : K) = 1527079 / 5000000 := by
  simp

/-- The packing mass coefficient is positive. -/
theorem qPack_pos : 0 < qPack := by norm_num

end CollatzPosDens
