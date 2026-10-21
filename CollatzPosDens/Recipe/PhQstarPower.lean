/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.PhQstarValue
public import CollatzPosDens.Recipe.TowerExp
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# The finite conductor comparison

The conductor `CollatzPosDens.conductor` and the tower exponent `CollatzPosDens.towerExp` satisfy
`4 + (317/200) * conductor < 2 ^ towerExp`. Since `conductor = d` is the explicit 49-digit integer
of `CollatzPosDens.conductor_value` and `towerExp = 163`, this is the exact integer comparison
`800 + 317 d < 200 · 2^163`.

## Main results

* `CollatzPosDens.four_add_mul_conductor_lt_two_pow_towerExp`:
  `4 + (317/200) * conductor < 2 ^ towerExp` in `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The finite conductor comparison `4 + (317/200) * conductor < 2 ^ towerExp` in `ℝ`. -/
@[collatz_pos_dens "lem_ph_qstar_power"]
theorem four_add_mul_conductor_lt_two_pow_towerExp :
    (4 : ℝ) + 317 / 200 * conductor < 2 ^ towerExp := by
  rw [conductor_value, towerExp_def]
  norm_num

end CollatzPosDens
