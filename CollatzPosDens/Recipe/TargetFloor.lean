/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales

/-!
# The target floor `t_min`

The target floor is the natural number `t_min := 16^{b_0}`, where `b_0 = CollatzPosDens.scale 0`
is the initial scale. Since `b_0 = 16544`, `t_min = 16^{16544}`.

## Main definitions

* `CollatzPosDens.targetFloor`: the target floor `t_min := 16^{b_0}`.

## Main results

* `CollatzPosDens.targetFloor_def`: `t_min = 16^{b_0}`.
* `CollatzPosDens.targetFloor_eq`: `t_min = 16^{16544}`.
* `CollatzPosDens.targetFloor_pos`: `0 < t_min`.

## Implementation notes

`targetFloor` is irreducible, so that the `66177`-bit number `16^{16544}` is never produced by
definitional unfolding. Use `targetFloor_def` or `targetFloor_eq`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The target floor `t_min := 16^{b_0} ∈ ℕ`, where `b_0 = scale 0` is the initial scale. -/
@[collatz_pos_dens "def_tmin", irreducible]
def targetFloor : ℕ := 16 ^ scale 0

/-- The defining formula of the target floor: `t_min = 16^{b_0}`. -/
theorem targetFloor_def : targetFloor = 16 ^ scale 0 := by
  unfold targetFloor
  rfl

/-- The value of the target floor: `t_min = 16^{16544}`. -/
theorem targetFloor_eq : targetFloor = 16 ^ 16544 := by
  rw [targetFloor_def, scale_zero]

/-- The target floor is positive. -/
theorem targetFloor_pos : 0 < targetFloor := by
  rw [targetFloor_def]
  exact Nat.pow_pos (by decide)

end CollatzPosDens
