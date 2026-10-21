/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Scales

/-!
# The seed shift `σ_sd`

The seed shift is the natural number `σ_sd := 4 b_0`, four times the initial scale
`b_0 = CollatzPosDens.scale 0`. Since `b_0 = 16544`, its value is `σ_sd = 4 · 16544 = 66176`.

## Main definitions

* `CollatzPosDens.seedShift`: the seed shift `σ_sd := 4 b_0`.

## Main results

* `CollatzPosDens.seedShift_def`: `σ_sd = 4 b_0`.
* `CollatzPosDens.seedShift_eq`: `σ_sd = 66176`.

## Implementation notes

`seedShift` is irreducible, so that it is used through `seedShift_def` or `seedShift_eq` and
never unfolded by definitional reduction.
-/

@[expose] public section

namespace CollatzPosDens

/-- The seed shift `σ_sd := 4 b_0 ∈ ℕ`, four times the initial scale `b_0 = scale 0`. -/
@[collatz_pos_dens "def_seed_shift", irreducible]
def seedShift : ℕ := 4 * scale 0

/-- The defining formula of the seed shift: `σ_sd = 4 b_0`. -/
theorem seedShift_def : seedShift = 4 * scale 0 := by
  unfold seedShift
  rfl

/-- The seed shift has the value `σ_sd = 66176`. -/
@[collatz_pos_dens "lem_seed_shift_value"]
theorem seedShift_eq : seedShift = 66176 := by
  rw [seedShift_def, scale_zero]

end CollatzPosDens
