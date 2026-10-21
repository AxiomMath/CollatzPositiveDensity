/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Eb
public import Mathlib.Order.Monotone.Basic

/-!
# The scales `b_j`

The scales of the first-crossing argument form the sequence `β : ℕ → ℕ` given by
`β(0) = 16544` and `β(j + 1) = β(j) + e_{β(j)}`, where `e_b = ⌈b/100⌉` is the scale increment.
We write `b_j = β(j)`. Every scale is at least `b_0 = 16544`, so each increment is positive and
the scales are strictly increasing.

## Main definitions

* `CollatzPosDens.scale`: the scales `b_j = β(j)`.

## Main results

* `CollatzPosDens.scale_zero`, `CollatzPosDens.scale_succ`: the defining recursion.
* `CollatzPosDens.sixteen544_le_scale`: every scale is at least `b_0 = 16544`.
* `CollatzPosDens.scale_strictMono`: the scales are strictly increasing.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Scales** `b_j = β(j)`: `β(0) = 16544` and `β(j + 1) = β(j) + e_{β(j)}`. -/
@[collatz_pos_dens "def_scales"]
def scale : ℕ → ℕ
  | 0 => 16544
  | j + 1 => scale j + eb (scale j)

/-- The first scale is `b_0 = 16544`. -/
@[simp]
theorem scale_zero : scale 0 = 16544 := rfl

/-- The recursion `b_{j+1} = b_j + e_{b_j}`. -/
theorem scale_succ (j : ℕ) : scale (j + 1) = scale j + eb (scale j) := rfl

/-- Every scale is at least `b_0 = 16544`. -/
theorem sixteen544_le_scale (j : ℕ) : 16544 ≤ scale j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact ih.trans (Nat.le_add_right _ _)

/-- Every scale is positive. -/
theorem scale_pos (j : ℕ) : 0 < scale j :=
  lt_of_lt_of_le (by norm_num) (sixteen544_le_scale j)

/-- Each scale is strictly smaller than the next. -/
theorem scale_lt_succ (j : ℕ) : scale j < scale (j + 1) :=
  Nat.lt_add_of_pos_right (one_le_eb_of_pos (scale_pos j))

/-- The scales are strictly increasing. -/
theorem scale_strictMono : StrictMono scale :=
  strictMono_nat_of_lt_succ scale_lt_succ

/-- The scales are nondecreasing. -/
theorem scale_monotone : Monotone scale :=
  scale_strictMono.monotone

end CollatzPosDens
