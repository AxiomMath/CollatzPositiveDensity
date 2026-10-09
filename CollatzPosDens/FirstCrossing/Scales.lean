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

The scales form the sequence `β : ℕ → ℕ` given by `β(0) = 9` and
`β(j + 1) = β(j) + e_{β(j)}`, where `e_b` is `CollatzPosDens.eb b`. We write `b_j = β(j)`.
Since `e_b ≥ 1` for every `b`, the scales are strictly increasing.

## Main definitions

* `CollatzPosDens.scale`: the scales `b_j = β(j)`.

## Main results

* `CollatzPosDens.scale_zero`, `CollatzPosDens.scale_succ`: the defining recursion.
* `CollatzPosDens.scale_strictMono`: the scales are strictly increasing.
* `CollatzPosDens.nine_le_scale`: every scale is at least `b_0 = 9`.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Scales** `b_j = β(j)`: `β(0) = 9` and `β(j + 1) = β(j) + e_{β(j)}`. -/
@[collatz_pos_dens "def_scales"]
def scale : ℕ → ℕ
  | 0 => 9
  | j + 1 => scale j + eb (scale j)

/-- The first scale is `b_0 = 9`. -/
@[simp]
theorem scale_zero : scale 0 = 9 := rfl

/-- The recursion `b_{j+1} = b_j + e_{b_j}`. -/
theorem scale_succ (j : ℕ) : scale (j + 1) = scale j + eb (scale j) := rfl

/-- Each scale is strictly smaller than the next. -/
theorem scale_lt_succ (j : ℕ) : scale j < scale (j + 1) := by
  rw [scale_succ]
  have := one_le_eb (scale j)
  omega

/-- The scales are strictly increasing. -/
theorem scale_strictMono : StrictMono scale :=
  strictMono_nat_of_lt_succ scale_lt_succ

/-- The scales are nondecreasing. -/
theorem scale_monotone : Monotone scale :=
  scale_strictMono.monotone

/-- Every scale is at least `b_0 = 9`. -/
theorem nine_le_scale (j : ℕ) : 9 ≤ scale j :=
  scale_monotone (Nat.zero_le j)

/-- Every scale is positive. -/
theorem scale_pos (j : ℕ) : 0 < scale j :=
  lt_of_lt_of_le (by norm_num) (nine_le_scale j)

end CollatzPosDens
