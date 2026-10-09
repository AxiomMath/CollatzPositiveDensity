/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.W
public import CollatzPosDens.Transfer.Z
public import Mathlib.Algebra.Order.Field.Basic

/-!
# The near-top margin

For the constants `w_* = wStar = 63/2500` and `z_* = zStar = 21/500` one has
`w_*/8 = 126/40000 < 189/40000 = 3/16 · 3/5 · z_*`, so
`1 + w_*/8 - 3/16 · 3/5 · z_* ≤ 1`.

## Main results

* `CollatzPosDens.moCase2_margin`: `1 + w_*/8 - 3/16 · 3/5 · z_* ≤ 1` in `ℚ`.
* `CollatzPosDens.moCase2_margin_cast`: the same inequality for the casts of `w_*` and `z_*`
  into any linearly ordered field, e.g. `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- `1 + w_*/8 - 3/16 · 3/5 · z_* ≤ 1` in `ℚ`. -/
@[collatz_pos_dens "lem_mo_case2_margin"]
theorem moCase2_margin : 1 + wStar / 8 - 3 / 16 * (3 / 5 * zStar) ≤ 1 := by
  rw [wStar_eq, zStar_eq]; norm_num

/-- `1 + w_*/8 - 3/16 · 3/5 · z_* ≤ 1` for the casts of `w_*` and `z_*` into a linearly ordered
field. -/
theorem moCase2_margin_cast {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    1 + (wStar : K) / 8 - 3 / 16 * (3 / 5 * (zStar : K)) ≤ 1 := by
  rw [wStar_cast, zStar_cast]; norm_num

end CollatzPosDens
