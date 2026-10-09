/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.EpsStar
public import Mathlib.Algebra.Order.Field.Basic

/-!
# The colour scale lies in the black-set range

The geometric statements about the black set are stated for a colouring parameter `ε` with
`0 < ε < 1/27`. The colour scale `ε_* = 8/217` satisfies these bounds: it is positive, and
`8 · 27 = 216 < 217` gives `8/217 < 1/27`. Hence each of those statements applies with
`ε = ε_*`.

## Main results

* `CollatzPosDens.epsStar_mem_bkRange`: `0 < ε_* ∧ ε_* < 1/27`, for `(ε_* : K)` in any linearly
  ordered field `K`, e.g. `ℚ` or `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The colour scale lies in the range `0 < ε_* < 1/27` of the black-set geometry, in any
linearly ordered field. -/
@[collatz_pos_dens "lem_bk_eps_star_range"]
theorem epsStar_mem_bkRange {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    0 < (epsStar : K) ∧ (epsStar : K) < 1 / 27 := by
  rw [epsStar_cast]
  constructor <;> norm_num

end CollatzPosDens
