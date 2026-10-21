/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.Case3.C3GapRatio

/-!
# The reciprocal slope is below `127/40`

With `α = log 2 / log 9`, the reciprocal slope satisfies `1/α < 127/40`.

Indeed `1/α = log 9 / log 2 < 158497/50000`, and
`158497 · 40 = 6339880 < 6350000 = 127 · 50000`.

## Main results

* `CollatzPosDens.packConst_lt_Qpack`: `1/α < 127/40`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The reciprocal slope satisfies `1/α < 127/40`. -/
@[collatz_pos_dens "lem_c3_pack_const"]
theorem packConst_lt_Qpack : 1 / alpha < 127 / 40 := by
  rw [alpha_def, one_div_div]
  exact log_nine_div_log_two_lt.trans (by norm_num)

end CollatzPosDens
