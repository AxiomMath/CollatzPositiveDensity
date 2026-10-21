/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Archimedes' upper bound `π < 22 / 7`

The classical rational upper bound `π < 22 / 7` for the circle constant.

## Main results

* `CollatzPosDens.pi_lt_twentyTwo_div_seven`: `π < 22 / 7`.

## Implementation notes

The classical proof integrates the identity
`x⁴(1 - x)⁴ / (1 + x²) = x⁶ - 4x⁵ + 5x⁴ - 4x² + 4 - 4 / (1 + x²)` over `[0, 1]`, obtaining
`∫₀¹ x⁴(1 - x)⁴ / (1 + x²) dx = 22 / 7 - π`, and concludes from the positivity of the integral.
Here we instead derive the bound from the sharper decimal estimate `π < 3.1416`
(`Real.pi_lt_d4`), since `3.1416 < 22 / 7`.
-/

@[expose] public section

namespace CollatzPosDens

/-- Archimedes' bound: `π < 22 / 7`. -/
@[collatz_pos_dens "lem_ch_pi_upper"]
theorem pi_lt_twentyTwo_div_seven : Real.pi < 22 / 7 :=
  Real.pi_lt_d4.trans (by norm_num)

end CollatzPosDens
