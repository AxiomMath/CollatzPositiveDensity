/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A rational upper bound for `e`

Euler's number satisfies `e < 68/25 = 2.72`. Mathlib's bound `Real.exp_one_lt_d9` gives
`e < 2.7182818286 = 13591409143/5000000000`, and `13591409143 < 13600000000` gives
`13591409143/5000000000 < 68/25`.

## Main results

* `CollatzPosDens.exp_one_lt_68_div_25`: `Real.exp 1 < 68/25`.
-/

@[expose] public section

namespace CollatzPosDens

/-- Euler's number is less than `68/25`. -/
@[collatz_pos_dens "lem_s02_e_upper"]
theorem exp_one_lt_68_div_25 : Real.exp 1 < 68 / 25 :=
  Real.exp_one_lt_d9.trans (by norm_num)

end CollatzPosDens
