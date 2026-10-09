/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

/-!
# A numerical length guard

This file proves the rational inequality
$$\frac94\cdot\frac{347}{500}\cdot\frac1{2^{22}}<\frac1{10^6},$$
where `347/500` is an upper bound for `log 2`. By exact computation the left side equals
`3123/8388608000`, and the difference `1/10^6 - 3123/8388608000 = 658201/1048576000000` is
positive.

## Main results

* `CollatzPosDens.ck_length_guard`: the inequality, stated in `ℝ`.

## Implementation notes

The statement is in `ℝ`, so that it compares directly with real logarithms; the proof is an
exact rational computation by `norm_num`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The inequality `(9/4) · (347/500) · (1/2^22) < 1/10^6`. -/
@[collatz_pos_dens "lem_ck_length_guard"]
theorem ck_length_guard : (9 / 4 : ℝ) * (347 / 500) * (1 / 2 ^ 22) < 1 / 10 ^ 6 := by
  norm_num

end CollatzPosDens
