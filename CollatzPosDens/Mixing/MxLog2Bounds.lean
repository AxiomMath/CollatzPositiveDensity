/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import CollatzPosDens.Attr

/-! # Numerical bounds on `log 2`

This file records the elementary numerical fact `0.693 < log 2 < 0.694`.

## Main results

* `CollatzPosDens.log_two_bounds`: `0.693 < Real.log 2 ∧ Real.log 2 < 0.694`.

## Implementation notes

The bounds follow from Mathlib's nine-digit bounds `Real.log_two_gt_d9` and
`Real.log_two_lt_d9`, which are obtained from partial sums of `log 2 = ∑ 1 / (k 2 ^ k)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- Numerical bounds on the natural logarithm of two: `0.693 < log 2 < 0.694`. -/
@[collatz_pos_dens "lem_mx_log2_bounds"]
theorem log_two_bounds : (0.693 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.694 :=
  ⟨lt_trans (by norm_num) Real.log_two_gt_d9, lt_trans Real.log_two_lt_d9 (by norm_num)⟩

end CollatzPosDens
