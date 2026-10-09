/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import CollatzPosDens.Attr

/-!
# A sharp lower bound for `log 2`

This file proves $\log 2 > 693147180 / 10^9$, a bound obtainable from the series
$\log 2 = 2\sum_{k\ge0} \frac{1}{(2k+1)3^{2k+1}}$ truncated at $k = 9$.

## Main results

* `CollatzPosDens.log_two_gt_sharp`: `693147180 / 10 ^ 9 < Real.log 2`.
* `CollatzPosDens.log_two_gt_693147180`: the same bound, restated.

## Implementation notes

Mathlib already provides the stronger bound `Real.log_two_gt_d9`
($0.6931471803 < \log 2$), proved by a series estimate of the same kind; we deduce the
stated bound from it by an exact rational comparison.
-/

@[expose] public section

namespace CollatzPosDens

/-- The sharp lower bound $\log 2 > 693147180 / 10^9$. -/
@[collatz_pos_dens "lem_log2_sharp"]
theorem log_two_gt_sharp : (693147180 : ℝ) / 10 ^ 9 < Real.log 2 :=
  lt_trans (by norm_num) Real.log_two_gt_d9

/-- The lower bound $\log 2 > 693147180 / 10^9$; a restatement of `log_two_gt_sharp`. -/
@[collatz_pos_dens "lem_s02_log2_lower"]
theorem log_two_gt_693147180 : (693147180 : ℝ) / 10 ^ 9 < Real.log 2 :=
  log_two_gt_sharp

end CollatzPosDens
