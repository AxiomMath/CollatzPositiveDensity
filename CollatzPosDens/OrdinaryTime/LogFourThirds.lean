/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import CollatzPosDens.Attr

/-!
# A lower bound on `log (4 / 3)`

This file proves $\log(4/3) > 287682/10^6$. Since $4/3 = (1 + \frac17)/(1 - \frac17)$, the series
$$\log\frac{1+t}{1-t} = 2 \sum_{k \ge 0} \frac{t^{2k+1}}{2k+1}$$
at $t = \frac17$ has positive terms, so $\log(4/3)$ is at least its partial sum over
$0 \le k \le 3$, which equals $\frac{24876448}{86472015}$; this rational exceeds
$\frac{287682}{10^6}$ by $\frac{578077}{8647201500000}$.

## Main results

* `CollatzPosDens.log_four_thirds_gt`: `287682 / 10 ^ 6 < log (4 / 3)`.

## Implementation notes

The series is taken in Mathlib's form `hasSum_log_one_add_inv` at `a = 3`, i.e.
$\log(1 + 3^{-1}) = 2 \sum_k \frac{1}{2k+1} (1/7)^{2k+1}$, which is the same series.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The elementary lower bound `log (4 / 3) > 287682 / 10 ^ 6`. -/
@[collatz_pos_dens "lem_s07_log_four_thirds"]
theorem log_four_thirds_gt : (287682 / 10 ^ 6 : ℝ) < log (4 / 3) := by
  have h := hasSum_log_one_add_inv (a := (3 : ℝ)) (by norm_num)
  have hle := sum_le_hasSum (Finset.range 4) (fun k _ => by positivity) h
  norm_num [Finset.sum_range_succ] at hle
  linarith

end CollatzPosDens
