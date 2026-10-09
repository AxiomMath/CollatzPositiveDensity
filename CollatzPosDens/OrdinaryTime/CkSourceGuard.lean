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
# The source guard for the ordinary-time count

The rational inequality
$$\frac{287682}{10^6}-\frac{347}{500}\Bigl(\frac{3}{1000}+\frac{26}{10\cdot 2^{22}}\Bigr)
  >\frac{28559}{100000}.$$
Here `287682/10^6` is a lower bound for `log (4/3)` and `347/500` an upper bound for `log 2`.
By exact computation the left side equals `598945709/2097152000`, which exceeds the right side
by `501733/52428800000`.

## Main results

* `CollatzPosDens.ck_source_guard`: the inequality, stated in `ℝ`.

## Implementation notes

The statement is in `ℝ`; the proof is an exact rational computation by `norm_num`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The source guard: `28559/100000 < 287682/10^6 - (347/500)(3/1000 + 26/(10·2^22))`. -/
@[collatz_pos_dens "lem_ck_source_guard"]
theorem ck_source_guard :
    (28559 / 100000 : ℝ) <
      287682 / 10 ^ 6 - 347 / 500 * (3 / 1000 + 26 / (10 * 2 ^ 22)) := by
  norm_num

end CollatzPosDens
