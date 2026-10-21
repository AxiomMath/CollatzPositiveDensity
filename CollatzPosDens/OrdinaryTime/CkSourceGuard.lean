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
It is used after bounding `log (4/3)` below by `287682/10^6` and `log 2` above by `347/500`.
By exact computation the left side equals `598945709/2097152000`, which exceeds the right side
by `501733/52428800000`.

## Main results

* `CollatzPosDens.ckSourceGuard`: the inequality, stated in `ℝ`.

## Implementation notes

The statement is in `ℝ`, where it is applied (against real logarithms); the proof is an exact
rational computation by `norm_num`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The source guard: `287682/10^6 - (347/500)(3/1000 + 26/(10·2^22)) > 28559/100000`. -/
@[collatz_pos_dens "lem_ck_source_guard"]
theorem ckSourceGuard :
    (28559 / 100000 : ℝ) <
      287682 / 10 ^ 6 - 347 / 500 * (3 / 1000 + 26 / (10 * 2 ^ 22)) := by
  norm_num

end CollatzPosDens
