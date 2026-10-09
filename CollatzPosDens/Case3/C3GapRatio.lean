/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The bound `log 9 / log 2 < 158497 / 50000`

The ratio `log 9 / log 2` satisfies `log 9 / log 2 < 158497 / 50000`. The integer
`9 ^ 50000` has binary length `158497`, so `9 ^ 50000 < 2 ^ 158497`; taking logarithms gives
`50000 log 9 < 158497 log 2`, which is the claim after dividing by `50000 log 2 > 0`.

## Main results

* `CollatzPosDens.log_nine_div_log_two_lt`: `log 9 / log 2 < 158497 / 50000`.

## Implementation notes

The integer inequality `9 ^ 50000 < 2 ^ 158497` is checked by the kernel on natural-number
literals, whose arithmetic is GMP-accelerated.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §10.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The inequality `9 ^ 50000 < 2 ^ 158497`, i.e. `9 ^ 50000` has at most `158497` binary
digits. -/
private theorem nine_pow_lt_two_pow : 9 ^ 50000 < 2 ^ 158497 := by
  decide +kernel

/-- The ratio of logarithms satisfies `log 9 / log 2 < 158497 / 50000`. -/
@[collatz_pos_dens "lem_c3_gap_ratio"]
theorem log_nine_div_log_two_lt : Real.log 9 / Real.log 2 < 158497 / 50000 := by
  rw [div_lt_div_iff₀ (Real.log_pos (by norm_num)) (by norm_num)]
  have hR : ((9 : ℕ) : ℝ) ^ 50000 < ((2 : ℕ) : ℝ) ^ 158497 := by
    rw [← Nat.cast_pow, ← Nat.cast_pow]
    exact Nat.cast_lt.mpr nine_pow_lt_two_pow
  have h := Real.log_lt_log (by positivity) hR
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

end CollatzPosDens
