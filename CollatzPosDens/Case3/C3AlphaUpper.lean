/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope

/-!
# The upper bound `α < 8 / 25`

The slope `α = log 2 / log 9` satisfies `α < 8 / 25`. Indeed
`2 ^ 25 = 33554432 < 43046721 = 9 ^ 8`, so `25 log 2 < 8 log 9`, which is the claim
after dividing by `25 log 9 > 0`.

## Main results

* `CollatzPosDens.alpha_lt_eight_div_twentyfive`: `α < 8 / 25`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The slope `alpha = log 2 / log 9` satisfies `alpha < 8 / 25`. -/
@[collatz_pos_dens "lem_c3_alpha_upper"]
theorem alpha_lt_eight_div_twentyfive : alpha < 8 / 25 := by
  rw [alpha_def, div_lt_iff₀ (Real.log_pos (by norm_num))]
  have h : Real.log ((2 : ℝ) ^ 25) < Real.log ((9 : ℝ) ^ 8) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

end CollatzPosDens
