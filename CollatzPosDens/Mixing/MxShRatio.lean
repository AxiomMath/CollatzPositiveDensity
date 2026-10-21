/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import CollatzPosDens.Attr

/-! # A numerical inequality between `√2` and `√3`

This file proves the numerical inequality `(1 + (√3 - 1) · 51/100) / √2 < 39/40` between real
numbers.

## Main results

* `CollatzPosDens.mx_sh_ratio_lt`: `(1 + (√3 - 1) * (51/100)) / √2 < 39/40`.

## Implementation notes

The proof uses the rational bounds `√3 < 1733/1000` (as `1733² > 3 · 10⁶`) and `707/500 < √2`
(as `707² < 2 · 500²`), after which the claim is the rational inequality `137383/141400 < 39/40`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The inequality `(1 + (√3 - 1) · 51/100) / √2 < 39/40` between real numbers. -/
@[collatz_pos_dens "lem_mx_sh_ratio"]
theorem mx_sh_ratio_lt :
    (1 + (Real.sqrt 3 - 1) * (51 / 100)) / Real.sqrt 2 < 39 / 40 := by
  have h3 : Real.sqrt 3 < 1733 / 1000 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h2 : (707 / 500 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2pos : (0 : ℝ) < Real.sqrt 2 := by positivity
  rw [div_lt_iff₀ h2pos]
  nlinarith

end CollatzPosDens
