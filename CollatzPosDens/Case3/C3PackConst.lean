/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkSlope
public import CollatzPosDens.Transfer.Qpack
public import CollatzPosDens.Case3.C3AlphaUpper
public import CollatzPosDens.Case3.C3GapRatio

/-!
# The packing constant is below `Qpack`

With `CollatzPosDens.alpha = log 2 / log 9`, the packing constant satisfies
`(1 + 2 * alpha) * (17/10) * √2 + (1 / alpha + 2) * (33/32) * (25/36) < Qpack`.

Indeed `1 + 2 * alpha < 41/25` since `alpha < 8/25`; `√2 < 99/70` since
`99² = 9801 > 9800 = 2 · 70²`; and `1 / alpha = log 9 / log 2 < 158497/50000 < 127/40`. All
factors are positive, so the left side is less than
`41/25 · 17/10 · 99/70 + (127/40 + 2) · 33/32 · 25/36 = 69003/17500 + 3795/1024`, which is
`34267893/4480000 = Qpack`.

## Main results

* `CollatzPosDens.packConst_lt_Qpack`: the packing constant is less than `Qpack`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The packing constant `(1 + 2 * alpha) * (17/10) * √2 + (1 / alpha + 2) * (33/32) * (25/36)`
is less than `Qpack`. -/
@[collatz_pos_dens "lem_c3_pack_const"]
theorem packConst_lt_Qpack :
    (1 + 2 * alpha) * (17 / 10) * Real.sqrt 2 + (1 / alpha + 2) * (33 / 32) * (25 / 36) <
      (Qpack : ℝ) := by
  have hs : Real.sqrt 2 < 99 / 70 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hinv : 1 / alpha < 127 / 40 := by
    rw [alpha_def, one_div_div]
    exact log_nine_div_log_two_lt.trans (by norm_num)
  have := mul_le_mul (by linarith [alpha_lt_eight_div_twentyfive] :
    1 + 2 * alpha ≤ 41 / 25) hs.le (Real.sqrt_nonneg 2) (by norm_num)
  rw [Qpack_cast]
  linarith

end CollatzPosDens
