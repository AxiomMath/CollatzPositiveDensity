/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02DF
public import CollatzPosDens.Transfer.S02DstarEq

/-!
# The leading digits of the Fourier decay constant `D_F`

Since `D_*(ι) = D_sc(ι)` and `D_F(ι) = 2 D_*(ι) + 6`, the Fourier decay constant is the explicit
integer `2 D_sc(ι) + 6`:
$$D_F(\mathrm o) = 2520129694230262480456458703308924761123561210,\qquad
  D_F(\mathrm b) = 535450934240100.$$
Then `15 D_F(o) = 37801945413453937206846880549633871416853418150`, and exact integer division
gives `⌊15 D_F(o) / 2^75⌋ = 1000609163609502169286000`, while
`15 D_F(b) = 8031764013601500 = 1078005117737754427392000 · 2^{-27}` exactly, i.e.
$$1000609163609502169286000 \cdot 2^{75} \le 15 D_F(\mathrm o)
  < 1000609163609502169286001 \cdot 2^{75},$$
$$1078005117737754427392000 \cdot 2^{-27} \le 15 D_F(\mathrm b)
  < 1078005117737754427392001 \cdot 2^{-27}.$$

## Main results

* `CollatzPosDens.DF_o`, `CollatzPosDens.DF_b`: the exact values of `D_F(ι)`.
* `CollatzPosDens.DF_head_o`, `CollatzPosDens.DF_head_b`: the two-sided bounds on `15 D_F(ι)`
  above.

## Implementation notes

The bounds for `ι = o` and `ι = b`, which differ in the mantissa and the binary exponent, are
the two theorems `DF_head_o` and `DF_head_b`. The negative power `2^{-27}` is written as the
division `/ 2 ^ 27` in `ℚ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value of `D_F(o) = 2 D_sc(o) + 6`. -/
theorem DF_o : DF .o = 2520129694230262480456458703308924761123561210 := by
  rw [DF_def, Dstar_eq_Dsc, Dsc_o]
  norm_num

/-- The exact value of `D_F(b) = 2 D_sc(b) + 6 = 2 · 267725467120047 + 6`. -/
theorem DF_b : DF .b = 535450934240100 := by
  rw [DF_def, Dstar_eq_Dsc, Dsc_b]
  norm_num

/-- **Leading digits of `D_F(o)`.**
`1000609163609502169286000 · 2^75 ≤ 15 D_F(o) < 1000609163609502169286001 · 2^75`. -/
@[collatz_pos_dens "lem_s02_DF_head"]
theorem DF_head_o :
    (1000609163609502169286000 : ℚ) * 2 ^ 75 ≤ 15 * DF .o ∧
      15 * DF .o < (1000609163609502169286001 : ℚ) * 2 ^ 75 := by
  rw [DF_o]
  norm_num

/-- **Leading digits of `D_F(b)`.**
`1078005117737754427392000 · 2^{-27} ≤ 15 D_F(b) < 1078005117737754427392001 · 2^{-27}`; the
left end is attained, `15 D_F(b) = 8031764013601500`. -/
@[collatz_pos_dens "lem_s02_DF_head"]
theorem DF_head_b :
    (1078005117737754427392000 : ℚ) / 2 ^ 27 ≤ 15 * DF .b ∧
      15 * DF .b < (1078005117737754427392001 : ℚ) / 2 ^ 27 := by
  rw [DF_b]
  norm_num

end CollatzPosDens
