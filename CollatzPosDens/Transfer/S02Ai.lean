/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02AdaptiveAnchor
public import CollatzPosDens.Transfer.S02S
public import CollatzPosDens.Transfer.S02Schedule
public import CollatzPosDens.Transfer.S02Wtot

/-!
# The adaptive denominators `A_i(ι)` of the trace schedule

For a Fourier index `ι ∈ 𝔍 = {o, b}` and `0 ≤ i < r_*(ι)`, the `i`-th adaptive denominator of
the trace schedule is the rational number
$$\mathsf A_i(\iota) := b_{\mathrm{an}}\,\mathsf S_i(\iota) - \mathsf W(\iota, p_i(\iota)) - 1,$$
where `b_an` is the adaptive anchor constant, `S_i(ι)` the `i`-th interval size, `p_i(ι)` the
`i`-th schedule position and `W(ι, ·)` the total allowance. Since `W(o, v) = 1697 + (6579/500) v`
and `W(b, v) = 1356 + (1653/125) v`, explicitly
`A_i(o) = b_an S_i(o) - 1698 - (6579/500) p_i(o)` and
`A_i(b) = b_an S_i(b) - 1357 - (1653/125) p_i(b)`.

## Main definitions

* `CollatzPosDens.aStar`: the denominator `A_i(ι) = b_an S_i(ι) - W(ι, p_i(ι)) - 1 : ℚ`.

## Main results

* `CollatzPosDens.aStar_def`: the defining formula.
* `CollatzPosDens.aStar_apply_o`, `CollatzPosDens.aStar_apply_b`: the explicit values.

## Implementation notes

The denominators are only meaningful for `0 ≤ i < r_*(ι)` (`CollatzPosDens.rStar`). The
definition is total on `ℕ`, since `S_i`, `p_i` and `W` are; its values at `i ≥ r_*(ι)` are never
used.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The adaptive denominators of the trace schedule:
`A_i(ι) := b_an S_i(ι) - W(ι, p_i(ι)) - 1 ∈ ℚ`. -/
@[collatz_pos_dens "def_s02_Ai"]
def aStar (ι : FIndex) (i : ℕ) : ℚ :=
  bAn * sStar ι i - totalAllowance ι (schedule ι i) - 1

/-- The defining formula `A_i(ι) = b_an S_i(ι) - W(ι, p_i(ι)) - 1`. -/
theorem aStar_def (ι : FIndex) (i : ℕ) :
    aStar ι i = bAn * sStar ι i - totalAllowance ι (schedule ι i) - 1 := rfl

/-- The explicit value `A_i(o) = b_an S_i(o) - 1698 - (6579/500) p_i(o)`. -/
theorem aStar_apply_o (i : ℕ) :
    aStar .o i = bAn * sStar .o i - 1698 - 6579 / 500 * schedule .o i := by
  rw [aStar_def, totalAllowance_eq_o]
  ring

/-- The explicit value `A_i(b) = b_an S_i(b) - 1357 - (1653/125) p_i(b)`. -/
theorem aStar_apply_b (i : ℕ) :
    aStar .b i = bAn * sStar .b i - 1357 - 1653 / 125 * schedule .b i := by
  rw [aStar_def, totalAllowance_eq_b]
  ring

end CollatzPosDens
