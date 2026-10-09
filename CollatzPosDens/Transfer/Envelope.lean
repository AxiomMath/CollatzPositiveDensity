/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.H
public import CollatzPosDens.Transfer.AK

/-!
# The envelope bound `1025 a_*^{580} < 2^{H_*}`

The plateau height `H_* = 17451` is the binary length of the integer `1025 a_*^{580}`, where
`a_* = 1127203229` is the growth factor. Hence `2^{H_* - 1} ≤ 1025 a_*^{580} < 2^{H_*}`.

## Main results

* `CollatzPosDens.envelope_lt_two_pow_Hstar`: `1025 a_*^{580} < 2^{H_*}`.
* `CollatzPosDens.two_pow_Hstar_sub_one_le_envelope`: `2^{H_* - 1} ≤ 1025 a_*^{580}`, so the
  bound is sharp to within one bit.

## Implementation notes

Both inequalities are statements about natural-number literals, decided by the kernel's
arithmetic on literals after substituting the values `a_* = 1127203229` and `H_* = 17451`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The envelope bound `1025 a_*^{580} < 2^{H_*}`. -/
@[collatz_pos_dens "lem_s02_envelope"]
theorem envelope_lt_two_pow_Hstar : 1025 * aK ^ 580 < 2 ^ Hstar := by
  rw [aK_eq, Hstar_def]
  decide +kernel

/-- The envelope bound is sharp to within one bit: `2^{H_* - 1} ≤ 1025 a_*^{580}`. -/
theorem two_pow_Hstar_sub_one_le_envelope : 2 ^ (Hstar - 1) ≤ 1025 * aK ^ 580 := by
  rw [aK_eq, Hstar_def]
  decide +kernel

end CollatzPosDens
