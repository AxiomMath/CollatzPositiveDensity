/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# The standard additive character of `G_n`

For `n : ℕ` and `x ∈ G_n = ℤ/3^nℤ` (the type `CollatzPosDens.ResidueGroup n`), the standard
additive character is `e_n(x) = exp(2πi x̃ / 3^n) ∈ ℂ`, where `x̃ ∈ {0, …, 3^n - 1}` is the least
nonnegative representative of `x`. It is an additive character of `G_n` with values on the unit
circle.

## Main definitions

* `CollatzPosDens.fxChar n`: the additive character `e_n : G_n → ℂ`.

## Main results

* `CollatzPosDens.fxChar_apply`: `e_n(x) = exp(2πi x̃ / 3^n)`, the defining formula.
* `CollatzPosDens.fxChar_intCast`: `e_n(j) = exp(2πi j / 3^n)` for any integer `j`.

## Implementation notes

The character is Mathlib's `ZMod.stdAddChar` on `ZMod (3 ^ n)`, so it is bundled as an
`AddChar`; the least nonnegative representative `x̃` is `ZMod.val`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- The standard additive character `e_n(x) = exp(2πi x̃ / 3^n)` of `G_n = ℤ/3^nℤ`. -/
@[collatz_pos_dens "def_fx_character"]
noncomputable def fxChar (n : ℕ) : AddChar (ResidueGroup n) ℂ :=
  ZMod.stdAddChar

/-- The value of `e_n` at the residue of an integer `j` is `exp(2πi j / 3^n)`. -/
theorem fxChar_intCast (n : ℕ) (j : ℤ) :
    fxChar n (j : ResidueGroup n) = exp (2 * π * I * j / 3 ^ n) := by
  rw [fxChar, ZMod.stdAddChar_coe]
  push_cast
  rfl

/-- The value of `e_n` at the residue of a natural number `j` is `exp(2πi j / 3^n)`. -/
theorem fxChar_natCast (n : ℕ) (j : ℕ) :
    fxChar n (j : ResidueGroup n) = exp (2 * π * I * j / 3 ^ n) := by
  simpa using fxChar_intCast n j

/-- The defining formula `e_n(x) = exp(2πi x̃ / 3^n)`, with `x̃ = x.val` the least nonnegative
representative of `x`. -/
theorem fxChar_apply (n : ℕ) (x : ResidueGroup n) :
    fxChar n x = exp (2 * π * I * x.val / 3 ^ n) := by
  have h := fxChar_natCast n x.val
  rwa [ZMod.natCast_zmod_val] at h

/-- `e_n(0) = 1`. -/
theorem fxChar_zero (n : ℕ) : fxChar n 0 = 1 :=
  AddChar.map_zero_eq_one _

end CollatzPosDens
