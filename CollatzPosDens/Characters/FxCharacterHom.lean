/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxCharacterInt

/-!
# The standard character of `G_n` is a homomorphism

For `n : ℕ` and `x, y ∈ G_n = ℤ/3^nℤ`, the standard character satisfies
`e_n(x + y) = e_n(x) e_n(y)`. Writing `x̃, ỹ` for the least nonnegative representatives of `x`
and `y`, the integer `x̃ + ỹ` is congruent modulo `3^n` to the least nonnegative representative
of `x + y`, so `e_n(x + y) = exp(2πi (x̃ + ỹ) / 3^n)`, which splits as a product by the functional
equation of the exponential.

## Main results

* `CollatzPosDens.fxChar_add_eq_mul`: `e_n(x + y) = e_n(x) e_n(y)`.

## Implementation notes

`fxChar` is bundled as an `AddChar`, so the identity is Mathlib's `AddChar.map_add_eq_mul`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- The standard character is a homomorphism: `e_n(x + y) = e_n(x) e_n(y)` for `x, y ∈ G_n`. -/
@[collatz_pos_dens "lem_fx_character_hom"]
theorem fxChar_add_eq_mul (n : ℕ) (x y : ResidueGroup n) :
    fxChar n (x + y) = fxChar n x * fxChar n y :=
  AddChar.map_add_eq_mul _ x y

end CollatzPosDens
