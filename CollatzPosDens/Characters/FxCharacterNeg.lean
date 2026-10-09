/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxCharacterAbs
public import CollatzPosDens.Characters.FxCharacterHom

/-!
# The standard character of `G_n` at `-x` is the conjugate

For `n : ℕ` and `x ∈ G_n = ℤ/3^nℤ`, the standard character satisfies
`e_n(-x) = conj (e_n(x))`. By the homomorphism property `e_n(-x) e_n(x) = e_n(0) = 1`, and since
`|e_n(x)| = 1` also `e_n(x) conj (e_n(x)) = 1`; hence both `e_n(-x)` and `conj (e_n(x))` equal
`e_n(x)⁻¹`.

## Main results

* `CollatzPosDens.fxChar_neg_eq_conj`: `e_n(-x) = conj (e_n(x))`.

## Implementation notes

`fxChar` is bundled as an `AddChar` on the finite group `G_n`, so the identity is Mathlib's
`AddChar.map_neg_eq_conj`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open ComplexConjugate

/-- The standard character at `-x` is the complex conjugate: `e_n(-x) = conj (e_n(x))`. -/
@[collatz_pos_dens "lem_fx_character_neg"]
theorem fxChar_neg_eq_conj (n : ℕ) (x : ResidueGroup n) :
    fxChar n (-x) = conj (fxChar n x) :=
  AddChar.map_neg_eq_conj _ x

end CollatzPosDens
