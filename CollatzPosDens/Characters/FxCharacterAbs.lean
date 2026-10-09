/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxCharacter

/-!
# The standard character of `G_n` has modulus one

For `n : ℕ` and `x ∈ G_n = ℤ/3^nℤ` (the type `CollatzPosDens.ResidueGroup n`), the standard
additive character `e_n = CollatzPosDens.fxChar n` satisfies `|e_n(x)| = 1`: indeed
`e_n(x) = exp(i t)` with the real number `t = 2π x̃ / 3^n`, where `x̃` is the least nonnegative
representative of `x`, and `|exp(i t)| = 1` for real `t`.

## Main results

* `CollatzPosDens.fxChar_norm_eq_one`: `‖e_n(x)‖ = 1`.

## Implementation notes

The modulus `|·|` on `ℂ` is Mathlib's norm `‖·‖`. Since `e_n` is bundled as an `AddChar` of a
finite group, the statement is an instance of `AddChar.norm_apply`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The standard character has modulus one: `|e_n(x)| = 1` for every `x ∈ G_n`. -/
@[collatz_pos_dens "lem_fx_character_abs"]
theorem fxChar_norm_eq_one (n : ℕ) (x : ResidueGroup n) : ‖fxChar n x‖ = 1 :=
  AddChar.norm_apply _ x

end CollatzPosDens
