/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxCharacter

/-!
# The character `e_n` through an integer representative

Let `e_n = CollatzPosDens.fxChar n` be the standard additive character of
`G_n = ℤ/3^nℤ` (the type `CollatzPosDens.ResidueGroup n`), and let `x̃ = x.val` be the least
nonnegative representative of `x ∈ G_n`. For any integer `a ≡ x̃ (mod 3^n)`, the character value
is `e_n(x) = exp(2πi a / 3^n)`: the formula defining `e_n` does not depend on the choice of
integer representative, since `exp(2πik) = 1` for every integer `k`.

## Main results

* `CollatzPosDens.fxChar_eq_exp_of_intModEq`: `e_n(x) = exp(2πi a / 3^n)` whenever
  `a ≡ x̃ (mod 3^n)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- If `a ∈ ℤ` satisfies `a ≡ x̃ (mod 3^n)`, where `x̃ = x.val` is the least nonnegative
representative of `x ∈ G_n`, then `e_n(x) = exp(2πi a / 3^n)`. -/
@[collatz_pos_dens "lem_fx_character_int"]
theorem fxChar_eq_exp_of_intModEq (n : ℕ) (x : ResidueGroup n) (a : ℤ)
    (ha : a ≡ (x.val : ℤ) [ZMOD 3 ^ n]) :
    fxChar n x = exp (2 * π * I * a / 3 ^ n) := by
  have hx : ((a : ℤ) : ResidueGroup n) = x := by
    rw [(ZMod.intCast_eq_intCast_iff a _ (3 ^ n)).2 (by exact_mod_cast ha)]
    simp
  rw [← hx, fxChar_intCast]

end CollatzPosDens
