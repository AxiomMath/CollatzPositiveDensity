/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxCharacterInt

/-!
# Orthogonality of the characters of `G_n`

For `n ∈ ℕ` and `η ∈ G_n = ℤ/3^nℤ`,
$$\sum_{y \in G_n} e_n(\eta y) = \begin{cases} 3^n & \eta = 0, \\ 0 & \text{otherwise}.
\end{cases}$$
The character `e_n` is the standard additive character of `ℤ/3^nℤ`, which is primitive, so this
is Mathlib's orthogonality relation `AddChar.sum_mulShift`.

## Main results

* `CollatzPosDens.sum_fxChar_mul`: `∑_{y ∈ G_n} e_n(ηy)` equals `3^n` if `η = 0` and `0`
  otherwise.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- Orthogonality of the characters of `G_n`: `∑_{y ∈ G_n} e_n(ηy)` equals `3^n` if `η = 0`
and `0` otherwise. -/
@[collatz_pos_dens "lem_mx_orthogonality"]
theorem sum_fxChar_mul (n : ℕ) (η : ResidueGroup n) :
    ∑ y : ResidueGroup n, fxChar n (η * y) = if η = 0 then (3 ^ n : ℂ) else 0 := by
  simpa [ZMod.card, mul_comm η, fxChar] using
    AddChar.sum_mulShift (R := ResidueGroup n) η (ZMod.isPrimitive_stdAddChar (3 ^ n))

end CollatzPosDens
