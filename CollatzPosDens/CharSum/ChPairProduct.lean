/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPairPoint
public import CollatzPosDens.Characters.FxCharacter
public import CollatzPosDens.Maps.Word

/-!
# The paired character product

Fix `n : ℕ` and `ξ ∈ G_n`. For integers `j ≥ 1`, `s ∈ ℤ` and a word `w` of positive integers,
the *paired character product* `Ep(j, s; w) ∈ ℂ` is defined by recursion on `|w|`, consuming
the letters of `w` two at a time:
`Ep(j, s; ∅) = 1`, `Ep(j, s; (a)) = e_n(-px(j, s + a) ξ)`, and for `w = (a₁, a₂) w'`,
`Ep(j, s; w) = e_n(-(2^{a₂} + 3) px(j, s + a₁ + a₂) ξ) · Ep(j + 1, s + a₁ + a₂; w')`.

## Main definitions

* `CollatzPosDens.chPairProduct n ξ j s w`: the paired character product `Ep(j, s; w)`.

## Main results

* `CollatzPosDens.chPairProduct_nil`, `CollatzPosDens.chPairProduct_singleton`,
  `CollatzPosDens.chPairProduct_cons_cons`: the three defining equations.

## Implementation notes

The parameters `n` and `ξ`, suppressed in [mazur2026], are explicit. The index `j` is a natural
number, as for `chPairPoint`; only `j ≥ 1` is used. The recursion is structural on the list `w`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The paired character product `Ep(j, s; w)`: `Ep(j, s; ∅) = 1`,
`Ep(j, s; (a)) = e_n(-px(j, s + a) ξ)`, and
`Ep(j, s; (a₁, a₂) w') = e_n(-(2^{a₂} + 3) px(j, s + a₁ + a₂) ξ) · Ep(j + 1, s + a₁ + a₂; w')`. -/
@[collatz_pos_dens "def_ch_pair_product"]
noncomputable def chPairProduct (n : ℕ) (ξ : ResidueGroup n) : ℕ → ℤ → Word → ℂ
  | _, _, [] => 1
  | j, s, [a] => fxChar n (-(chPairPoint n j (s + a) * ξ))
  | j, s, a₁ :: a₂ :: w =>
      fxChar n (-((2 ^ (a₂ : ℕ) + 3) * chPairPoint n j (s + a₁ + a₂) * ξ)) *
        chPairProduct n ξ (j + 1) (s + a₁ + a₂) w

/-- `Ep(j, s; ∅) = 1`. -/
@[simp]
theorem chPairProduct_nil (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ) :
    chPairProduct n ξ j s [] = 1 := by
  simp [chPairProduct]

/-- `Ep(j, s; (a)) = e_n(-px(j, s + a) ξ)`. -/
@[simp]
theorem chPairProduct_singleton (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ) (a : ℕ+) :
    chPairProduct n ξ j s [a] = fxChar n (-(chPairPoint n j (s + a) * ξ)) := by
  simp [chPairProduct]

/-- `Ep(j, s; (a₁, a₂) w') = e_n(-(2^{a₂} + 3) px(j, s + a₁ + a₂) ξ) · Ep(j + 1, s + a₁ + a₂; w')`.
-/
@[simp]
theorem chPairProduct_cons_cons (n : ℕ) (ξ : ResidueGroup n) (j : ℕ) (s : ℤ) (a₁ a₂ : ℕ+)
    (w : Word) :
    chPairProduct n ξ j s (a₁ :: a₂ :: w) =
      fxChar n (-((2 ^ (a₂ : ℕ) + 3) * chPairPoint n j (s + a₁ + a₂) * ξ)) *
        chPairProduct n ξ (j + 1) (s + a₁ + a₂) w := by
  simp [chPairProduct]

end CollatzPosDens
