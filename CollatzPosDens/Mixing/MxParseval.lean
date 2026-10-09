/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Characters.FxCharacterHom
public import CollatzPosDens.Characters.FxCharacterNeg
public import CollatzPosDens.Mixing.MxOrthogonality

/-!
# Parseval's identity on `G_n`

For `n ∈ ℕ`, `G_n = ℤ/3^nℤ` (`ResidueGroup n`) with additive characters `e_n` (`fxChar n`),
and `f : G_n → ℂ`, the unnormalized Fourier coefficients `f̂(ξ) = ∑_y f(y) e_n(-ξ y)` satisfy
$$\sum_{\xi \in G_n} |\hat f(\xi)|^2 = 3^n \sum_{y \in G_n} |f(y)|^2.$$
Expanding `|f̂(ξ)|^2 = f̂(ξ) conj (f̂(ξ))` as a double sum, the product of characters is
`e_n(ξ(y' - y))`, and summing over `ξ` by orthogonality leaves only the diagonal `y = y'`.

## Main results

* `CollatzPosDens.sum_norm_fxDft_sq`: Parseval's identity for `fxDft`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open ComplexConjugate Finset

/-- Parseval's identity on `G_n`: `∑_ξ |f̂(ξ)|^2 = 3^n ∑_y |f(y)|^2`. -/
@[collatz_pos_dens "lem_mx_parseval"]
theorem sum_norm_fxDft_sq (n : ℕ) (f : ResidueGroup n → ℂ) :
    ∑ ξ : ResidueGroup n, ‖fxDft n f ξ‖ ^ 2 = 3 ^ n * ∑ y : ResidueGroup n, ‖f y‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.mul_conj']
  have hconj : ∀ ξ, conj (fxDft n f ξ) =
      ∑ y' : ResidueGroup n, conj (f y') * fxChar n (ξ * y') := by
    intro ξ
    rw [fxDft_apply, map_sum]
    refine sum_congr rfl fun y' _ => ?_
    rw [map_mul, ← fxChar_neg_eq_conj, neg_neg]
  simp_rw [hconj, fxDft_apply, sum_mul_sum]
  have hterm : ∀ ξ y y' : ResidueGroup n,
      f y * fxChar n (-(ξ * y)) * (conj (f y') * fxChar n (ξ * y')) =
        f y * conj (f y') * fxChar n ((y' - y) * ξ) := by
    intro ξ y y'
    rw [show (y' - y) * ξ = -(ξ * y) + ξ * y' by ring, fxChar_add_eq_mul]
    ring
  simp_rw [hterm]
  rw [sum_comm, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_comm]
  simp_rw [← mul_sum, sum_fxChar_mul, sub_eq_zero, mul_ite, mul_zero, sum_ite_eq', mem_univ,
    ite_true]
  ring

end CollatzPosDens
