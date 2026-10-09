/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Characters.FxCharacterHom

/-!
# The convolution theorem on `G_n`

For `n ∈ ℕ` and `f, g, c : G_n → ℂ` with `c(x) = ∑_{y ∈ G_n} f(y) g(x - y)` for all `x`, the
Fourier coefficients satisfy `ĉ(ξ) = f̂(ξ) ĝ(ξ)` for every `ξ ∈ G_n`.

## Main results

* `CollatzPosDens.fxDft_eq_mul_of_convolution`: `ĉ(ξ) = f̂(ξ) ĝ(ξ)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §13.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- The convolution theorem on `G_n`: if `c(x) = ∑_y f(y) g(x - y)` for all `x`, then
`ĉ(ξ) = f̂(ξ) ĝ(ξ)` for every `ξ`. -/
@[collatz_pos_dens "lem_mx_dft_convolution"]
theorem fxDft_eq_mul_of_convolution (n : ℕ) (f g c : ResidueGroup n → ℂ)
    (hc : ∀ x, c x = ∑ y : ResidueGroup n, f y * g (x - y)) (ξ : ResidueGroup n) :
    fxDft n c ξ = fxDft n f ξ * fxDft n g ξ := by
  simp_rw [fxDft_apply, hc, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Equiv.sum_comp (Equiv.addRight y), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : -(ξ * (x + y)) = -(ξ * y) + -(ξ * x) := by ring
  rw [Equiv.coe_addRight, add_sub_cancel_right, h, fxChar_add_eq_mul]
  ring

end CollatzPosDens
