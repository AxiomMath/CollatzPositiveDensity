/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Mixing.MxOsc
public import CollatzPosDens.Mixing.MxDftConvolution
public import CollatzPosDens.Mixing.MxDftFiber
public import CollatzPosDens.Mixing.MxParseval

/-!
# Oscillation of a convolution with a Fourier-decaying kernel

Let `0 ≤ m ≤ n`, let `h, t, c : G_n → ℝ` with `c(x) = ∑_y h(y) t(x - y)`, and suppose
`|t̂(ξ)| ≤ δ` for every `ξ` with `3^m ξ ≠ 0`. Then
`Osc_{m,n}(c)^2 ≤ δ^2 3^n ∑_y h(y)^2`.

With `d = c - Avg_{m,n} c`, Cauchy–Schwarz gives `Osc_{m,n}(c)^2 ≤ 3^n ∑_y d(y)^2`, which by
Parseval is `∑_ξ |d̂(ξ)|^2`. The coefficient `d̂(ξ)` vanishes when `3^m ξ = 0` and otherwise
equals `ĥ(ξ) t̂(ξ)`, of modulus at most `δ |ĥ(ξ)|`; a second use of Parseval concludes.

## Main results

* `CollatzPosDens.oscillation_sq_le_of_convolution`: `Osc_{m,n}(c)^2 ≤ δ^2 3^n ∑_y h(y)^2`.

## Implementation notes

The bound holds for every real `δ`, so no hypothesis `0 ≤ δ` is assumed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Let `0 ≤ m ≤ n`, `h, t, c : G_n → ℝ` with `c(x) = ∑_y h(y) t(x - y)` for all `x`, and
`δ` with `|t̂(ξ)| ≤ δ` whenever `3^m ξ ≠ 0`. Then
`Osc_{m,n}(c)^2 ≤ δ^2 3^n ∑_y h(y)^2`. -/
@[collatz_pos_dens "lem_mx_collision_osc"]
theorem oscillation_sq_le_of_convolution {m n : ℕ} (hmn : m ≤ n)
    (h t c : ResidueGroup n → ℝ) (hc : ∀ x, c x = ∑ y : ResidueGroup n, h y * t (x - y))
    (δ : ℝ)
    (ht : ∀ ξ : ResidueGroup n, (3 : ResidueGroup n) ^ m * ξ ≠ 0 →
      ‖fxDft n (fun y => (t y : ℂ)) ξ‖ ≤ δ) :
    oscillation hmn c ^ 2 ≤ δ ^ 2 * 3 ^ n * ∑ y : ResidueGroup n, h y ^ 2 := by
  set d : ResidueGroup n → ℝ := fun y => c y - fiberAvg hmn c y with hd
  have hcC : ∀ x, (c x : ℂ) = ∑ y : ResidueGroup n, (h y : ℂ) * (t (x - y) : ℂ) := by
    intro x
    rw [hc]
    push_cast
    rfl
  have hpt : ∀ ξ : ResidueGroup n, ‖fxDft n (fun y => (d y : ℂ)) ξ‖ ^ 2 ≤
      δ ^ 2 * ‖fxDft n (fun y => (h y : ℂ)) ξ‖ ^ 2 := by
    intro ξ
    rw [fxDft_sub_fiberAvg hmn c d (fun y => rfl) ξ,
      fxDft_eq_mul_of_convolution n (fun y => (h y : ℂ)) (fun y => (t y : ℂ)) _ hcC ξ]
    by_cases h0 : (3 : ResidueGroup n) ^ m * ξ ≠ 0
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0), one_mul, norm_mul, mul_pow, mul_comm (δ ^ 2)]
      gcongr
      exact ht ξ h0
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0), zero_mul, norm_zero, zero_pow two_ne_zero]
      positivity
  have hPd := sum_norm_fxDft_sq n (fun y => (d y : ℂ))
  have hPh := sum_norm_fxDft_sq n (fun y => (h y : ℂ))
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hPd hPh
  calc oscillation hmn c ^ 2 ≤ 3 ^ n * ∑ y : ResidueGroup n, d y ^ 2 := by
        simpa [oscillation, hd, card_univ, ZMod.card, sq_abs] using
          sq_sum_le_card_mul_sum_sq (s := (univ : Finset (ResidueGroup n))) (f := fun y => |d y|)
    _ = ∑ ξ : ResidueGroup n, ‖fxDft n (fun y => (d y : ℂ)) ξ‖ ^ 2 := hPd.symm
    _ ≤ ∑ ξ : ResidueGroup n, δ ^ 2 * ‖fxDft n (fun y => (h y : ℂ)) ξ‖ ^ 2 :=
      sum_le_sum fun ξ _ => hpt ξ
    _ = δ ^ 2 * 3 ^ n * ∑ y : ResidueGroup n, h y ^ 2 := by
      rw [← mul_sum, hPh, mul_assoc]

end CollatzPosDens
