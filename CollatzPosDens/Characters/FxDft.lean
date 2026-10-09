/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Fourier.ZMod
public import CollatzPosDens.Attr
public import CollatzPosDens.Characters.FxCharacter
public import CollatzPosDens.Transfer.RefLaw

/-!
# Fourier coefficients on `G_n`

For `n ∈ ℕ`, a function `f : G_n → ℂ` and `ξ ∈ G_n`, the Fourier coefficient of `f` at `ξ` is
`f̂(ξ) = ∑_{y ∈ G_n} f(y) e_n(-ξ y)`, where `e_n` is the standard additive character of
`G_n = ℤ/3^nℤ`. A real-valued function is regarded as complex-valued; in particular the
reference law `μ_n` is regarded as the real-valued function `y ↦ μ_n(y)^ℝ`, giving
`μ̂_n(ξ) = ∑_{y ∈ G_n} μ_n(y)^ℝ e_n(-ξ y)`.

## Main definitions

* `CollatzPosDens.fxDft n f ξ`: the Fourier coefficient `f̂(ξ)` of `f : G_n → ℂ`.
* `CollatzPosDens.refLawDft n ξ`: the Fourier coefficient `μ̂_n(ξ)` of the reference law.

## Main results

* `CollatzPosDens.fxDft_eq_dft`: `f̂` is Mathlib's discrete Fourier transform `𝓕 f`.
* `CollatzPosDens.refLawDft_apply`: `μ̂_n(ξ) = ∑_y μ_n(y)^ℝ e_n(-ξ y)`.

## Implementation notes

The operation `x ↦ x^ℝ` on `[0, ∞]` is `ENNReal.toReal`, followed by the coercion `ℝ → ℂ`.
The transform agrees with `ZMod.dft` on `ZMod (3 ^ n)`, so its general theory (inversion,
Parseval) is available through `fxDft_eq_dft`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open ZMod

/-- The Fourier coefficient `f̂(ξ) = ∑_{y ∈ G_n} f(y) e_n(-ξ y)` of `f : G_n → ℂ`. -/
@[collatz_pos_dens "def_fx_dft"]
noncomputable def fxDft (n : ℕ) (f : ResidueGroup n → ℂ) (ξ : ResidueGroup n) : ℂ :=
  ∑ y : ResidueGroup n, f y * fxChar n (-(ξ * y))

/-- The Fourier coefficient `μ̂_n(ξ)` of the reference law, with `μ_n` regarded as the
real-valued function `y ↦ μ_n(y)^ℝ`. -/
@[collatz_pos_dens "def_fx_dft"]
noncomputable def refLawDft (n : ℕ) (ξ : ResidueGroup n) : ℂ :=
  fxDft n (fun y => ((refLaw n y).toReal : ℂ)) ξ

/-- The defining formula of `fxDft`. -/
theorem fxDft_apply (n : ℕ) (f : ResidueGroup n → ℂ) (ξ : ResidueGroup n) :
    fxDft n f ξ = ∑ y : ResidueGroup n, f y * fxChar n (-(ξ * y)) := rfl

/-- The defining formula `μ̂_n(ξ) = ∑_{y ∈ G_n} μ_n(y)^ℝ e_n(-ξ y)`. -/
theorem refLawDft_apply (n : ℕ) (ξ : ResidueGroup n) :
    refLawDft n ξ = ∑ y : ResidueGroup n, ((refLaw n y).toReal : ℂ) * fxChar n (-(ξ * y)) :=
  rfl

/-- The Fourier coefficients `f̂` are Mathlib's discrete Fourier transform on `ZMod (3 ^ n)`. -/
theorem fxDft_eq_dft (n : ℕ) (f : ResidueGroup n → ℂ) : fxDft n f = 𝓕 f := by
  ext ξ
  rw [fxDft_apply, dft_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_eq_mul, mul_comm (f y), mul_comm ξ y]
  rfl

/-- The Fourier coefficient at `0` is the sum of the values: `f̂(0) = ∑_y f(y)`. -/
@[simp]
theorem fxDft_zero (n : ℕ) (f : ResidueGroup n → ℂ) :
    fxDft n f 0 = ∑ y : ResidueGroup n, f y := by
  simp [fxDft_apply]

end CollatzPosDens
