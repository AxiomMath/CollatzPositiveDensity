/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxGateUnion
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Transfer.RefDensity
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# The gate subdensity `g_n`

For an integer `n ≥ 1`, the *gate subdensity* `g_n : G_n → ℝ` rescales the submass of the gate
union `𝒰_n` exactly as the reference density `ρ_n` rescales the reference law:
$$g_n(y) = \tfrac23\, 3^n\, \bigl(\mathrm{Sub}^n_{\mathcal U_n}(y)\bigr)^{\mathbb R},$$
where for `x ∈ [0, ∞]` the real number `x^ℝ` is `x` when `x < ∞` and `0` when `x = ∞`.

## Main definitions

* `CollatzPosDens.mxSubdensity n`: the function `g_n : G_n → ℝ`.

## Main results

* `CollatzPosDens.mxSubdensity_def`: the unfolding of `g_n(y)`.
* `CollatzPosDens.mxSubdensity_nonneg`: `0 ≤ g_n(y)`.

## Implementation notes

As in `CollatzPosDens.refDensity`, the operation `x ↦ x^ℝ` is `ENNReal.toReal`, which sends `∞`
to `0`. The hypothesis `n ≥ 1` is not needed to form the function, so it is defined for every
`n : ℕ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The gate subdensity `g_n(y) = (2/3) · 3^n · (Sub^n_{𝒰_n}(y))^ℝ` on `G_n`, where `x^ℝ` is
`ENNReal.toReal x` (equal to `x` for `x < ∞` and to `0` for `x = ∞`). -/
@[collatz_pos_dens "def_mx_subdensity"]
noncomputable def mxSubdensity (n : ℕ) (y : ResidueGroup n) : ℝ :=
  2 / 3 * 3 ^ n * (subMass n (mxGateUnion n) y).toReal

/-- Unfolding lemma for `mxSubdensity`. -/
theorem mxSubdensity_def (n : ℕ) (y : ResidueGroup n) :
    mxSubdensity n y = 2 / 3 * 3 ^ n * (subMass n (mxGateUnion n) y).toReal :=
  rfl

/-- The gate subdensity is nonnegative. -/
theorem mxSubdensity_nonneg (n : ℕ) (y : ResidueGroup n) : 0 ≤ mxSubdensity n y := by
  unfold mxSubdensity
  positivity

end CollatzPosDens
