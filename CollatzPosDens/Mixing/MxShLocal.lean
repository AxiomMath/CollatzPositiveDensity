/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Amix
public import CollatzPosDens.Transfer.S02Bstar

/-!
# The local profile of the shell cut

For each Fourier index `ι ∈ {o, b}` the local profile of the shell cut is the real function
$$Q_ι(x) := 18\,B_{\mathrm F}(ι)\,x^{-a_{\mathrm{mx}}(ι)}\log x + 15\,x^{-2},$$
where `B_F(ι)` is the Fourier prefactor `CollatzPosDens.fourierPrefactor`, `a_mx(ι)` is the
profile exponent `CollatzPosDens.amix`, `x ^ (-a) = 1 / x ^ a` is the positive real power and
`log` is the natural logarithm.

## Main definitions

* `CollatzPosDens.mxShLocal`: the local profile `Q_ι : ℝ → ℝ`.

## Main results

* `CollatzPosDens.mxShLocal_def`: the defining formula of `Q_ι(x)` with real powers.
* `CollatzPosDens.mxShLocal_eq_div`: for `0 ≤ x`,
  `Q_ι(x) = 18 B_F(ι) log x / x ^ a_mx(ι) + 15 / x ^ 2`.
* `CollatzPosDens.mxShLocal_pos`, `CollatzPosDens.mxShLocal_nonneg`: `0 < Q_ι(x)` for `1 ≤ x`.

## Implementation notes

The profile is defined on all of `ℝ`, through `Real.rpow` and `Real.log`; only its values at
positive arguments carry meaning.
-/

@[expose] public section

namespace CollatzPosDens

/-- The local profile of the shell cut,
`Q_ι(x) := 18 B_F(ι) x ^ (-a_mx(ι)) log x + 15 x ^ (-2)`, with `x ^ (-a) = 1 / x ^ a` the positive
real power and `log` the natural logarithm. -/
@[collatz_pos_dens "def_mx_sh_local"]
noncomputable def mxShLocal (ι : FIndex) (x : ℝ) : ℝ :=
  18 * fourierPrefactor ι * x ^ (-(amix ι : ℝ)) * Real.log x + 15 * x ^ (-2 : ℝ)

/-- The defining formula of the local profile of the shell cut. -/
theorem mxShLocal_def (ι : FIndex) (x : ℝ) :
    mxShLocal ι x =
      18 * fourierPrefactor ι * x ^ (-(amix ι : ℝ)) * Real.log x + 15 * x ^ (-2 : ℝ) := rfl

/-- The local profile of the shell cut with the negative powers written as quotients. -/
theorem mxShLocal_eq_div (ι : FIndex) {x : ℝ} (hx : 0 ≤ x) :
    mxShLocal ι x = 18 * fourierPrefactor ι * Real.log x / x ^ (amix ι : ℝ) + 15 / x ^ 2 := by
  rw [mxShLocal_def, Real.rpow_neg hx, Real.rpow_neg hx, Real.rpow_two]
  ring

/-- The local profile of the shell cut is positive from `1` on. -/
theorem mxShLocal_pos (ι : FIndex) {x : ℝ} (hx : 1 ≤ x) : 0 < mxShLocal ι x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have := Real.log_nonneg hx
  have := fourierPrefactor_pos ι
  have := Real.rpow_pos_of_pos hx0 (-(amix ι : ℝ))
  have := Real.rpow_pos_of_pos hx0 (-2)
  rw [mxShLocal_def]
  positivity

/-- The local profile of the shell cut is nonnegative from `1` on. -/
theorem mxShLocal_nonneg (ι : FIndex) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ mxShLocal ι x :=
  (mxShLocal_pos ι hx).le

end CollatzPosDens
