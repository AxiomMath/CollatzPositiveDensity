/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Amix
public import CollatzPosDens.Transfer.S02Bstar
public import CollatzPosDens.Transfer.MxBootV
public import CollatzPosDens.Transfer.MxBootW

/-!
# The exact chained profile

For each Fourier index `ι ∈ {o, b}` the exact chained profile is the real function
$$\mathfrak M^{\mathrm{ex}}_\iota(x) := 18\,B_{\mathrm F}(\iota)\,x^{-a_{\mathrm{mx}}(\iota)}
  \bigl(u_\iota\log x + v_\iota\bigr) + w_{\mathrm b}\,x^{-2},$$
where `B_F(ι)` is the Fourier prefactor `CollatzPosDens.fourierPrefactor`, `a_mx(ι)` is the
profile exponent `CollatzPosDens.amix`, `u_ι`, `v_ι` are the index-dependent coefficients
`CollatzPosDens.bootU`, `CollatzPosDens.bootV`, `w_b` is the quadratic coefficient
`CollatzPosDens.bootW`, `x ^ (-a) = 1 / x ^ a` is the positive real power and `log` is the
natural logarithm.

## Main definitions

* `CollatzPosDens.mxExactProfile`: the exact chained profile `𝔐^ex_ι : ℝ → ℝ`.

## Main results

* `CollatzPosDens.mxExactProfile_eq`: the defining formula with real powers.
* `CollatzPosDens.mxExactProfile_eq_div`: for `0 ≤ x`, the formula with the negative powers
  written as quotients.
* `CollatzPosDens.mxExactProfile_pos`: `0 < 𝔐^ex_ι(x)` for `1 ≤ x`.
* `CollatzPosDens.mxExactProfile_nonneg`: `0 ≤ 𝔐^ex_ι(x)` for `1 ≤ x`.

## Implementation notes

The profile is defined on all of `ℝ`, through `Real.rpow` and `Real.log`; only its values at
positive arguments are of interest.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact chained profile
`𝔐^ex_ι(x) := 18 B_F(ι) x ^ (-a_mx(ι)) (u_ι log x + v_ι) + w_b x ^ (-2)`, with
`x ^ (-a) = 1 / x ^ a` the positive real power and `log` the natural logarithm. -/
@[collatz_pos_dens "def_mx_exact_profile"]
noncomputable def mxExactProfile (ι : FIndex) (x : ℝ) : ℝ :=
  18 * fourierPrefactor ι * x ^ (-(amix ι : ℝ)) * (bootU ι * Real.log x + bootV ι) +
    (bootW : ℝ) * x ^ (-2 : ℝ)

/-- The defining formula of the exact chained profile. -/
theorem mxExactProfile_eq (ι : FIndex) (x : ℝ) :
    mxExactProfile ι x =
      18 * fourierPrefactor ι * x ^ (-(amix ι : ℝ)) * (bootU ι * Real.log x + bootV ι) +
        (bootW : ℝ) * x ^ (-2 : ℝ) := rfl

/-- The exact chained profile with the negative powers written as quotients. -/
theorem mxExactProfile_eq_div (ι : FIndex) {x : ℝ} (hx : 0 ≤ x) :
    mxExactProfile ι x =
      18 * fourierPrefactor ι * (bootU ι * Real.log x + bootV ι) / x ^ (amix ι : ℝ) +
        (bootW : ℝ) / x ^ 2 := by
  rw [mxExactProfile_eq, Real.rpow_neg hx, Real.rpow_neg hx, Real.rpow_two]
  ring

/-- The exact chained profile is positive from `1` on. -/
theorem mxExactProfile_pos (ι : FIndex) {x : ℝ} (hx : 1 ≤ x) : 0 < mxExactProfile ι x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have := Real.log_nonneg hx
  have := fourierPrefactor_pos ι
  have := Real.rpow_pos_of_pos hx0 (-(amix ι : ℝ))
  have := Real.rpow_pos_of_pos hx0 (-2)
  have := bootU_pos ι
  have := bootV_pos ι
  have : (0 : ℝ) < bootW := by exact_mod_cast bootW_pos
  rw [mxExactProfile_eq]
  positivity

/-- The exact chained profile is nonnegative from `1` on. -/
theorem mxExactProfile_nonneg (ι : FIndex) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ mxExactProfile ι x :=
  (mxExactProfile_pos ι hx).le

end CollatzPosDens
