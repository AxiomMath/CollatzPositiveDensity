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
public import CollatzPosDens.Transfer.MxExactProfile

/-!
# The propagation mixing profiles

For each Fourier index `ι ∈ {o, b}` the propagation mixing profile is the real function
$$\mathfrak M_{\mathrm o}(x) := 126\,B_{\mathrm F}(\mathrm o)\,x^{-a_{\mathrm{mx}}(\mathrm o)}
  \log x + 105\,x^{-2},$$
$$\mathfrak M_{\mathrm b}(x) := 18\,B_{\mathrm F}(\mathrm b)\,x^{-a_{\mathrm{mx}}(\mathrm b)}
  \bigl(u_{\mathrm b}\log x + v_{\mathrm b}\bigr) + w_{\mathrm b}\,x^{-2},$$
where `B_F(ι)` is the Fourier prefactor `CollatzPosDens.fourierPrefactor`, `a_mx(ι)` is the
profile exponent `CollatzPosDens.amix`, `u_b`, `v_b`, `w_b` are the coefficients
`CollatzPosDens.bootU .b`, `CollatzPosDens.bootV .b`, `CollatzPosDens.bootW`,
`x ^ (-a) = 1 / x ^ a` is the positive real power and `log` is the natural logarithm. The profile
bounds the mean oscillation of the residue densities between two word lengths.

## Main definitions

* `CollatzPosDens.mxProfile`: the propagation mixing profile `𝔐_ι : ℝ → ℝ`.

## Main results

* `CollatzPosDens.mxProfile_o`, `CollatzPosDens.mxProfile_b`: the defining formulas of `𝔐_o`
  and `𝔐_b` with real powers.
* `CollatzPosDens.mxProfile_b_eq_mxExactProfile`: `𝔐_b` is the exact chained profile
  `CollatzPosDens.mxExactProfile` at the bootstrap index.
* `CollatzPosDens.mxProfile_eq_div_o`: for `0 ≤ x`,
  `𝔐_o(x) = 126 B_F(o) log x / x ^ a_mx(o) + 105 / x ^ 2`.
* `CollatzPosDens.mxProfile_pos`, `CollatzPosDens.mxProfile_nonneg`: `0 < 𝔐_ι(x)` for `1 ≤ x`.

## Implementation notes

The profile is defined on all of `ℝ`, through `Real.rpow` and `Real.log`; only its values at
positive arguments carry meaning.
-/

@[expose] public section

namespace CollatzPosDens

/-- The propagation mixing profile `𝔐_ι`:
`𝔐_o(x) := 126 B_F(o) x ^ (-a_mx(o)) log x + 105 x ^ (-2)` and
`𝔐_b(x) := 18 B_F(b) x ^ (-a_mx(b)) (u_b log x + v_b) + w_b x ^ (-2)`, with `x ^ (-a) = 1 / x ^ a`
the positive real power and `log` the natural logarithm. -/
@[collatz_pos_dens "def_mx_profile"]
noncomputable def mxProfile : FIndex → ℝ → ℝ
  | .o, x =>
    126 * fourierPrefactor .o * x ^ (-(amix .o : ℝ)) * Real.log x + 105 * x ^ (-2 : ℝ)
  | .b, x =>
    18 * fourierPrefactor .b * x ^ (-(amix .b : ℝ)) * (bootU .b * Real.log x + bootV .b) +
      (bootW : ℝ) * x ^ (-2 : ℝ)

/-- The defining formula of the propagation mixing profile at the original index. -/
theorem mxProfile_o (x : ℝ) :
    mxProfile .o x =
      126 * fourierPrefactor .o * x ^ (-(amix .o : ℝ)) * Real.log x + 105 * x ^ (-2 : ℝ) := rfl

/-- The defining formula of the propagation mixing profile at the bootstrap index. -/
theorem mxProfile_b (x : ℝ) :
    mxProfile .b x =
      18 * fourierPrefactor .b * x ^ (-(amix .b : ℝ)) * (bootU .b * Real.log x + bootV .b) +
        (bootW : ℝ) * x ^ (-2 : ℝ) := rfl

/-- The propagation mixing profile at the bootstrap index is the exact chained profile there. -/
theorem mxProfile_b_eq_mxExactProfile : mxProfile .b = mxExactProfile .b := rfl

/-- The propagation mixing profile at the original index with the negative powers written as
quotients. -/
theorem mxProfile_eq_div_o {x : ℝ} (hx : 0 ≤ x) :
    mxProfile .o x =
      126 * fourierPrefactor .o * Real.log x / x ^ (amix .o : ℝ) + 105 / x ^ 2 := by
  rw [mxProfile_o, Real.rpow_neg hx, Real.rpow_neg hx, Real.rpow_two]
  ring

/-- The propagation mixing profile is positive from `1` on. -/
theorem mxProfile_pos (ι : FIndex) {x : ℝ} (hx : 1 ≤ x) : 0 < mxProfile ι x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hp : ∀ a : ℝ, 0 < x ^ a := fun a => Real.rpow_pos_of_pos hx0 a
  cases ι
  · rw [mxProfile_o]
    have := fourierPrefactor_pos .o
    have := hp (-(amix .o : ℝ))
    have := hp (-2)
    positivity
  · rw [mxProfile_b_eq_mxExactProfile]
    exact mxExactProfile_pos .b hx

/-- The propagation mixing profile is nonnegative from `1` on. -/
theorem mxProfile_nonneg (ι : FIndex) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ mxProfile ι x :=
  (mxProfile_pos ι hx).le

end CollatzPosDens
