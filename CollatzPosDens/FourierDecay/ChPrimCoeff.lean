/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Dstar
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The primitive Fourier coefficient constant `C_*`

This file defines the positive real number
$$C_* := (160\,D_*)^{10241/4096},$$
where `D_*` is the renewal threshold `CollatzPosDens.Dstar`. It is the constant in the
explicit decay bound `|μ̂_n(ξ)| ≤ C_* / n^{10241/4096}` for the Fourier coefficients at
primitive frequencies.

## Main definitions

* `CollatzPosDens.Cstar`: the constant `C_* ∈ ℝ`.

## Main results

* `CollatzPosDens.Cstar_def`: the defining formula `C_* = (160 D_*)^{10241/4096}`.
* `CollatzPosDens.Cstar_pos`: `0 < C_*`.
* `CollatzPosDens.one_le_Cstar`: `1 ≤ C_*`.

## Implementation notes

The exponent `10241/4096` is not an integer, so the power is the real power `Real.rpow`.
Its base `160 D_*` is positive, so the real power is the genuine positive power. Since `D_*`
is a number with thousands of digits, `C_*` is irreducible and is used only through
`Cstar_def`, `Cstar_pos` and `one_le_Cstar`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The primitive Fourier coefficient constant `C_* := (160 D_*)^{10241/4096} ∈ ℝ`. -/
@[collatz_pos_dens "def_ch_prim_coeff", irreducible]
noncomputable def Cstar : ℝ :=
  (160 * (Dstar : ℝ)) ^ (10241 / 4096 : ℝ)

/-- The defining formula of `C_*`. -/
theorem Cstar_def : Cstar = (160 * (Dstar : ℝ)) ^ (10241 / 4096 : ℝ) := by
  unfold Cstar; rfl

/-- The base `160 D_*` of `C_*` is at least `1`. -/
theorem one_le_160_mul_Dstar : (1 : ℝ) ≤ 160 * (Dstar : ℝ) := by
  have h : (1 : ℝ) ≤ Dstar := by exact_mod_cast one_le_Dstar
  linarith

/-- `C_*` is at least `1`. -/
theorem one_le_Cstar : 1 ≤ Cstar := by
  rw [Cstar_def]
  exact Real.one_le_rpow one_le_160_mul_Dstar (by norm_num)

/-- `C_*` is positive. -/
theorem Cstar_pos : 0 < Cstar :=
  zero_lt_one.trans_le one_le_Cstar

end CollatzPosDens
