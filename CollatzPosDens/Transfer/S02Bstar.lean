/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02DF
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The Fourier prefactor `B_F`

At each Fourier parameter index `ι ∈ {o, b}` the Fourier prefactor is the real number
$$B_{\mathrm F}(ι) := \bigl(\tfrac{15}{2} D_F(ι)\bigr)^{A_*(ι)},$$
where `D_F(ι)` is the Fourier decay constant `CollatzPosDens.DF`, `A_*(ι)` is the decay exponent
`CollatzPosDens.Aexp`, and the power is the positive real power `y ^ A_*(ι) = exp (A_*(ι) log y)`
of the positive base `y = 15/2 · D_F(ι)`.

## Main definitions

* `CollatzPosDens.fourierPrefactor`: the Fourier prefactor `B_F(ι) = (15/2 · D_F(ι))^{A_*(ι)}`.

## Main results

* `CollatzPosDens.fourierPrefactor_def`: the defining formula of `B_F(ι)` as a real power.
* `CollatzPosDens.fourierPrefactor_base_pos`: the base `15/2 · D_F(ι)` is positive.
* `CollatzPosDens.fourierPrefactor_eq_exp`: `B_F(ι) = exp (A_*(ι) log (15/2 · D_F(ι)))`.
* `CollatzPosDens.fourierPrefactor_pos`, `CollatzPosDens.fourierPrefactor_nonneg`:
  `0 < B_F(ι)` and `0 ≤ B_F(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The Fourier prefactor `B_F(ι) := (15/2 · D_F(ι))^{A_*(ι)} ∈ ℝ`, with the power the positive
real power `y ^ A_*(ι) = exp (A_*(ι) log y)`. -/
@[collatz_pos_dens "def_s02_Bstar"]
noncomputable def fourierPrefactor (ι : FIndex) : ℝ := (15 / 2 * (DF ι : ℝ)) ^ (Aexp ι : ℝ)

/-- The defining formula of `B_F(ι)` as a real power. -/
theorem fourierPrefactor_def (ι : FIndex) :
    fourierPrefactor ι = (15 / 2 * (DF ι : ℝ)) ^ (Aexp ι : ℝ) := rfl

/-- The base `15/2 · D_F(ι)` of the Fourier prefactor is positive. -/
theorem fourierPrefactor_base_pos (ι : FIndex) : 0 < 15 / 2 * (DF ι : ℝ) := by
  have : (0 : ℝ) < DF ι := by exact_mod_cast DF_pos ι
  positivity

/-- `B_F(ι) = exp (A_*(ι) log (15/2 · D_F(ι)))`, the positive real power written through `exp`
and `log`. -/
theorem fourierPrefactor_eq_exp (ι : FIndex) :
    fourierPrefactor ι = Real.exp ((Aexp ι : ℝ) * Real.log (15 / 2 * (DF ι : ℝ))) := by
  rw [fourierPrefactor_def, Real.rpow_def_of_pos (fourierPrefactor_base_pos ι), mul_comm]

/-- The Fourier prefactor is positive. -/
theorem fourierPrefactor_pos (ι : FIndex) : 0 < fourierPrefactor ι :=
  Real.rpow_pos_of_pos (fourierPrefactor_base_pos ι) _

/-- The Fourier prefactor is nonnegative. -/
theorem fourierPrefactor_nonneg (ι : FIndex) : 0 ≤ fourierPrefactor ι :=
  (fourierPrefactor_pos ι).le

end CollatzPosDens
