/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.X
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The mixing coefficient `C`

The mixing coefficient is the real number
$$C := \frac{477}{20}\, X_*^{A_*} + \frac{159}{10},$$
where `X_* = CollatzPosDens.Xstar`, `A_* = CollatzPosDens.Aexp = 10241/4096` and
`X_*^{A_*} = \exp(A_* \log X_*)` is the positive real power.

## Main definitions

* `CollatzPosDens.mixingConst`: the mixing coefficient `C ∈ ℝ`.

## Main results

* `CollatzPosDens.mixingConst_def`: the defining formula of `C`.
* `CollatzPosDens.Xstar_rpow_Aexp_pos`, `CollatzPosDens.Xstar_rpow_Aexp_eq_exp`:
  `0 < X_*^{A_*} = exp (A_* log X_*)`.
* `CollatzPosDens.mixingConst_eq_exp`: the defining formula with the power written as
  `exp (A_* log X_*)`.
* `CollatzPosDens.mixingConst_pos`, `CollatzPosDens.lt_mixingConst`,
  `CollatzPosDens.one_le_mixingConst`, `CollatzPosDens.mul_rpow_lt_mixingConst`: the bounds
  `0 < C`, `159/10 < C`, `1 ≤ C` and `477/20 X_*^{A_*} < C`.

## Implementation notes

The power is Mathlib's real power `Real.rpow` of the casts of `X_* ∈ ℚ` and `A_* ∈ ℚ` to `ℝ`.
Since `X_* > 0`, it agrees with `exp (A_* log X_*)`, as `Xstar_rpow_Aexp_eq_exp` records.
-/

@[expose] public section

namespace CollatzPosDens

/-- The mixing coefficient `C := 477/20 · X_*^{A_*} + 159/10 ∈ ℝ`, with `X_*^{A_*}` the positive
real power. -/
@[collatz_pos_dens "def_mixing_const"]
noncomputable def mixingConst : ℝ := 477 / 20 * (Xstar : ℝ) ^ (Aexp : ℝ) + 159 / 10

/-- The defining formula of the mixing coefficient. -/
theorem mixingConst_def :
    mixingConst = 477 / 20 * (Xstar : ℝ) ^ (Aexp : ℝ) + 159 / 10 := rfl

/-- The real power `X_*^{A_*}` is positive. -/
theorem Xstar_rpow_Aexp_pos : 0 < (Xstar : ℝ) ^ (Aexp : ℝ) :=
  Real.rpow_pos_of_pos (by exact_mod_cast Xstar_pos) _

/-- The real power `X_*^{A_*}` equals `exp (A_* log X_*)`. -/
theorem Xstar_rpow_Aexp_eq_exp :
    (Xstar : ℝ) ^ (Aexp : ℝ) = Real.exp ((Aexp : ℝ) * Real.log (Xstar : ℝ)) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast Xstar_pos), mul_comm]

/-- The defining formula of the mixing coefficient, with the power as `exp (A_* log X_*)`. -/
theorem mixingConst_eq_exp :
    mixingConst = 477 / 20 * Real.exp ((Aexp : ℝ) * Real.log (Xstar : ℝ)) + 159 / 10 := by
  rw [mixingConst_def, Xstar_rpow_Aexp_eq_exp]

/-- `477/20 · X_*^{A_*} < C`. -/
theorem mul_rpow_lt_mixingConst : 477 / 20 * (Xstar : ℝ) ^ (Aexp : ℝ) < mixingConst := by
  rw [mixingConst_def]; linarith

/-- `159/10 < C`. -/
theorem lt_mixingConst : 159 / 10 < mixingConst := by
  rw [mixingConst_def]; linarith [Xstar_rpow_Aexp_pos]

/-- The mixing coefficient is positive. -/
theorem mixingConst_pos : 0 < mixingConst := by
  linarith [lt_mixingConst]

/-- `1 ≤ C`. -/
theorem one_le_mixingConst : 1 ≤ mixingConst := by
  linarith [lt_mixingConst]

end CollatzPosDens
