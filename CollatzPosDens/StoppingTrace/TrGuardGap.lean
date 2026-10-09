/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrDeltaSix
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.Transfer.Omega

/-!
# Guard for a positive initial gap

The passage surplus at gap six, damped by the single-passage survival `1 - d_*`, exceeds the
two-passage correction: `(1 - d_*) δ_tr(6) > Ω_*`. All three quantities are explicit rationals
(the value of `δ_tr(6)` is computed in `trDelta_six`), and
`(1 - d_*) δ_tr(6) - Ω_* =
31870583226525836929616430324021343424825895322789577973634564070497907817 /
78012218368000000000000000000000000000000000000000000000000000000000000000000 > 0`.

## Main results

* `CollatzPosDens.omegaStar_lt_one_sub_dStar_mul_trDelta_six`: `Ω_* < (1 - d_*) δ_tr(6)`.

## Implementation notes

The inequality is stated in `ℝ`, where `δ_tr` lives, with `d_*` and `Ω_*` cast from `ℚ`; it is
written with `<`, i.e. as `Ω_* < (1 - d_*) δ_tr(6)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Guard for a positive initial gap.** `(1 - d_*) δ_tr(6) > Ω_*`. -/
@[collatz_pos_dens "lem_tr_guard_gap"]
theorem omegaStar_lt_one_sub_dStar_mul_trDelta_six :
    (omegaStar : ℝ) < (1 - (dStar : ℝ)) * trDelta 6 := by
  rw [trDelta_six, dStar_eq, omegaStar_eq]
  push_cast
  norm_num

end CollatzPosDens
