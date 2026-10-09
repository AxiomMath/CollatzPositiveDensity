/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.StoppingTrace.TrE8
public import Mathlib.Order.MinMax
public import Mathlib.Tactic.NormNum

/-!
# Positivity of the eighth-order defect at the trace tilts

The eighth-order exponential defect `E₈` is positive at both tilts used by the stopping trace:
`min (E₈(γ_*), E₈(κ_* γ_*)) > 0`. Since `γ_* = 87/200` and `κ_* γ_* = 87/1250`, exact
evaluation gives
`E₈(γ_*) = 4045450969326735650631 / 11468800000000000000000` and
`E₈(κ_* γ_*) = 1795318739900437013458321431 / 26702880859375000000000000000`,
both quotients of positive integers.

## Main results

* `CollatzPosDens.E8_gammaStar`: the exact value of `E₈(γ_*)`.
* `CollatzPosDens.E8_kappaStar_mul_gammaStar`: the exact value of `E₈(κ_* γ_*)`.
* `CollatzPosDens.min_E8_gammaStar_pos`: `0 < min (E₈(γ_*), E₈(κ_* γ_*))`.

## Implementation notes

The constants `γ_*` and `κ_*` are rational; they are cast to `ℝ` before `E₈` is applied.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value of `E₈(γ_*)`. -/
theorem E8_gammaStar :
    E8 (gammaStar : ℝ) = 4045450969326735650631 / 11468800000000000000000 := by
  rw [gammaStar_cast, E8_eq]
  norm_num

/-- The exact value of `E₈(κ_* γ_*)`. -/
theorem E8_kappaStar_mul_gammaStar :
    E8 ((kappaStar : ℝ) * gammaStar) =
      1795318739900437013458321431 / 26702880859375000000000000000 := by
  rw [gammaStar_cast, kappaStar_def, E8_eq]
  norm_num

/-- `E₈(γ_*)` is positive. -/
theorem E8_gammaStar_pos : 0 < E8 (gammaStar : ℝ) := by
  rw [E8_gammaStar]; norm_num

/-- `E₈(κ_* γ_*)` is positive. -/
theorem E8_kappaStar_mul_gammaStar_pos : 0 < E8 ((kappaStar : ℝ) * gammaStar) := by
  rw [E8_kappaStar_mul_gammaStar]; norm_num

/-- The eighth-order defect is positive at both trace tilts: `min (E₈(γ_*), E₈(κ_* γ_*)) > 0`. -/
@[collatz_pos_dens "lem_tr_E8_pos"]
theorem min_E8_gammaStar_pos :
    0 < min (E8 (gammaStar : ℝ)) (E8 ((kappaStar : ℝ) * gammaStar)) :=
  lt_min E8_gammaStar_pos E8_kappaStar_mul_gammaStar_pos

end CollatzPosDens
