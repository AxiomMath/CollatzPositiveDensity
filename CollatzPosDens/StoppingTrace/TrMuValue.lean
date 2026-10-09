/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnP3
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnRawMassFormula
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrDeltaSix
public import CollatzPosDens.StoppingTrace.TrE8
public import CollatzPosDens.StoppingTrace.TrMu
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa

/-!
# The exact value of the adjacent surplus `μ_∘`

The adjacent surplus `μ_∘ = (3/16) δ_tr(6) + (1/8) δ_tr(5)` is evaluated exactly. The value of
`δ_tr(6)` is known. For `δ_tr(5)`, since `⌊(5 · 5 + 16)/16⌋ = ⌊41/16⌋ = 2`, only the raw-prefix
masses `𝖱(0, t) = [t = 0]` and `𝖱(1, t) = binom(t - 1, 1) 2^{-t}` enter, giving
`p₄₅(5) = 61/256` and `p₃(5) = 9/64`. Substituting `γ_* = 87/200`, `κ_* = 4/25` and the exact
value of `d_*` yields
`δ_tr(5) = 4730304540206345078315898630590427 / 448000000000000000000000000000000000`,
and hence
`μ_∘ = 6799086470348268519226291189141329 / 4096000000000000000000000000000000000`.

## Main results

* `CollatzPosDens.trMu_value_p45`: `p₄₅(5) = 61/256`.
* `CollatzPosDens.trMu_value_p3`: `p₃(5) = 9/64`.
* `CollatzPosDens.trMu_value_trDelta_five`: the exact value of `δ_tr(5)`.
* `CollatzPosDens.trMu_value`: the exact value of `μ_∘`.

## References

* [Mazur, *Collatz positive density*], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The closing exit mass at gap five: `p₄₅(5) = 61/256`. -/
theorem trMu_value_p45 : p45 5 = 61 / 256 := by
  rw [p45, show (5 * 5 + 16) / 16 = 2 by norm_num]
  simp only [show Icc (4 : ℤ) 5 = {4, 5} by decide, show Icc (1 : ℤ) 4 = {1, 2, 3, 4} by decide,
    show Icc (1 : ℕ) 2 = {1, 2} by decide]
  simp [rawMass_zero, rawMass_one, varpi_of_two_le, zpow_neg]
  norm_num

/-- The raw-three exit mass at gap five: `p₃(5) = 9/64`. -/
theorem trMu_value_p3 : p3 5 = 9 / 64 := by
  rw [p3, show (5 * 5 + 16) / 16 = 2 by norm_num]
  simp only [show Icc (1 : ℕ) 3 = {1, 2, 3} by decide, show Icc (1 : ℕ) 2 = {1, 2} by decide]
  simp [rawMass_zero, rawMass_one, varpi_of_two_le, zpow_neg]
  norm_num

/-- The passage surplus at gap five:
`δ_tr(5) = 4730304540206345078315898630590427 / 448000000000000000000000000000000000`. -/
theorem trMu_value_trDelta_five :
    trDelta 5 = 4730304540206345078315898630590427 / 448000000000000000000000000000000000 := by
  rw [trDelta, trMu_value_p45, trMu_value_p3, E8_ratCast, E8_ratCast, dStar_eq, gammaStar_eq,
    kappaStar_def]
  push_cast
  norm_num

/-- **The exact value of the adjacent surplus.**
`μ_∘ = 6799086470348268519226291189141329 / 4096000000000000000000000000000000000`. -/
@[collatz_pos_dens "lem_tr_mu_value"]
theorem trMu_value :
    trMu = 6799086470348268519226291189141329 / 4096000000000000000000000000000000000 := by
  rw [trMu_def, trDelta_six, trMu_value_trDelta_five]
  norm_num

/-- The adjacent surplus is positive. -/
theorem trMu_pos : 0 < trMu := by
  rw [trMu_value]
  norm_num

/-- The adjacent surplus is nonnegative. -/
theorem trMu_nonneg : 0 ≤ trMu :=
  trMu_pos.le

end CollatzPosDens
