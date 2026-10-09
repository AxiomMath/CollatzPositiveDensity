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
public import CollatzPosDens.StoppingTrace.TrE8
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa

/-!
# The passage surplus at gap six

The passage surplus `δ_tr(s) = E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s) - d_*` is evaluated exactly at
`s = 6`. Since `⌊(5 · 6 + 16)/16⌋ = 2`, only the raw-prefix masses `𝖱(0, t) = [t = 0]` and
`𝖱(1, t) = binom(t - 1, 1) 2^{-t}` (for `t ≥ 1`, and `0` for `t ≤ 0`) enter, giving
`p₄₅(6) = 227/1024` and `p₃(6) = 25/256`. Substituting `γ_* = 87/200`, `κ_* = 4/25` and the
exact value of `d_*` yields
`δ_tr(6) = 3250389656929039669352283093088629 / 1792000000000000000000000000000000000`.

## Main results

* `CollatzPosDens.trDelta_six_p45`: `p₄₅(6) = 227/1024`.
* `CollatzPosDens.trDelta_six_p3`: `p₃(6) = 25/256`.
* `CollatzPosDens.trDelta_six`: the exact value of `δ_tr(6)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The closing exit mass at gap six: `p₄₅(6) = 227/1024`. -/
theorem trDelta_six_p45 : p45 6 = 227 / 1024 := by
  rw [p45, show (5 * 6 + 16) / 16 = 2 by norm_num]
  simp only [show Icc (4 : ℤ) 5 = {4, 5} by decide, show Icc (1 : ℤ) 4 = {1, 2, 3, 4} by decide,
    show Icc (1 : ℕ) 2 = {1, 2} by decide]
  simp [rawMass_zero, rawMass_one, varpi_of_two_le, zpow_neg]
  norm_num

/-- The raw-three exit mass at gap six: `p₃(6) = 25/256`. -/
theorem trDelta_six_p3 : p3 6 = 25 / 256 := by
  rw [p3, show (5 * 6 + 16) / 16 = 2 by norm_num]
  simp only [show Icc (1 : ℕ) 3 = {1, 2, 3} by decide, show Icc (1 : ℕ) 2 = {1, 2} by decide]
  simp [rawMass_zero, rawMass_one, varpi_of_two_le, zpow_neg]
  norm_num

/-- The passage surplus at gap six:
`δ_tr(6) = 3250389656929039669352283093088629 / 1792000000000000000000000000000000000`. -/
@[collatz_pos_dens "lem_tr_delta_six"]
theorem trDelta_six :
    trDelta 6 = 3250389656929039669352283093088629 / 1792000000000000000000000000000000000 := by
  rw [trDelta, trDelta_six_p45, trDelta_six_p3, E8_ratCast, E8_ratCast, dStar_eq, gammaStar_eq,
    kappaStar_def]
  push_cast
  norm_num

end CollatzPosDens
