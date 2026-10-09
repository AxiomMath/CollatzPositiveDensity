/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnP3
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.StoppingTrace.TrE8
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.Transfer.D

/-!
# The passage surplus vanishes at gap zero

The passage surplus `δ_tr(s) = E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s) - d_*` vanishes at `s = 0`.
Indeed, for `s = 0` the length bound `⌊16/16⌋ = 1` admits only `r = 1`, and
`𝖱(0, t) = [t = 0]` (the empty word). Hence only `c = O = 4` contributes to `p₄₅(0)`, giving
`p₄₅(0) = ϖ(4) = 3/16`, and only `O = 3` contributes to `p₃(0)`, giving `p₃(0) = ϖ(3) = 1/4`.
So `δ_tr(0) = (3/16) E₈(γ_*) + (1/4) E₈(κ_* γ_*) - d_* = 0` by the definition of `d_*`.

## Main results

* `CollatzPosDens.trDelta_zero`: `δ_tr(0) = 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- At gap zero the closing exit mass is `p₄₅(0) = ϖ(4) = 3/16`. -/
private theorem trDelta_zero_p45 : p45 0 = 3 / 16 := by
  simp only [p45]
  rw [show Icc (4 : ℤ) 5 = {4, 5} by decide, show Icc (1 : ℤ) 4 = {1, 2, 3, 4} by decide,
    show Icc 1 ((5 * 0 + 16) / 16) = {1} by decide]
  simp +decide only [sum_insert, mem_insert, mem_singleton, sum_singleton, Nat.sub_self]
  norm_num [varpi_of_two_le, rawMass_zero]

/-- At gap zero the raw-three exit mass is `p₃(0) = ϖ(3) = 1/4`. -/
private theorem trDelta_zero_p3 : p3 0 = 1 / 4 := by
  simp only [p3]
  rw [show Icc (1 : ℕ) 3 = {1, 2, 3} by decide, show Icc 1 ((5 * 0 + 16) / 16) = {1} by decide]
  simp +decide only [sum_insert, mem_insert, mem_singleton, sum_singleton, Nat.sub_self]
  norm_num [varpi_of_two_le, rawMass_zero]

/-- The passage surplus vanishes at gap zero: `δ_tr(0) = 0`. -/
@[collatz_pos_dens "lem_tr_delta_zero"]
theorem trDelta_zero : trDelta 0 = 0 := by
  rw [trDelta, trDelta_zero_p45, trDelta_zero_p3, E8_ratCast, E8_ratCast, dStar_eq,
    gammaStar_eq, kappaStar_def]
  norm_num

end CollatzPosDens
