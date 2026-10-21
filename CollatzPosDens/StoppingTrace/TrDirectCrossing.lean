/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.StoppingTrace.TrRepCoeff
public import CollatzPosDens.BlackSet.BkExitWidth

/-!
# The broad first-crossing decrement

For `s ∈ ℕ`, the broad first-crossing decrement is
`D_cr(s) := ∑_{c=3}^{16} ϖ(c) ∑_{o=1}^{c} δ^{rep}_{s,c,o} ∑_{r=1}^{f_s} 𝖱(r - 1, s + o - c)`,
where `ϖ` is the Pascal holding-time weight `varpi`, `δ^{rep}_{s,c,o}` the replaced crossing
coefficient `trRepCoeff`, `𝖱` the raw-prefix mass `rawMass` and `f_s` the exit width
`bkExitWidth`.

## Main definitions

* `CollatzPosDens.trDirectCrossing s`: the broad first-crossing decrement `D_cr(s)`.

## Main results

* `CollatzPosDens.trDirectCrossing_eq_sum_sum_sum`: `D_cr(s)` as a single triple sum of the
  products `δ^{rep}_{s,c,o} ϖ(c) 𝖱(r - 1, s + o - c)`.
* `CollatzPosDens.trDirectCrossing_nonneg`: `0 ≤ D_cr(s)`.

## Implementation notes

The second argument `s + o - c` of `𝖱` is formed in `ℤ`, where it may be negative. The replaced
crossing coefficient takes values in `ℚ` and is cast to `ℝ`.

## References

* [Mazur, *Collatz positive density*], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The broad first-crossing decrement
`D_cr(s) = ∑_{c=3}^{16} ϖ(c) ∑_{o=1}^{c} δ^{rep}_{s,c,o} ∑_{r=1}^{f_s} 𝖱(r - 1, s + o - c)`. -/
@[collatz_pos_dens "def_tr_direct_crossing"]
noncomputable def trDirectCrossing (s : ℕ) : ℝ :=
  ∑ c ∈ Icc (3 : ℕ) 16, varpi c * ∑ o ∈ Icc 1 c, (trRepCoeff s c o : ℝ) *
    ∑ r ∈ Icc 1 (bkExitWidth s), rawMass (r - 1) ((s : ℤ) + o - c)

/-- The defining formula of `trDirectCrossing s`. -/
theorem trDirectCrossing_def (s : ℕ) :
    trDirectCrossing s = ∑ c ∈ Icc (3 : ℕ) 16, varpi c * ∑ o ∈ Icc 1 c, (trRepCoeff s c o : ℝ) *
      ∑ r ∈ Icc 1 (bkExitWidth s), rawMass (r - 1) ((s : ℤ) + o - c) := rfl

/-- `D_cr(s)` as a triple sum over `3 ≤ c ≤ 16`, `1 ≤ o ≤ c`, `1 ≤ r ≤ f_s` of
`δ^{rep}_{s,c,o} ϖ(c) 𝖱(r - 1, s + o - c)`. -/
theorem trDirectCrossing_eq_sum_sum_sum (s : ℕ) :
    trDirectCrossing s = ∑ c ∈ Icc (3 : ℕ) 16, ∑ o ∈ Icc 1 c, ∑ r ∈ Icc 1 (bkExitWidth s),
      (trRepCoeff s c o : ℝ) * varpi c * rawMass (r - 1) ((s : ℤ) + o - c) := by
  simp only [trDirectCrossing, mul_sum]
  refine sum_congr rfl fun c _ ↦ sum_congr rfl fun o _ ↦ sum_congr rfl fun r _ ↦ ?_
  ring

/-- The broad first-crossing decrement is nonnegative. -/
theorem trDirectCrossing_nonneg (s : ℕ) : 0 ≤ trDirectCrossing s := by
  rw [trDirectCrossing_eq_sum_sum_sum]
  refine sum_nonneg fun c _ ↦ sum_nonneg fun o _ ↦ sum_nonneg fun r _ ↦ ?_
  have := trRepCoeff_nonneg s c o
  exact mul_nonneg (mul_nonneg (by exact_mod_cast this) (varpi_nonneg _)) (rawMass_nonneg _ _)

end CollatzPosDens
