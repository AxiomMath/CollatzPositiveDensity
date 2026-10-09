/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.Tstar
public import CollatzPosDens.Transfer.RecipeMap
public import CollatzPosDens.Transfer.K
public import CollatzPosDens.Transfer.HDef
public import CollatzPosDens.Transfer.Pinit
public import CollatzPosDens.Transfer.Schedule
public import CollatzPosDens.Transfer.Plateau

/-!
# The bit size of the final time `P_*`

Since `β_*(p_i) = K_*(p_i + 1)` for `0 ≤ i ≤ r_*` (`CollatzPosDens.betaStar_schedule`), for
`0 ≤ i < r_* = 580` the shifted schedule positions `y_i = p_i + 1` obey the integer recurrence
$$y_{i+1} = y_i + \lceil 4 K_* y_i / 35 \rceil + 8294, \qquad y_0 = p_{\mathrm{init}} + 1 = 1025,$$
with `K_* = 9863028149`. Hence `P_* = p_{r_*} + 1 = y_{580}` is the `580`-th iterate of an
explicit computable map on `ℕ` started at `1025`. Evaluating this iterate shows that `P_*` has
binary length `17451`; in particular `2^{17450} ≤ P_*`.

## Main definitions

* `CollatzPosDens.scheduleStep`: the step `y ↦ y + ⌈4 K_* y / 35⌉ + 8294` of the
  shifted schedule.

## Main results

* `CollatzPosDens.schedule_succ_eq_scheduleStep_iterate`: `p_i + 1 = y_i` for `i ≤ r_*`.
* `CollatzPosDens.pStar_eq_scheduleStep_iterate`: `P_* = y_{580}`.
* `CollatzPosDens.two_pow_le_pStar`: `2^{17450} ≤ P_*`.
* `CollatzPosDens.pStar_lt_two_pow`: `P_* < 2^{17451}`.

## Implementation notes

The real ceiling in the window length is replaced by the natural-number ceiling division
`(4 K_* y + 34) / 35`, so that `y_{580}` is a closed computable natural number; the two
numerical comparisons with powers of two are then checked by kernel evaluation of natural-number
arithmetic on literals.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The step `y ↦ y + ⌈4 K_* y / 35⌉ + 8294` of the shifted schedule `y_i = p_i + 1`, with the
ceiling written as natural-number ceiling division. -/
def scheduleStep (y : ℕ) : ℕ := y + (4 * 9863028149 * y + 34) / 35 + 8294

/-- For `i ≤ r_*`, the shifted schedule `p_i + 1` is the `i`-th iterate of `scheduleStep`
started at `1025`. -/
theorem schedule_succ_eq_scheduleStep_iterate {i : ℕ} (hi : i ≤ rStar) :
    schedule i + 1 = scheduleStep^[i] 1025 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ← ih (by omega), schedule_succ, recipeMap_eq,
      windowLength_eq_div, betaStar_schedule (by omega : i ≤ rStar), scheduleStep, Kstar_eq]
    rw [← mul_assoc]
    generalize (4 * 9863028149 * (schedule i + 1) + 34) / 35 = c
    omega

/-- `P_*` is the `580`-th iterate of `scheduleStep` started at `1025`. -/
theorem pStar_eq_scheduleStep_iterate : pStar = scheduleStep^[580] 1025 := by
  rw [pStar_def, schedule_succ_eq_scheduleStep_iterate le_rfl, rStar_def]

/-- **Bit size of `P_*`.** `2^{17450} ≤ P_*`. -/
@[collatz_pos_dens "lem_s02_P_bits"]
theorem two_pow_le_pStar : 2 ^ 17450 ≤ pStar := by
  rw [pStar_eq_scheduleStep_iterate]
  decide +kernel

/-- **Upper bound on `P_*`.** `P_* < 2^{17451}`, so `P_*` has binary length exactly `17451`. -/
@[collatz_pos_dens "lem_s02_P_upper"]
theorem pStar_lt_two_pow : pStar < 2 ^ 17451 := by
  rw [pStar_eq_scheduleStep_iterate]
  decide +kernel

end CollatzPosDens
