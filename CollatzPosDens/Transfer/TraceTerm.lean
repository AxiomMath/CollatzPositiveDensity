/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.PT
public import CollatzPosDens.Transfer.B12
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.RhoUnit
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The even score pays the trace reserve

We prove `exp (101 γ_*) ϱ_*^290 < 1 / P_T`, where `γ_*` is the trace tilt, `ϱ_*` the
two-passage rate and `P_T = ∑_{j ≤ 50} L_*^j / j!` the trace Taylor sum.

The argument has three steps. First, writing `x = 1 - ϱ_* ∈ (0, 1)`, the series
`-log ϱ_* = ∑_{j ≥ 1} x^j / j` has positive terms, so its twelfth partial sum `b_*` satisfies
`b_* ≤ -log ϱ_*`, i.e. `ϱ_* ≤ exp (-b_*)`. Second, exact rational arithmetic gives
`101 γ_* + L_* < 290 b_*`. Third, `P_T ≤ exp L_*` because `P_T` is a partial sum of the
exponential series with nonnegative terms. Combining,
`exp (101 γ_*) ϱ_*^290 ≤ exp (101 γ_* - 290 b_*) < exp (-L_*) ≤ 1 / P_T`.

## Main results

* `CollatzPosDens.rhoStar_le_exp_neg_bStar`: `ϱ_* ≤ exp (-b_*)`.
* `CollatzPosDens.gammaStar_add_Lstar_lt_bStar`: `101 γ_* + L_* < 290 b_*`.
* `CollatzPosDens.exp_gammaStar_mul_rhoStar_pow_lt`: `exp (101 γ_*) ϱ_*^290 < 1 / P_T`.

## Implementation notes

[mazur2026] proves the strict inequality `ϱ_* < exp (-b_*)` in the first step and the non-strict
`101 γ_* + L_* ≤ 290 b_*` in the second; here the first step is non-strict and the strictness is
taken from the second, where the slack `290 b_* - 101 γ_* - L_* ≈ 2.95 · 10⁻⁷` is positive.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The two-passage rate is at most `exp (-b_*)`: the pair score `b_*` is a partial sum of the
positive series for `-log ϱ_*`. -/
theorem rhoStar_le_exp_neg_bStar : (rhoStar : ℝ) ≤ Real.exp (-(bStar : ℝ)) := by
  obtain ⟨h0, h1⟩ := rhoStar_pos_and_lt_one_cast (K := ℝ)
  set x : ℝ := 1 - rhoStar with hx
  have hx0 : 0 < x := sub_pos.mpr h1
  have hx1 : |x| < 1 := (abs_of_pos hx0).trans_lt (by linarith)
  have hb : (bStar : ℝ) ≤ -Real.log (1 - x) := by
    have : (bStar : ℝ) = ∑ i ∈ Finset.range 12, x ^ (i + 1) / (i + 1) := by
      rw [bStar_eq_sum_range]
      push_cast
      rfl
    rw [this]
    exact sum_le_hasSum _ (fun i _ => by positivity) (Real.hasSum_pow_div_log_of_abs_lt_one hx1)
  rw [hx, sub_sub_cancel] at hb
  exact (Real.log_le_iff_le_exp h0).mp (by linarith)

/-- The exact numerical comparison `101 γ_* + L_* < 290 b_*`. -/
theorem gammaStar_add_Lstar_lt_bStar : 101 * gammaStar + Lstar < 290 * bStar := by
  rw [bStar_def, gammaStar_eq, Lstar_eq, rhoStar_eq]
  simp only [Finset.sum_Icc_succ_top, Finset.Icc_self, Finset.sum_singleton, Nat.reduceLeDiff]
  norm_num

/-- **The even score pays the trace reserve**: `exp (101 γ_*) ϱ_*^290 < 1 / P_T`. -/
@[collatz_pos_dens "lem_s02_trace_term"]
theorem exp_gammaStar_mul_rhoStar_pow_lt :
    Real.exp (101 * gammaStar) * (rhoStar : ℝ) ^ 290 < 1 / (PT : ℝ) := by
  have h0 : (0 : ℝ) ≤ rhoStar := (rhoStar_pos_and_lt_one_cast (K := ℝ)).1.le
  have hnum : (101 * gammaStar + Lstar : ℝ) < 290 * bStar := by
    exact_mod_cast gammaStar_add_Lstar_lt_bStar
  calc Real.exp (101 * gammaStar) * (rhoStar : ℝ) ^ 290
      ≤ Real.exp (101 * gammaStar) * Real.exp (-(bStar : ℝ)) ^ 290 := by
        gcongr
        exact rhoStar_le_exp_neg_bStar
    _ = Real.exp (101 * gammaStar - 290 * bStar) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        ring_nf
    _ < Real.exp (-Lstar) := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 / Real.exp Lstar := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (PT : ℝ) := one_div_le_one_div_of_le (by exact_mod_cast PT_pos) PT_le_exp

end CollatzPosDens
