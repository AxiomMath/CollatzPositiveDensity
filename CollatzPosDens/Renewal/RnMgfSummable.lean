/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnMgf

/-!
# Convergence of the exponential moment `M₄₅`

For real `t` with `11 e^t < 16`, the series `∑_{r ≥ 1} ν₄₅(r) e^{t r}` defining `M₄₅(t)`
converges. Indeed `ν₄₅(r) e^{t r} = (5 e^t / 16) (11 e^t / 16)^(r-1)` for `r ≥ 1`, the terms of a
geometric series with ratio `0 < 11 e^t / 16 < 1`; its sum is `5 e^t / (16 - 11 e^t)`.

## Main results

* `CollatzPosDens.nu45_natCast_add_one_mul_exp`: the `r`-th term is geometric.
* `CollatzPosDens.hasSum_nu45_mul_exp`: the real series sums to `5 e^t / (16 - 11 e^t)`.
* `CollatzPosDens.summable_nu45_mul_exp`: the real series `∑_{r ≥ 1} ν₄₅(r) e^{t r}` is
  summable.
* `CollatzPosDens.mgfNu45_ne_top`: the extended-real value `M₄₅(t)` is finite.
* `CollatzPosDens.mgfNu45_eq_ofReal`: `M₄₅(t) = 5 e^t / (16 - 11 e^t)`.

## Implementation notes

Since `M₄₅` is defined as a sum in `ℝ≥0∞`, "the series converges" is recorded both as
summability of the real series and as finiteness of `M₄₅(t)`. The index `r ≥ 1` is written
`r + 1` with `r : ℕ`, as in the definition of `M₄₅`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

/-- The `(r+1)`-st term of `M₄₅(t)` is geometric with ratio `11 e^t / 16`. -/
lemma nu45_natCast_add_one_mul_exp (t : ℝ) (r : ℕ) :
    nu45 ((r : ℤ) + 1) * exp (t * ((r : ℝ) + 1)) = 5 * exp t / 16 * (11 / 16 * exp t) ^ r := by
  rw [nu45_natCast_add_one, mul_pow, mul_add_one, exp_add, mul_comm t, exp_nat_mul]
  ring

/-- For `11 e^t < 16`, `∑_{r ≥ 1} ν₄₅(r) e^{t r} = 5 e^t / (16 - 11 e^t)`. -/
lemma hasSum_nu45_mul_exp {t : ℝ} (ht : 11 * exp t < 16) :
    HasSum (fun r : ℕ ↦ nu45 ((r : ℤ) + 1) * exp (t * ((r : ℝ) + 1)))
      (5 * exp t / (16 - 11 * exp t)) := by
  simp_rw [nu45_natCast_add_one_mul_exp]
  have h0 : 0 ≤ 11 / 16 * exp t := by positivity
  have h1 : 11 / 16 * exp t < 1 := by linarith
  convert (hasSum_geometric_of_lt_one h0 h1).mul_left (5 * exp t / 16) using 1
  have : (16 : ℝ) - 11 * exp t ≠ 0 := by linarith
  have : (1 : ℝ) - 11 / 16 * exp t ≠ 0 := by linarith
  field_simp

/-- For `11 e^t < 16`, the series `∑_{r ≥ 1} ν₄₅(r) e^{t r}` defining `M₄₅(t)` converges. -/
@[collatz_pos_dens "lem_rn_mgf_summable"]
theorem summable_nu45_mul_exp {t : ℝ} (ht : 11 * exp t < 16) :
    Summable (fun r : ℕ ↦ nu45 ((r : ℤ) + 1) * exp (t * ((r : ℝ) + 1))) :=
  (hasSum_nu45_mul_exp ht).summable

/-- For `11 e^t < 16`, `M₄₅(t) = 5 e^t / (16 - 11 e^t)`. -/
lemma mgfNu45_eq_ofReal {t : ℝ} (ht : 11 * exp t < 16) :
    mgfNu45 t = ENNReal.ofReal (5 * exp t / (16 - 11 * exp t)) := by
  rw [mgfNu45_def, ← ENNReal.ofReal_tsum_of_nonneg
    (fun r ↦ mul_nonneg (nu45_nonneg _) (exp_pos _).le) (summable_nu45_mul_exp ht),
    (hasSum_nu45_mul_exp ht).tsum_eq]

/-- For `11 e^t < 16`, the exponential moment `M₄₅(t)` is finite. -/
@[collatz_pos_dens "lem_rn_mgf_summable"]
theorem mgfNu45_ne_top {t : ℝ} (ht : 11 * exp t < 16) : mgfNu45 t ≠ ∞ := by
  rw [mgfNu45_eq_ofReal ht]
  exact ENNReal.ofReal_ne_top

end CollatzPosDens
