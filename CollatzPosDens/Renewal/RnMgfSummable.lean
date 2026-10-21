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

## Implementation notes

Since `M₄₅` is defined as a sum in `ℝ≥0∞` of the embedded real terms, "the series converges"
is recorded as summability of the real series. The index `r ≥ 1` is written
`r + 1` with `r : ℕ`, as in the definition of `M₄₅`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.3.
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
  convert (hasSum_geometric_of_lt_one (r := 11 / 16 * exp t) (by positivity)
    (by linarith)).mul_left (5 * exp t / 16) using 1
  have : (16 : ℝ) - 11 * exp t ≠ 0 := by linarith
  have : (1 : ℝ) - 11 / 16 * exp t ≠ 0 := by linarith
  field_simp

/-- For `11 e^t < 16`, the series `∑_{r ≥ 1} ν₄₅(r) e^{t r}` defining `M₄₅(t)` converges. -/
@[collatz_pos_dens "lem_rn_mgf_summable"]
theorem summable_nu45_mul_exp {t : ℝ} (ht : 11 * exp t < 16) :
    Summable (fun r : ℕ ↦ nu45 ((r : ℤ) + 1) * exp (t * ((r : ℝ) + 1))) :=
  (hasSum_nu45_mul_exp ht).summable

end CollatzPosDens
