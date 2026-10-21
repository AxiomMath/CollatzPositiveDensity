/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnMgf
public import CollatzPosDens.Renewal.RnMgfSummable

/-!
# Value of the exponential moment `mgfNu45`

For real `t` with `11 e^t < 16`, the exponential moment `mgfNu45 t` of the horizontal law `nu45`
equals `5 e^t / (16 - 11 e^t)`. Indeed `nu45 r * e^{t r} = (5 e^t / 16) (11 e^t / 16)^(r-1)` for
`r ≥ 1`, a geometric series with ratio `0 < 11 e^t / 16 < 1` whose sum is
`(5 e^t / 16) / (1 - 11 e^t / 16) = 5 e^t / (16 - 11 e^t)`.

## Main results

* `CollatzPosDens.mgfNu45_eq_div`: `mgfNu45 t = 5 e^t / (16 - 11 e^t)` in `ℝ≥0∞`.

## Implementation notes

`mgfNu45` takes values in `[0, ∞] = ℝ≥0∞`, so the closed form is stated as
`mgfNu45 t = ENNReal.ofReal (5 e^t / (16 - 11 e^t))`; the right-hand side is positive under the
hypothesis, so no information is lost by the embedding.
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

/-- For real `t` with `11 e^t < 16`, `mgfNu45 t = 5 e^t / (16 - 11 e^t)`. -/
@[collatz_pos_dens "lem_rn_mgf_finite"]
theorem mgfNu45_eq_div {t : ℝ} (ht : 11 * exp t < 16) :
    mgfNu45 t = ENNReal.ofReal (5 * exp t / (16 - 11 * exp t)) := by
  rw [mgfNu45_def, ← ENNReal.ofReal_tsum_of_nonneg
    (fun r ↦ mul_nonneg (nu45_nonneg _) (exp_pos _).le) (summable_nu45_mul_exp ht),
    (hasSum_nu45_mul_exp ht).tsum_eq]

end CollatzPosDens
