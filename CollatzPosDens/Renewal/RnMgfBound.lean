/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnMgf
public import CollatzPosDens.Renewal.RnMgfFinite

/-!
# An explicit bound on the exponential moment `M₄₅`

For real `t` with `0 ≤ t ≤ 1/1024` we have `M₄₅(t) ≤ e^{13t/4}`. Since `e^{-t} ≥ 1 - t`, one gets
`16 e^{-t} - 11 ≥ 5 - 16t > 0`, so `11 e^t < 16` and the closed form
`M₄₅(t) = 5 e^t / (16 - 11 e^t) = 5 / (16 e^{-t} - 11)` applies. It then suffices to show
`e^{13t/4} (16 e^{-t} - 11) ≥ 5`, and indeed
`e^{13t/4} (16 e^{-t} - 11) ≥ (1 + 13t/4)(5 - 16t) = 5 + t/4 - 52t² ≥ 5`
because `0 ≤ t ≤ 1/208`.

## Main results

* `CollatzPosDens.mgfNu45_le_exp`: `M₄₅(t) ≤ e^{13t/4}` for `0 ≤ t ≤ 1/1024`.

## Implementation notes

`M₄₅` takes values in `ℝ≥0∞`, so the bound is stated as `M₄₅(t) ≤ ofReal (e^{13t/4})`.
Rather than bounding `e^{-13t/4}` from above by its second-order Taylor polynomial, we bound
`e^{13t/4}` from below by `1 + 13t/4`, which gives the conclusion on the stated range of `t`
(in fact on `0 ≤ t ≤ 1/208`) with a one-line polynomial comparison.
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

/-- For real `t` with `0 ≤ t ≤ 1/1024`, `M₄₅(t) ≤ e^{13t/4}`. -/
@[collatz_pos_dens "lem_rn_mgf_bound"]
theorem mgfNu45_le_exp {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1 / 1024) :
    mgfNu45 t ≤ ENNReal.ofReal (exp (13 * t / 4)) := by
  have hu : exp t * exp (-t) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hut : -t + 1 ≤ exp (-t) := add_one_le_exp _
  have hE : 13 * t / 4 + 1 ≤ exp (13 * t / 4) := add_one_le_exp _
  have hpos : 0 < exp t := exp_pos t
  -- `16 e^{-t} - 11 ≥ 5 - 16t > 0`, hence `11 e^t < 16`.
  have hlt : 11 * exp t < 16 := by nlinarith
  rw [mgfNu45_eq_div hlt]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (by linarith)]
  -- Reduce to `5 ≤ e^{13t/4} (16 e^{-t} - 11)` after dividing by `e^t`.
  have key : 5 ≤ exp (13 * t / 4) * (16 * exp (-t) - 11) := by
    have h1 : 5 ≤ (13 * t / 4 + 1) * (5 - 16 * t) := by nlinarith
    have h2 : (13 * t / 4 + 1) * (5 - 16 * t) ≤ exp (13 * t / 4) * (5 - 16 * t) :=
      mul_le_mul_of_nonneg_right hE (by linarith)
    have h3 : exp (13 * t / 4) * (5 - 16 * t) ≤ exp (13 * t / 4) * (16 * exp (-t) - 11) :=
      mul_le_mul_of_nonneg_left (by linarith) (exp_pos _).le
    linarith
  calc 5 * exp t = exp t * 5 := mul_comm _ _
    _ ≤ exp t * (exp (13 * t / 4) * (16 * exp (-t) - 11)) :=
        mul_le_mul_of_nonneg_left key hpos.le
    _ = exp (13 * t / 4) * (16 - 11 * exp t) := by
        linear_combination (16 * exp (13 * t / 4)) * hu

end CollatzPosDens
