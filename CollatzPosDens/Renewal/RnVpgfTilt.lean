/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnVpgf
public import CollatzPosDens.Renewal.RnHoldVpgf

/-!
# The vertical generating function of a hold at `27/25`

At the tilt `y = 27/25` the vertical generating function of the holding-time law is finite and
explicit: `y² / (2 - y)² = 729/529` and `(3/16) y⁴ + (1/8) y⁵ = 68555889/156250000`, so the
non-closing weight `y² / (2 - y)² - (3/16) y⁴ - (1/8) y⁵ = 77640184719/82656250000` is below `1`,
and the closed form of `𝖵` gives `𝖵(27/25) = 36266065281/5016065281 < 8`.

## Main results

* `CollatzPosDens.holdVpgf_tilt_eq`: `𝖵(27/25) = 36266065281/5016065281`.
* `CollatzPosDens.holdVpgf_tilt_lt`: `𝖵(27/25) < 8`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The exact value `𝖵(27/25) = 36266065281/5016065281`. -/
theorem holdVpgf_tilt_eq :
    holdVpgf (27 / 25) = ENNReal.ofReal (36266065281 / 5016065281) := by
  rw [holdVpgf_eq (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- **The vertical generating function at the tilt.** `𝖵(27/25) < 8`. -/
@[collatz_pos_dens "lem_rn_vpgf_tilt"]
theorem holdVpgf_tilt_lt : holdVpgf (27 / 25) < 8 := by
  rw [holdVpgf_tilt_eq, show (8 : ℝ≥0∞) = ENNReal.ofReal 8 by norm_num,
    ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
  norm_num

end CollatzPosDens
