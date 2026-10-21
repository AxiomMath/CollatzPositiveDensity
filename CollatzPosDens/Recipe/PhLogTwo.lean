/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02AtanhBounds

/-!
# A fifteen-digit enclosure of `log 2`

The inverse hyperbolic tangent enclosure `CollatzPosDens.log_mem_atanh_partialSum` of the
logarithm at `y = 2`, where `(y - 1)/(y + 1) = 1/3`, with `15` terms gives the rationals
$$\ell^{\mathrm{lo}} = 2\sum_{j=0}^{14}\frac{3^{-(2j+1)}}{2j+1} = 0.69314718055994519278\ldots,
\qquad \ell^{\mathrm{hi}} = \ell^{\mathrm{lo}} + \frac{2\cdot 3^{-31}}{31\,(1-\frac19)}
= 0.69314718055994531029\ldots$$
with $\ell^{\mathrm{lo}} \le \log 2 \le \ell^{\mathrm{hi}}$, whence
$$\frac{693147180559945}{10^{15}} < \log 2 < \frac{693147180559946}{10^{15}}.$$
Mathlib's `Real.log_two_gt_d9` and `Real.log_two_lt_d9` give only nine digits.

## Main results

* `CollatzPosDens.log_two_mem_Ioo_d15`:
  `693147180559945 / 10^15 < log 2 < 693147180559946 / 10^15`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Enclosure of `log 2`.** `693147180559945 / 10^15 < log 2 < 693147180559946 / 10^15`. -/
@[collatz_pos_dens "lem_ph_log_two"]
theorem log_two_mem_Ioo_d15 :
    (693147180559945 / 10 ^ 15 : ℝ) < log 2 ∧ log 2 < 693147180559946 / 10 ^ 15 := by
  obtain ⟨h1, h2⟩ := log_mem_atanh_partialSum (y := (2 : ℝ)) (by norm_num) 15
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

end CollatzPosDens
