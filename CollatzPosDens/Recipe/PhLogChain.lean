/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MxChainRatio
public import CollatzPosDens.Transfer.S02AtanhBounds

/-!
# An enclosure of `log bootChainRatio`

Write $c = 1079/1000$ for `bootChainRatio`, so that $(c - 1)/(c + 1) = 79/2079$. The partial sum
with `6` terms of the inverse hyperbolic tangent series for the logarithm at $c$
(`log_mem_atanh_partialSum`) gives the rationals
$$\ell^{\mathrm{lo}} = 2\sum_{j=0}^{5}\frac{(79/2079)^{2j+1}}{2j+1}
= 0.076034686275997607421\ldots,
\qquad \ell^{\mathrm{hi}} = \ell^{\mathrm{lo}} + \frac{2\,(79/2079)^{13}}{13\,(1-(79/2079)^2)}
= 0.076034686275997607474\ldots$$
with $\ell^{\mathrm{lo}} \le \log c \le \ell^{\mathrm{hi}}$, whence
$$\frac{76034686275}{10^{12}} < \log c < \frac{76034686276}{10^{12}}.$$

## Main results

* `CollatzPosDens.log_bootChainRatio_mem_Ioo`:
  `76034686275 / 10^12 < log bootChainRatio < 76034686276 / 10^12`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- `76034686275 / 10^12 < log bootChainRatio < 76034686276 / 10^12`, where
`bootChainRatio = 1079/1000`. -/
@[collatz_pos_dens "lem_ph_log_chain"]
theorem log_bootChainRatio_mem_Ioo :
    (76034686275 / 10 ^ 12 : ℝ) < log (bootChainRatio : ℝ) ∧
      log (bootChainRatio : ℝ) < 76034686276 / 10 ^ 12 := by
  have hy : (1 : ℝ) ≤ bootChainRatio := by rw [bootChainRatio_cast]; norm_num
  obtain ⟨h1, h2⟩ := log_mem_atanh_partialSum hy 6
  rw [bootChainRatio_cast] at h1 h2 ⊢
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

end CollatzPosDens
