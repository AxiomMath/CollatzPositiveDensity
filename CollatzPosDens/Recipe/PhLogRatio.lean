/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.Transfer.S02AtanhBounds

/-!
# A fifteen-digit enclosure of `log 𝗀`

The physical growth ratio is `𝗀 = 101/100`, for which `(𝗀 - 1)/(𝗀 + 1) = 1/201`. The inverse
hyperbolic tangent enclosure of the logarithm at `y = 𝗀` with `3` terms gives the rationals
$$\ell^{\mathrm{lo}} = 2\Bigl(\frac1{201}+\frac1{3\cdot201^3}+\frac1{5\cdot201^5}\Bigr)
= 0.0099503308531680612922\ldots,
\qquad \ell^{\mathrm{hi}} = \ell^{\mathrm{lo}} + \frac{2\cdot 201^{-7}}{7\,(1-201^{-2})}
= 0.0099503308531680828483\ldots$$
with $\ell^{\mathrm{lo}} \le \log \mathsf g \le \ell^{\mathrm{hi}}$, whence
$$\frac{9950330853168}{10^{15}} < \log \mathsf g < \frac{9950330853169}{10^{15}}.$$

## Main results

* `CollatzPosDens.log_growthRatio_mem_Ioo`:
  `9950330853168 / 10^15 < log 𝗀 < 9950330853169 / 10^15`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Enclosure of `log 𝗀`.**
`9950330853168 / 10^15 < log 𝗀 < 9950330853169 / 10^15` for the growth ratio `𝗀 = 101/100`. -/
@[collatz_pos_dens "lem_ph_log_ratio"]
theorem log_growthRatio_mem_Ioo :
    (9950330853168 / 10 ^ 15 : ℝ) < log (growthRatio : ℝ) ∧
      log (growthRatio : ℝ) < 9950330853169 / 10 ^ 15 := by
  obtain ⟨h1, h2⟩ := log_mem_atanh_partialSum one_lt_growthRatio_cast.le 3
  rw [growthRatio_cast] at h1 h2 ⊢
  norm_num [Finset.sum_range_succ] at h1 h2
  constructor <;> linarith

end CollatzPosDens
