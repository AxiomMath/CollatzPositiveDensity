/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The chain ratio bound

The numerical fact
$$\Bigl(\frac{90000}{99999}\Bigr)^{9/8} < \frac{159}{179}.$$
Both sides are positive and `t ↦ t^8` is strictly increasing on `[0, ∞)`, so the claim is
equivalent to `(90000/99999)^9 < (159/179)^8`, i.e. to the integer inequality
`90000^9 · 179^8 < 159^8 · 99999^9`, which is checked by evaluation.

## Main results

* `CollatzPosDens.mxChainRatio_lt`: `(90000/99999)^(9/8) < 159/179` in `ℝ`, with the
  exponent a real power.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The real power `(90000/99999)^(9/8)` is less than `159/179`. -/
@[collatz_pos_dens "lem_mx_chain_ratio"]
theorem mxChainRatio_lt : ((90000 : ℝ) / 99999) ^ ((9 : ℝ) / 8) < 159 / 179 := by
  have hx : (0 : ℝ) ≤ 90000 / 99999 := by norm_num
  refine lt_of_pow_lt_pow_left₀ 8 (by norm_num) ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

end CollatzPosDens
