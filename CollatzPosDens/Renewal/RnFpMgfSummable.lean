/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnFpFinite
public import CollatzPosDens.Renewal.RnFpMgf
public import CollatzPosDens.Renewal.RnMgfSummable

/-!
# Convergence of the horizontal moment of the first-passage law

For a level `s ∈ ℕ` and real `t ≥ 0` with `11 e^t < 16`, the series
`∑_{(r, ℓ) ∈ ℤ²} F_s(r, ℓ) e^{t r}` converges. Its terms are nonnegative reals, and its sum in
`[0, ∞]` is at most `mgfNu45 t ^ (s + 1)`, which is finite because `mgfNu45 t ≠ ∞`. A series of
nonnegative reals with finite sum in `[0, ∞]` is summable.

## Main results

* `CollatzPosDens.summable_firstPassageLaw_mul_exp`: the series
  `∑_{x ∈ ℤ²} F_s(x) e^{t x₁}` is summable.
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

/-- **Convergence of the horizontal moment of the first-passage law.** For `s ∈ ℕ` and real
`t ≥ 0` with `11 e^t < 16`, the series `∑_{(r, ℓ) ∈ ℤ²} F_s(r, ℓ) e^{t r}` converges. -/
@[collatz_pos_dens "lem_rn_fp_mgf_summable"]
theorem summable_firstPassageLaw_mul_exp (s : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht16 : 11 * exp t < 16) :
    Summable fun x : ℤ × ℤ ↦ firstPassageLaw s x * exp (t * x.1) := by
  have hne : ∑' x : ℤ × ℤ, ENNReal.ofReal (firstPassageLaw s x * exp (t * x.1)) ≠ ∞ :=
    ne_top_of_le_ne_top (pow_ne_top (mgfNu45_ne_top ht16))
      (tsum_ofReal_firstPassageLaw_mul_exp_le s ht)
  convert ENNReal.summable_toReal hne using 2 with x
  exact (ENNReal.toReal_ofReal (mul_nonneg (firstPassageLaw_nonneg _ _) (exp_pos _).le)).symm

end CollatzPosDens
