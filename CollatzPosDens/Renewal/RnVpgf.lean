/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.Renewal.RnHold
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The vertical generating function of a hold

For real `y > 0`, the vertical generating function of the holding-time law `η` is
`𝖵(y) = ∑_{(j, l) ∈ 𝒫} η(j, l) y^l ∈ [0, ∞]`, a series of nonnegative terms over the lattice point
set `𝒫 = ℤ_{≥1} × ℤ`, which may diverge.

## Main definitions

* `CollatzPosDens.holdVpgf y`: the vertical generating function `𝖵(y)`, valued in `[0, ∞]`.

## Main results

* `CollatzPosDens.holdVpgf_def`: the defining sum.
* `CollatzPosDens.holdVpgf_eq_tsum_succ`: the same sum in the parametrization
  `(m, l) ↦ (m + 1, l)` of `𝒫` by `ℕ × ℤ`; `CollatzPosDens.holdVpgf_eq_tsum_natPoints`: over
  the pairs `(j, l) : ℕ × ℤ` with `1 ≤ j`.
* `CollatzPosDens.holdVpgf_eq_ofReal_of_hasSum`: if the real series converges to `s`, then
  `𝖵(y) = s`.
* `CollatzPosDens.holdVpgf_ne_top_iff`: for `y ≥ 0`, `𝖵(y) ≠ ∞` iff the real series is
  summable.

## Implementation notes

The value `𝖵(y) ∈ [0, ∞]` is the `ENNReal`-valued sum of the terms `η(j, l) y^l`, each embedded
by `ENNReal.ofReal`. For `y > 0` these terms are nonnegative, so the embedding is faithful; the
definition is made for all real `y`, and only its values at `y > 0` carry meaning. The power
`y^l` with `l ∈ ℤ` is the integer power. A point `p ∈ 𝒫 ⊆ ℤ × ℤ` is evaluated as
`η(p.1.toNat, p.2)`, which is faithful since `p.1 ≥ 1`.

## References

* [Mazur, *Collatz positive density*], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The vertical generating function of a hold, `𝖵(y) = ∑_{(j, l) ∈ 𝒫} η(j, l) y^l ∈ [0, ∞]`. -/
@[collatz_pos_dens "def_rn_vpgf"]
noncomputable def holdVpgf (y : ℝ) : ℝ≥0∞ :=
  ∑' p : bkPoints, ENNReal.ofReal (holdLaw p.1.1.toNat p.1.2 * y ^ p.1.2)

/-- `𝖵(y)` is the sum over `p ∈ 𝒫` of `ENNReal.ofReal (η(p.1.toNat, p.2) * y ^ p.2)`. -/
theorem holdVpgf_def (y : ℝ) :
    holdVpgf y = ∑' p : bkPoints, ENNReal.ofReal (holdLaw p.1.1.toNat p.1.2 * y ^ p.1.2) :=
  rfl

/-- The terms of `𝖵(y)` are nonnegative for `y ≥ 0`. -/
theorem holdVpgf_term_nonneg {y : ℝ} (hy : 0 ≤ y) (j : ℕ) (l : ℤ) :
    0 ≤ holdLaw j l * y ^ l :=
  mul_nonneg (holdLaw_nonneg j l) (zpow_nonneg hy l)

/-- `𝖵(y)` in the parametrization `(m, l) ↦ (m + 1, l)` of `𝒫` by `ℕ × ℤ`. -/
theorem holdVpgf_eq_tsum_succ (y : ℝ) :
    holdVpgf y = ∑' x : ℕ × ℤ, ENNReal.ofReal (holdLaw (x.1 + 1) x.2 * y ^ x.2) := by
  rw [holdVpgf_def, ← bkPointsEquiv.tsum_eq]
  rfl

/-- `𝖵(y)` as a sum over the pairs `(j, l) : ℕ × ℤ` with `1 ≤ j`. -/
theorem holdVpgf_eq_tsum_natPoints (y : ℝ) :
    holdVpgf y =
      ∑' p : {p : ℕ × ℤ // 1 ≤ p.1}, ENNReal.ofReal (holdLaw p.1.1 p.1.2 * y ^ p.1.2) := by
  rw [holdVpgf_eq_tsum_succ, ← natPointsEquiv.tsum_eq]
  rfl

/-- If the real series `∑_{p ∈ 𝒫} η(p) y^{l(p)}` converges to `s` (with `y ≥ 0`), then
`𝖵(y) = s`. -/
theorem holdVpgf_eq_ofReal_of_hasSum {y s : ℝ} (hy : 0 ≤ y)
    (h : HasSum (fun p : bkPoints ↦ holdLaw p.1.1.toNat p.1.2 * y ^ p.1.2) s) :
    holdVpgf y = ENNReal.ofReal s := by
  rw [holdVpgf_def, ← h.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun p ↦ holdVpgf_term_nonneg hy _ _) h.summable]

/-- For `y ≥ 0`, `𝖵(y)` is finite iff the real series `∑_{p ∈ 𝒫} η(p) y^{l(p)}` is summable. -/
theorem holdVpgf_ne_top_iff {y : ℝ} (hy : 0 ≤ y) :
    holdVpgf y ≠ ∞ ↔
      Summable (fun p : bkPoints ↦ holdLaw p.1.1.toNat p.1.2 * y ^ p.1.2) := by
  rw [holdVpgf_def]
  simp only [ENNReal.ofReal]
  rw [ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact summable_congr fun p ↦ Real.coe_toNNReal _ (holdVpgf_term_nonneg hy _ _)

end CollatzPosDens
