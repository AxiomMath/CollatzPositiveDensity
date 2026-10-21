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
# The joint generating function of a hold

For real `X > 0` and `y > 0`, the joint generating function of the holding-time law `η` is
`𝖦(X, y) = ∑_{(j, l) ∈ 𝒫} η(j, l) X^j y^l ∈ [0, ∞]`, a series of nonnegative terms over the
lattice point set `𝒫 = ℤ_{≥1} × ℤ`, which may diverge.

## Main definitions

* `CollatzPosDens.holdJointPgf X y`: the joint generating function `𝖦(X, y)`, valued in
  `[0, ∞]`.

## Main results

* `CollatzPosDens.holdJointPgf_def`: the defining sum.
* `CollatzPosDens.holdJointPgf_eq_tsum_succ`: the same sum in the parametrization
  `(m, l) ↦ (m + 1, l)` of `𝒫` by `ℕ × ℤ`; `CollatzPosDens.holdJointPgf_eq_tsum_natPoints`:
  over the pairs `(j, l) : ℕ × ℤ` with `1 ≤ j`.
* `CollatzPosDens.holdJointPgf_eq_ofReal_of_hasSum`: if the real series converges to `s`, then
  `𝖦(X, y) = s`.
* `CollatzPosDens.holdJointPgf_ne_top_iff`: for `X, y ≥ 0`, `𝖦(X, y) ≠ ∞` iff the real series
  is summable.

## Implementation notes

The value `𝖦(X, y) ∈ [0, ∞]` is the `ENNReal`-valued sum of the terms `η(j, l) X^j y^l`, each
embedded by `ENNReal.ofReal`. For `X, y > 0` these terms are nonnegative, so the embedding is
faithful; the definition is made for all real `X` and `y`, and only its values at `X, y > 0`
carry meaning. A point `p ∈ 𝒫 ⊆ ℤ × ℤ` is evaluated as `η(p.1.toNat, p.2) X^{p.1.toNat} y^{p.2}`,
with a natural power of `X` and an integer power of `y`; this is faithful since `p.1 ≥ 1`.

## References

* [Mazur, *Collatz positive density*], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The joint generating function of a hold,
`𝖦(X, y) = ∑_{(j, l) ∈ 𝒫} η(j, l) X^j y^l ∈ [0, ∞]`. -/
@[collatz_pos_dens "def_rn_joint_pgf"]
noncomputable def holdJointPgf (X y : ℝ) : ℝ≥0∞ :=
  ∑' p : bkPoints, ENNReal.ofReal (holdLaw p.1.1.toNat p.1.2 * X ^ p.1.1.toNat * y ^ p.1.2)

/-- `𝖦(X, y)` is the sum over `p ∈ 𝒫` of
`ENNReal.ofReal (η(p.1.toNat, p.2) X^{p.1.toNat} y^{p.2})`. -/
theorem holdJointPgf_def (X y : ℝ) :
    holdJointPgf X y =
      ∑' p : bkPoints, ENNReal.ofReal (holdLaw p.1.1.toNat p.1.2 * X ^ p.1.1.toNat * y ^ p.1.2) :=
  rfl

/-- The terms of `𝖦(X, y)` are nonnegative for `X, y ≥ 0`. -/
theorem holdJointPgf_term_nonneg {X y : ℝ} (hX : 0 ≤ X) (hy : 0 ≤ y) (j : ℕ) (l : ℤ) :
    0 ≤ holdLaw j l * X ^ j * y ^ l :=
  mul_nonneg (mul_nonneg (holdLaw_nonneg j l) (pow_nonneg hX j)) (zpow_nonneg hy l)

/-- `𝖦(X, y)` in the parametrization `(m, l) ↦ (m + 1, l)` of `𝒫` by `ℕ × ℤ`. -/
theorem holdJointPgf_eq_tsum_succ (X y : ℝ) :
    holdJointPgf X y =
      ∑' x : ℕ × ℤ, ENNReal.ofReal (holdLaw (x.1 + 1) x.2 * X ^ (x.1 + 1) * y ^ x.2) := by
  rw [holdJointPgf_def, ← bkPointsEquiv.tsum_eq]
  rfl

/-- `𝖦(X, y)` as a sum over the pairs `(j, l) : ℕ × ℤ` with `1 ≤ j`. -/
theorem holdJointPgf_eq_tsum_natPoints (X y : ℝ) :
    holdJointPgf X y =
      ∑' p : {p : ℕ × ℤ // 1 ≤ p.1},
        ENNReal.ofReal (holdLaw p.1.1 p.1.2 * X ^ p.1.1 * y ^ p.1.2) := by
  rw [holdJointPgf_eq_tsum_succ, ← natPointsEquiv.tsum_eq]
  rfl

/-- If the real series `∑_{p ∈ 𝒫} η(p) X^{j(p)} y^{l(p)}` converges to `s` (with `X, y ≥ 0`),
then `𝖦(X, y) = s`. -/
theorem holdJointPgf_eq_ofReal_of_hasSum {X y s : ℝ} (hX : 0 ≤ X) (hy : 0 ≤ y)
    (h : HasSum (fun p : bkPoints ↦ holdLaw p.1.1.toNat p.1.2 * X ^ p.1.1.toNat * y ^ p.1.2) s) :
    holdJointPgf X y = ENNReal.ofReal s := by
  rw [holdJointPgf_def, ← h.tsum_eq,
    ENNReal.ofReal_tsum_of_nonneg (fun p ↦ holdJointPgf_term_nonneg hX hy _ _) h.summable]

/-- For `X, y ≥ 0`, `𝖦(X, y)` is finite iff the real series `∑_{p ∈ 𝒫} η(p) X^{j(p)} y^{l(p)}`
is summable. -/
theorem holdJointPgf_ne_top_iff {X y : ℝ} (hX : 0 ≤ X) (hy : 0 ≤ y) :
    holdJointPgf X y ≠ ∞ ↔
      Summable (fun p : bkPoints ↦ holdLaw p.1.1.toNat p.1.2 * X ^ p.1.1.toNat * y ^ p.1.2) := by
  rw [holdJointPgf_def]
  simp only [ENNReal.ofReal]
  rw [ENNReal.tsum_coe_ne_top_iff_summable_coe]
  exact summable_congr fun p ↦ Real.coe_toNNReal _ (holdJointPgf_term_nonneg hX hy _ _)

end CollatzPosDens
