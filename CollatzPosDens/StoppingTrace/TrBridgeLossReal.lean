/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.StoppingTrace.TrBridgeLoss
public import CollatzPosDens.StoppingTrace.TrBridgeMassLe
public import CollatzPosDens.StoppingTrace.TrDeltaNonneg
public import CollatzPosDens.StoppingTrace.TrGainLe
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrLossBlack
public import CollatzPosDens.StoppingTrace.TrLossOutside

/-!
# The bridge loss as a real number

Fix a level `n` and a residue `ξ ∈ G_n`. The bridge loss
`Loss(y) = (1 - d_*) (1 - g_br(y)) + H(y)` is defined in `EReal`, because the bridge mass
`g_br(y)` and the bridge gain `H(y)` live in `[0, ∞]`. Both are finite at every `y ∈ 𝒫` for a
unit `ξ`, so there `Loss(y)` is the real number
`(1 - d_*) (1 - g_br(y)) + H(y)`, written `trBridgeLossReal n ξ y`, which lies in `[0, 1 - d_*]`.

## Main results

* `CollatzPosDens.trBridgeLossReal`: the real number `(1 - d_*) (1 - g_br(y)) + H(y)`.
* `CollatzPosDens.trBridgeLoss_eq_coe_trBridgeLossReal`: `Loss(y) = trBridgeLossReal n ξ y` at
  every `y ∈ 𝒫`, for a unit `ξ`.
* `CollatzPosDens.trBridgeLossReal_nonneg`, `CollatzPosDens.trBridgeLossReal_le`:
  `0 ≤ trBridgeLossReal n ξ y ≤ 1 - d_*`.
* `CollatzPosDens.trBridgeLossReal_of_bkBlack`, `CollatzPosDens.trBridgeLossReal_of_lt_bkJ`: its
  values at a black point and beyond the strip.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

variable {n : ℕ} {ξ : ResidueGroup n} {y : ℤ × ℤ}

/-- The bridge loss as a real number, `(1 - d_*) (1 - g_br(y)) + H(y)`. -/
noncomputable def trBridgeLossReal (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) : ℝ :=
  (1 - (dStar : ℝ)) * (1 - (trBridgeMass n ξ y).toReal) + (trBridgeGain n ξ y).toReal

/-- At a point `y ∈ 𝒫`, the bridge loss is the real number `trBridgeLossReal n ξ y`. -/
theorem trBridgeLoss_eq_coe_trBridgeLossReal (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints) :
    trBridgeLoss n ξ y = (trBridgeLossReal n ξ y : EReal) :=
  trBridgeLoss_eq_coe (trBridgeMass_ne_top n ξ y) (trBridgeGain_ne_top hξ hy)

/-- At a point `y ∈ 𝒫`, the bridge loss in `[0, ∞]` is `ofReal (trBridgeLossReal n ξ y)`. -/
theorem toENNReal_trBridgeLoss (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints) :
    (trBridgeLoss n ξ y).toENNReal = ENNReal.ofReal (trBridgeLossReal n ξ y) := by
  rw [trBridgeLoss_eq_coe_trBridgeLossReal hξ hy, EReal.real_coe_toENNReal]

/-- `H(y) ≤ (1 - d_*) g_br(y)` as real numbers. -/
theorem toReal_trBridgeGain_le (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints) :
    (trBridgeGain n ξ y).toReal ≤ (1 - (dStar : ℝ)) * (trBridgeMass n ξ y).toReal := by
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (trBridgeMass_ne_top n ξ y)) (trBridgeGain_le hξ hy)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal one_sub_dStar_pos.le] at h

/-- `0 ≤ trBridgeLossReal n ξ y`, from `g_br(y) ≤ 1` and `d_* < 1`. -/
theorem trBridgeLossReal_nonneg (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) :
    0 ≤ trBridgeLossReal n ξ y := by
  have hg : (trBridgeMass n ξ y).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (trBridgeMass_le_one n ξ y)
  have := one_sub_dStar_pos
  unfold trBridgeLossReal
  nlinarith [ENNReal.toReal_nonneg (a := trBridgeGain n ξ y)]

/-- At a point `y ∈ 𝒫`, `trBridgeLossReal n ξ y ≤ 1 - d_*`. -/
theorem trBridgeLossReal_le (hξ : IsResidueUnit ξ) (hy : y ∈ bkPoints) :
    trBridgeLossReal n ξ y ≤ 1 - (dStar : ℝ) := by
  have := toReal_trBridgeGain_le hξ hy
  unfold trBridgeLossReal
  nlinarith

/-- At a black point the real bridge loss is `δ_tr(gap(y))`. -/
theorem trBridgeLossReal_of_bkBlack (hy : BkBlack n ξ (epsStar : ℝ) y) :
    trBridgeLossReal n ξ y = trDelta (trGap n ξ (epsStar : ℝ) y) := by
  rw [trBridgeLossReal, trBridgeMass_of_bkBlack hy, trBridgeGain_of_bkBlack hy,
    ENNReal.toReal_ofReal (trDelta_nonneg _)]
  simp

/-- Beyond the strip the real bridge loss is `1 - d_*`. -/
theorem trBridgeLossReal_of_lt_bkJ (hy : ((n / 2 : ℕ) : ℤ) < bkJ y) :
    trBridgeLossReal n ξ y = 1 - (dStar : ℝ) := by
  rw [trBridgeLossReal, trBridgeMass_eq_zero_of_lt_bkJ hy, trBridgeGain_eq_zero_of_lt_bkJ hy]
  simp

end CollatzPosDens
