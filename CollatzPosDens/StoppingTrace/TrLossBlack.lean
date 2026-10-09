/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.StoppingTrace.TrBridgeGain
public import CollatzPosDens.StoppingTrace.TrBridgeLoss
public import CollatzPosDens.StoppingTrace.TrBridgeMass
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrDeltaNonneg
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# The bridge loss at a black point

Fix a level `n` and a residue `ξ ∈ G_n`, and call `y` black when `BkBlack n ξ ε_* y` holds. If
`y` is black, the empty list is the only first-stop list from `y`, its weighted white count
vanishes and its path stays at `y`. Hence the bridge mass is `g_br(y) = 1` and the bridge gain is
`H(y) = max(δ_tr(gap(y)), 0) = δ_tr(gap(y))`, the passage surplus being nonnegative. The bridge
loss is therefore
```
Loss(y) = (1 - d_*) (1 - 1) + δ_tr(gap(y)) = δ_tr(gap(y)).
```

## Main results

* `CollatzPosDens.trBridgeGain_of_bkBlack`: `H(y) = δ_tr(gap(y))` when `y` is black.
* `CollatzPosDens.trBridgeLoss_of_bkBlack`: `Loss(y) = δ_tr(gap(y))` when `y` is black.

## Implementation notes

The source assumes `n ≥ 1` and that `ξ` is a unit; neither is used, and the statement is made
for every level `n` and every `ξ ∈ G_n`. The base point ranges over all of `ℤ × ℤ`.

## References

* [Mazur, *Collatz positive density*], §9.5.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {y : ℤ × ℤ}

/-- At a black point `y`, the bridge gain is `H(y) = δ_tr(gap(y))`. -/
lemma trBridgeGain_of_bkBlack (hy : BkBlack n ξ (epsStar : ℝ) y) :
    trBridgeGain n ξ y = ENNReal.ofReal (trDelta (trGap n ξ (epsStar : ℝ) y)) := by
  rw [trBridgeGain_def, trFirstStopSet_eq_singleton_nil_of_bkBlack hy]
  refine (tsum_singleton ([] : List (List ℤ × ℤ)) fun b ↦ ENNReal.ofReal (trListWeight b) *
    ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ y b b.length)) *
      ENNReal.ofReal
        (max (trDelta (trGap n ξ (epsStar : ℝ) (trPath y b b.length))) 0)).trans ?_
  simp [max_eq_left (trDelta_nonneg _)]

/-- **The bridge loss at a black point.** For every black point `y`,
`Loss(y) = δ_tr(gap(y))`. -/
@[collatz_pos_dens "lem_tr_loss_black"]
theorem trBridgeLoss_of_bkBlack (hy : BkBlack n ξ (epsStar : ℝ) y) :
    trBridgeLoss n ξ y = (trDelta (trGap n ξ (epsStar : ℝ) y) : EReal) := by
  rw [trBridgeLoss_def, trBridgeMass_of_bkBlack hy, trBridgeGain_of_bkBlack hy,
    EReal.coe_ennreal_ofReal, max_eq_left (trDelta_nonneg _), EReal.coe_ennreal_one,
    show (1 : EReal) - 1 = 0 from EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1),
    mul_zero, zero_add]

end CollatzPosDens
