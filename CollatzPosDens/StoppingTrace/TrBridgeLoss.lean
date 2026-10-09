/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.StoppingTrace.TrBridgeGain
public import CollatzPosDens.StoppingTrace.TrBridgeMass
public import Mathlib.Data.EReal.Operations

/-!
# The bridge loss

Fix a level `n` and a residue `ξ : ResidueGroup n`. For a base point `y : ℤ × ℤ`, the *bridge
loss* combines the bridge mass `g_br(y) ∈ [0, ∞]` and the bridge gain `H(y) ∈ [0, ∞]` with the
single-passage loss `d_*`:
```
Loss(y) = (1 - d_*) (1 - g_br(y)) + H(y) ∈ [-∞, ∞].
```
When both `g_br(y)` and `H(y)` are finite, this is the real number
`(1 - d_*) (1 - g_br(y)) + H(y)`.

## Main definitions

* `CollatzPosDens.trBridgeLoss n ξ y`: the bridge loss `Loss(y) ∈ [-∞, ∞]`.

## Main results

* `CollatzPosDens.trBridgeLoss_def`: the unfolding of the definition.
* `CollatzPosDens.trBridgeLoss_eq_coe`: if `g_br(y)` and `H(y)` are finite, the bridge loss
  is the real number `(1 - d_*) (1 - g_br(y)) + H(y)`.
* `CollatzPosDens.trBridgeLoss_of_eq_zero`: if `g_br(y) = H(y) = 0`, then
  `Loss(y) = 1 - d_*`.

## Implementation notes

The loss takes values in the extended reals `EReal`, into which `g_br(y)` and `H(y)` are cast
from `[0, ∞]`. Since `1 - d_* > 0`, the only expression without a classical value is
`g_br(y) = H(y) = ∞`, where the formula reads `-∞ + ∞`; there the value is that of addition on
`EReal`, namely `-∞`.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The bridge loss `Loss(y) = (1 - d_*) (1 - g_br(y)) + H(y) ∈ [-∞, ∞]`, where `g_br` is the
bridge mass and `H` the bridge gain. -/
@[collatz_pos_dens "def_tr_bridge_loss"]
noncomputable def trBridgeLoss (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) : EReal :=
  ((1 - (dStar : ℝ) : ℝ) : EReal) * (1 - (trBridgeMass n ξ y : EReal)) +
    (trBridgeGain n ξ y : EReal)

/-- The bridge loss is `(1 - d_*) (1 - g_br(y)) + H(y)`, computed in `EReal`. -/
lemma trBridgeLoss_def (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) :
    trBridgeLoss n ξ y =
      ((1 - (dStar : ℝ) : ℝ) : EReal) * (1 - (trBridgeMass n ξ y : EReal)) +
        (trBridgeGain n ξ y : EReal) :=
  rfl

variable {n : ℕ} {ξ : ResidueGroup n} {y : ℤ × ℤ}

/-- When the bridge mass and the bridge gain are finite, the bridge loss is the real number
`(1 - d_*) (1 - g_br(y)) + H(y)`. -/
lemma trBridgeLoss_eq_coe (hm : trBridgeMass n ξ y ≠ ∞) (hg : trBridgeGain n ξ y ≠ ∞) :
    trBridgeLoss n ξ y =
      (((1 - (dStar : ℝ)) * (1 - (trBridgeMass n ξ y).toReal) +
        (trBridgeGain n ξ y).toReal : ℝ) : EReal) := by
  rw [trBridgeLoss_def, ← EReal.coe_ennreal_toReal hm, ← EReal.coe_ennreal_toReal hg]
  norm_cast

/-- When the bridge mass and the bridge gain vanish, the bridge loss is `1 - d_*`. -/
lemma trBridgeLoss_of_eq_zero (hm : trBridgeMass n ξ y = 0) (hg : trBridgeGain n ξ y = 0) :
    trBridgeLoss n ξ y = ((1 - (dStar : ℝ) : ℝ) : EReal) := by
  rw [trBridgeLoss_def, hm, hg]
  simp

end CollatzPosDens
