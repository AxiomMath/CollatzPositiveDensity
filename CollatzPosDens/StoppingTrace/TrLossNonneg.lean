/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.StoppingTrace.TrBridgeGain
public import CollatzPosDens.StoppingTrace.TrBridgeLoss
public import CollatzPosDens.StoppingTrace.TrBridgeMassLe

/-!
# The bridge loss is nonnegative

Fix a level `n` and a residue `ξ ∈ G_n`. For every base point `y`, the bridge loss
`Loss(y) = (1 - d_*) (1 - g_br(y)) + H(y)` is nonnegative.

Indeed, `0 ≤ g_br(y) ≤ 1` since the bridge mass is at most one, `1 - d_* > 0`, and the bridge
gain `H(y)` is a sum of nonnegative terms.

## Main results

* `CollatzPosDens.trBridgeLoss_nonneg`: `0 ≤ Loss(y)`.

## Implementation notes

In [mazur2026] the lemma is stated for `n ≥ 1`, a unit `ξ ∈ G_n` and `y ∈ 𝒫`. None of these
hypotheses is needed: the bridge mass is at most one for every `n`, `ξ` and `y ∈ ℤ × ℤ`, and
`0 < d_* < 1` is a property of the constant alone. The lemma is therefore stated for every level,
every residue and every base point. The bound `d_* < 1` is read off the exact value of `d_*`
rather than from the estimate `E₈(t) < 1` used in [mazur2026].

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.5.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- **The bridge loss is nonnegative**: `0 ≤ Loss(y)` for every base point `y`. -/
@[collatz_pos_dens "lem_tr_loss_nonneg"]
theorem trBridgeLoss_nonneg (n : ℕ) (ξ : ResidueGroup n) (y : ℤ × ℤ) :
    0 ≤ trBridgeLoss n ξ y := by
  have hm := trBridgeMass_le_one n ξ y
  have hm' := trBridgeMass_ne_top n ξ y
  have hd : (dStar : ℝ) < 1 := by exact_mod_cast dStar_lt_one
  have hg : (0 : EReal) ≤ (trBridgeGain n ξ y : EReal) := EReal.coe_ennreal_nonneg _
  have h1 : (0 : EReal) ≤
      ((1 - (dStar : ℝ) : ℝ) : EReal) * (1 - (trBridgeMass n ξ y : EReal)) := by
    rw [← EReal.coe_ennreal_toReal hm', ← EReal.coe_one, ← EReal.coe_sub, ← EReal.coe_mul,
      EReal.coe_nonneg]
    have : (trBridgeMass n ξ y).toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using hm)
    exact mul_nonneg (by linarith) (by linarith)
  rw [trBridgeLoss_def]
  exact add_nonneg h1 hg

end CollatzPosDens
