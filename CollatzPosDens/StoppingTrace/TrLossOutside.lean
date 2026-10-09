/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.StoppingTrace.TrBridgeGain
public import CollatzPosDens.StoppingTrace.TrBridgeLoss
public import CollatzPosDens.StoppingTrace.TrBridgeMass
public import CollatzPosDens.StoppingTrace.TrFirstStopSet
public import CollatzPosDens.StoppingTrace.TrPathGrowthJ

/-!
# The bridge loss beyond the strip

Fix a level `n` and a residue `ξ` in `CollatzPosDens.ResidueGroup n`, and let `J = ⌊n/2⌋`. The
strip is the set of points `y ∈ ℤ × ℤ` with `j(y) = CollatzPosDens.bkJ y ≤ J`. If a base point `y`
lies beyond the strip, i.e. `j(y) > J`, then the bridge loss is `Loss(y) = 1 - d_*`, where
`d_* = CollatzPosDens.dStar`. Indeed the `j`-coordinate does not decrease along the path of any
block list, so `j(x_t(y, u)) ≥ j(y) > J` for every list `u` and every time `t`; hence no point of
any path from `y` is black, the set `𝒰(y)` of first-stop lists is empty, and the bridge mass
`g_br(y)` and the bridge gain `H(y)` both vanish.

## Main results

* `CollatzPosDens.trFirstStopSet_eq_empty_of_lt_bkJ`: `𝒰(y) = ∅` when `j(y) > J`.
* `CollatzPosDens.trBridgeMass_eq_zero_of_lt_bkJ`: `g_br(y) = 0` when `j(y) > J`.
* `CollatzPosDens.trBridgeGain_eq_zero_of_lt_bkJ`: `H(y) = 0` when `j(y) > J`.
* `CollatzPosDens.trBridgeLoss_of_lt_bkJ`: `Loss(y) = 1 - d_*` when `j(y) > J`.

## Implementation notes

The emptiness of `𝒰(y)` holds at every colour scale `ε`, and the base point `y` ranges over all
of `ℤ × ℤ`. The bound `J = ⌊n/2⌋` is the natural-number quotient `n / 2`, cast to `ℤ`, as in
`CollatzPosDens.BkBlack`.

## References

* [Mazur, *Collatz positive density*], §9.5.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n} {y : ℤ × ℤ}

/-- Beyond the strip there are no first-stop lists: if `j(y) > ⌊n/2⌋`, then `𝒰(y) = ∅` at
every colour scale `ε`. -/
lemma trFirstStopSet_eq_empty_of_lt_bkJ {ε : ℝ} (hy : ((n / 2 : ℕ) : ℤ) < bkJ y) :
    trFirstStopSet n ξ ε y = ∅ := by
  refine Set.eq_empty_iff_forall_notMem.2 fun u hu ↦ ?_
  have hg := trPath_bkJ_sub_bkJ_ge y u (Nat.zero_le u.length)
  rw [trPath_zero] at hg
  have := (trFirstStopSet_bkBlack hu).bkJ_le
  omega

/-- Beyond the strip the bridge mass vanishes: `g_br(y) = 0` when `j(y) > ⌊n/2⌋`. -/
lemma trBridgeMass_eq_zero_of_lt_bkJ (hy : ((n / 2 : ℕ) : ℤ) < bkJ y) :
    trBridgeMass n ξ y = 0 := by
  rw [trBridgeMass_def, trFirstStopSet_eq_empty_of_lt_bkJ hy]
  exact tsum_empty

/-- Beyond the strip the bridge gain vanishes: `H(y) = 0` when `j(y) > ⌊n/2⌋`. -/
lemma trBridgeGain_eq_zero_of_lt_bkJ (hy : ((n / 2 : ℕ) : ℤ) < bkJ y) :
    trBridgeGain n ξ y = 0 := by
  rw [trBridgeGain_def, trFirstStopSet_eq_empty_of_lt_bkJ hy]
  exact tsum_empty

/-- If `j(y) > ⌊n/2⌋`, then the bridge loss is `Loss(y) = 1 - d_*`. -/
@[collatz_pos_dens "lem_tr_loss_outside"]
theorem trBridgeLoss_of_lt_bkJ (hy : ((n / 2 : ℕ) : ℤ) < bkJ y) :
    trBridgeLoss n ξ y = ((1 - (dStar : ℝ) : ℝ) : EReal) :=
  trBridgeLoss_of_eq_zero (trBridgeMass_eq_zero_of_lt_bkJ hy) (trBridgeGain_eq_zero_of_lt_bkJ hy)

end CollatzPosDens
