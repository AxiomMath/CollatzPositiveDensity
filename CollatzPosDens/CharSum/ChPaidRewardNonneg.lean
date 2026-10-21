/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidRewardGeOld

/-!
# The paid reward is nonnegative

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For every integer `c` and every point
`p`, the paid reward is nonnegative: `R_c(p) ≥ 0`. Every case of the baseline reward
`R^old_c(p)` is a sum of nonnegative terms, since `κ_* > 0`, `M_c(p) ≥ 0`, `c - 1 > 0` for
`c ≥ 6` and `1 - z_*/2 = 6117/6250 > 0`; and `R_c(p) ≥ R^old_c(p)`.

## Main results

* `CollatzPosDens.zero_le_chPaidReward`: `0 ≤ R_c(p)`.

## Implementation notes

The inequality holds for every `p : ℤ × ℤ`, not only for `p ∈ 𝒫`, since the paid reward is
defined on all of `ℤ × ℤ`.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every integer `c` and every point `p`, the paid reward is nonnegative: `0 ≤ R_c(p)`. -/
@[collatz_pos_dens "lem_ch_paid_reward_nonneg"]
theorem zero_le_chPaidReward (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (c : ℤ) (p : ℤ × ℤ) :
    0 ≤ chPaidReward n ξ ε c p :=
  chOldReward_nonneg.trans (chPaidReward_ge_chOldReward n ξ ε c p)

end CollatzPosDens
