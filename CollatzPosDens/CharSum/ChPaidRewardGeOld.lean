/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidReward

/-!
# The paid reward dominates the baseline reward

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For every integer `c` and every point
`p`, the paid reward dominates the baseline paid reward: `R_c(p) ≥ R^old_c(p)`. Indeed `R_c(p)` is
either `R^old_c(p)` itself or the maximum of `R^old_c(p)` and a logarithmic term.

## Main results

* `CollatzPosDens.chPaidReward_ge_chOldReward`: `R_c(p) ≥ R^old_c(p)`.

## Implementation notes

The inequality holds for every `p : ℤ × ℤ`, not only for `p ∈ 𝒫`, since both rewards are defined
on all of `ℤ × ℤ`.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every integer `c` and every point `p`, the paid reward dominates the baseline paid
reward: `R_c(p) ≥ R^old_c(p)`. -/
@[collatz_pos_dens "lem_ch_paid_reward_ge_old"]
theorem chPaidReward_ge_chOldReward (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (c : ℤ) (p : ℤ × ℤ) :
    chOldReward n ξ ε c p ≤ chPaidReward n ξ ε c p :=
  chOldReward_le_chPaidReward

end CollatzPosDens
