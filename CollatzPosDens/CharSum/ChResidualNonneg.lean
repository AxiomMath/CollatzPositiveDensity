/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChResidualReward
public import CollatzPosDens.CharSum.ChPaidRewardNonneg

/-!
# The residual reward is nonnegative

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For every integer `c` and every point
`p`, the residual reward is nonnegative: `ρ_c(p) ≥ 0`. If `c ∉ {4, 5}` or `p` is not white, then
`ρ_c(p) = R_c(p) ≥ 0`. If `c ∈ {4, 5}` and `p` is white, the baseline reward is
`R^old_c(p) = 1`, so `ρ_c(p) = R_c(p) - 1 ≥ R^old_c(p) - 1 = 0`.

## Main results

* `CollatzPosDens.zero_le_chResidualReward`: `0 ≤ ρ_c(p)`.

## Implementation notes

The inequality holds for every `p : ℤ × ℤ`, not only for `p ∈ 𝒫`, since the residual reward is
defined on all of `ℤ × ℤ`.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- For every integer `c` and every point `p`, the residual reward is nonnegative:
`0 ≤ ρ_c(p)`. -/
@[collatz_pos_dens "lem_ch_residual_nonneg"]
theorem zero_le_chResidualReward (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (c : ℤ) (p : ℤ × ℤ) :
    0 ≤ chResidualReward n ξ ε c p := by
  by_cases h : (c = 4 ∨ c = 5) ∧ IsBkWhite n ξ ε p
  · rw [chResidualReward_of_mem h.1 h.2, sub_nonneg,
      ← chOldReward_of_isBkWhite (n := n) (ξ := ξ) (ε := ε) h.1 h.2]
    exact chPaidReward_ge_chOldReward n ξ ε c p
  · rw [chResidualReward_of_not_mem h]
    exact zero_le_chPaidReward n ξ ε c p

end CollatzPosDens
