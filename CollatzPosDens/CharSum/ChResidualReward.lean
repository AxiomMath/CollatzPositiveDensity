/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.CharSum.ChPaidReward

/-!
# The residual reward

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For an integer `c` and a point `p`,
the *residual reward* is the paid reward with the unit reward of a white closing letter
removed:
`ρ_c(p) = R_c(p) - [c ∈ {4, 5}] [p white]`.

## Main definitions

* `CollatzPosDens.chResidualReward n ξ ε c p`: the residual reward `ρ_c(p)`.

## Main results

* `CollatzPosDens.chResidualReward_of_mem`: `ρ_c(p) = R_c(p) - 1` when `c ∈ {4, 5}` and `p` is
  white.
* `CollatzPosDens.chResidualReward_of_not_mem`: `ρ_c(p) = R_c(p)` otherwise.
* `CollatzPosDens.chResidualReward_le_chPaidReward`: `ρ_c(p) ≤ R_c(p)`.
* `CollatzPosDens.chResidualReward_eq_zero_of_lt_bkJ`: `ρ_c(p) = 0` when `j(p) > ⌊n/2⌋`.

## Implementation notes

The reward is defined for every `p : ℤ × ℤ`, as the paid reward and whiteness are.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- The residual reward `ρ_c(p) = R_c(p) - [c ∈ {4, 5}] [p white]`. -/
@[collatz_pos_dens "def_ch_residual_reward"]
noncomputable def chResidualReward (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (c : ℤ) (p : ℤ × ℤ) :
    ℝ :=
  chPaidReward n ξ ε c p - if (c = 4 ∨ c = 5) ∧ IsBkWhite n ξ ε p then 1 else 0

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {c : ℤ} {p : ℤ × ℤ}

/-- The residual reward of a white point at a letter `c ∈ {4, 5}`. -/
theorem chResidualReward_of_mem (hc : c = 4 ∨ c = 5) (hp : IsBkWhite n ξ ε p) :
    chResidualReward n ξ ε c p = chPaidReward n ξ ε c p - 1 := by
  simp only [chResidualReward, hc, hp, and_self, ite_true]

/-- The residual reward equals the paid reward unless `c ∈ {4, 5}` and `p` is white. -/
theorem chResidualReward_of_not_mem (h : ¬ ((c = 4 ∨ c = 5) ∧ IsBkWhite n ξ ε p)) :
    chResidualReward n ξ ε c p = chPaidReward n ξ ε c p := by
  simp only [chResidualReward, h, ite_false, sub_zero]

/-- The residual reward equals the paid reward at a letter `c ∉ {4, 5}`. -/
theorem chResidualReward_of_ne (h₄ : c ≠ 4) (h₅ : c ≠ 5) :
    chResidualReward n ξ ε c p = chPaidReward n ξ ε c p :=
  chResidualReward_of_not_mem fun h => h.1.elim h₄ h₅

/-- The residual reward equals the paid reward at a point that is not white. -/
theorem chResidualReward_of_not_isBkWhite (hp : ¬ IsBkWhite n ξ ε p) :
    chResidualReward n ξ ε c p = chPaidReward n ξ ε c p :=
  chResidualReward_of_not_mem fun h => hp h.2

/-- The residual reward is at most the paid reward. -/
theorem chResidualReward_le_chPaidReward :
    chResidualReward n ξ ε c p ≤ chPaidReward n ξ ε c p := by
  unfold chResidualReward
  split_ifs <;> linarith

/-- `ρ_c(p) = 0` when `j(p) > ⌊n/2⌋`. -/
theorem chResidualReward_eq_zero_of_lt_bkJ (hp : ((n / 2 : ℕ) : ℤ) < bkJ p) :
    chResidualReward n ξ ε c p = 0 := by
  rw [chResidualReward_of_not_isBkWhite fun h => (not_le_of_gt hp) h.bkJ_le,
    chPaidReward_eq_zero_of_lt_bkJ hp]

end CollatzPosDens
