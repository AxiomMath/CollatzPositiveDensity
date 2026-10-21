/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChPaidReward
public import CollatzPosDens.Transfer.EpsStar
public import Mathlib.Data.List.GetD

/-!
# The reward of a block

Fix a level `n` and a residue `ξ ∈ G_n`, and write `R_a(p)` for the paid reward of
`(n, ξ, ε_*)`. For a point `x ∈ 𝒫` and a block `β = (c, e)` with `c = (c₁, …, c_m)`, put
`a_i = c_i` for `1 ≤ i ≤ m` and `a_{m+1} = e`. The *reward* of `β` at `x` is
```
rw(x, β) = ∑_{i=1}^{m+1} R_{a_i}(x + (i, a₁ + ⋯ + a_i)),
```
the sum of the paid rewards collected at the successive points visited by the block, the last
of which is `x + bpt(β)`.

## Main definitions

* `CollatzPosDens.trReward n ξ x β`: the reward `rw(x, β) ∈ ℝ`.

## Main results

* `CollatzPosDens.trReward_eq_sum_add`: the reward splits as the rewards of the nonclosing
  letters plus `R_e(x + bpt(β))`.
* `CollatzPosDens.trReward_nonneg`: rewards are nonnegative.
* `CollatzPosDens.chPaidReward_le_trReward`: `R_e(x + bpt(β)) ≤ rw(x, β)`.
* `CollatzPosDens.trReward_nil`: a block with no nonclosing letters has reward `R_e(x + (1, e))`.

## Implementation notes

As for `CollatzPosDens.chBlockPoint`, blocks are modelled as pairs `(c, e) : List ℤ × ℤ` and
points of `𝒫` as elements of `ℤ × ℤ`; the reward is defined for all of them, and is used for
`x ∈ 𝒫` and blocks of `𝔅`. The word `(a₁, …, a_{m+1})` is the list `c ++ [e]`, indexed from `0`:
the summand of index `i ∈ [0, m]` is the summand `i + 1` of the displayed sum, with letter
`(c ++ [e]).getD i 0` and partial sum `((c ++ [e]).take (i + 1)).sum`. The definition does not
need `ξ` to be a unit, and does not assume it.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The reward `rw(x, β) = ∑_{i=1}^{m+1} R_{a_i}(x + (i, a₁ + ⋯ + a_i))` of a block
`β = (c, e)` at a point `x`, where `(a₁, …, a_{m+1}) = (c₁, …, c_m, e)` and `R` is the paid
reward of `(n, ξ, ε_*)`. -/
@[collatz_pos_dens "def_tr_reward"]
noncomputable def trReward (n : ℕ) (ξ : ResidueGroup n) (x : ℤ × ℤ) (β : List ℤ × ℤ) : ℝ :=
  ∑ i ∈ Finset.range (β.1.length + 1),
    chPaidReward n ξ (epsStar : ℝ) ((β.1 ++ [β.2]).getD i 0)
      (x + ((i : ℤ) + 1, ((β.1 ++ [β.2]).take (i + 1)).sum))

variable {n : ℕ} {ξ : ResidueGroup n}

/-- The reward of `(c, e)` is the sum of the paid rewards of the nonclosing letters `cᵢ` at
`x + (i, c₁ + ⋯ + cᵢ)`, plus the paid reward `R_e(x + bpt(c, e))` of the closing letter. -/
theorem trReward_eq_sum_add (x : ℤ × ℤ) (c : List ℤ) (e : ℤ) :
    trReward n ξ x (c, e) =
      (∑ i ∈ Finset.range c.length,
        chPaidReward n ξ (epsStar : ℝ) (c.getD i 0) (x + ((i : ℤ) + 1, (c.take (i + 1)).sum))) +
        chPaidReward n ξ (epsStar : ℝ) e (x + chBlockPoint (c, e)) := by
  simp only [trReward]
  rw [Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi : i < c.length := Finset.mem_range.1 hi
    rw [List.getD_append _ _ _ _ hi, List.take_append_of_le_length (by omega)]
  · simp [chBlockPoint, List.getD_eq_getElem?_getD, List.take_of_length_le]

/-- Rewards are nonnegative. -/
theorem trReward_nonneg (x : ℤ × ℤ) (β : List ℤ × ℤ) : 0 ≤ trReward n ξ x β :=
  Finset.sum_nonneg fun _ _ => chPaidReward_nonneg

/-- A block's reward is at least the paid reward `R_e(x + bpt(β))` of its closing letter. -/
theorem chPaidReward_le_trReward (x : ℤ × ℤ) (β : List ℤ × ℤ) :
    chPaidReward n ξ (epsStar : ℝ) β.2 (x + chBlockPoint β) ≤ trReward n ξ x β := by
  obtain ⟨c, e⟩ := β
  rw [trReward_eq_sum_add]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => chPaidReward_nonneg)

/-- A block with no nonclosing letters is rewarded only for its endpoint. -/
@[simp]
theorem trReward_nil (x : ℤ × ℤ) (e : ℤ) :
    trReward n ξ x ([], e) = chPaidReward n ξ (epsStar : ℝ) e (x + (1, e)) := by
  simp [trReward_eq_sum_add, chBlockPoint]

end CollatzPosDens
