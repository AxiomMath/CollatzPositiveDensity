/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidRewardBound
public import CollatzPosDens.CharSum.ChPenalty
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.CharSum.ChRawFactorRange
public import CollatzPosDens.Transfer.EpsStar

/-!
# The raw factors of a word are bounded by its penalty

Fix `n`, `ξ ∈ G_n` and `ε ≥ ε_*`. For every word `b = (b₁, …, b_k)` of integers,
`∏_{i=1}^k φ_{b_i}((i, b₁ + ⋯ + b_i)) ≤ Pen(b)`.

Both sides are products over `i = 1, …, k` of nonnegative factors, so it suffices to compare
them factor by factor: with `p_i = (i, b₁ + ⋯ + b_i) ∈ 𝒫`, the paid reward bound gives
`φ_{b_i}(p_i) ≤ exp(-z_* R_{b_i}(p_i))`, which is the `i`-th factor of `Pen(b)`.

## Main results

* `CollatzPosDens.prod_chRawFactor_le_chPenalty`:
  `∏ᵢ φ_{b_i}((i, b₁ + ⋯ + b_i)) ≤ Pen(b)`.

## Implementation notes

Words are `List ℤ`, indexed from `0`, so the source's factor with index `i` is the term
`i - 1 : Fin b.length`, with letter `b[i - 1]` and partial sum `(b.take i).sum`.

## References

* [Mazur, *Collatz positive density*], §7.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- **The raw factors of a word are bounded by its penalty.** For `ε ≥ ε_*` and every word
`b = (b₁, …, b_k)`, `∏_{i=1}^k φ_{b_i}((i, b₁ + ⋯ + b_i)) ≤ Pen(b)`. -/
@[collatz_pos_dens "lem_ch_factor_penalty"]
theorem prod_chPairFactor_le_chPenalty {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    (hε : (epsStar : ℝ) ≤ ε) (b : List ℤ) :
    ∏ i : Fin b.length, chRawFactor n ξ b[i] (((i + 1 : ℕ) : ℤ), (b.take (i + 1)).sum) ≤
      chPenalty n ξ ε b := by
  rw [chPenalty_def, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_le_prod₀ (fun i _ => (chRawFactor_mem_Icc n ξ _ _).1) fun i _ => ?_
  have hp : (((i + 1 : ℕ) : ℤ), (b.take (i + 1)).sum) ∈ bkPoints := by
    simp [bkPoints]
  have h := chRawFactor_le_exp_neg_chPaidReward (n := n) (ξ := ξ) hε b[i] hp
  rw [neg_mul]
  simpa using h

end CollatzPosDens
