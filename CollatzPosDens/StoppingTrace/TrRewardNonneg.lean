/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidRewardNonneg
public import CollatzPosDens.StoppingTrace.TrReward

/-!
# Nonnegativity of the block reward

Fix a level `n` and a residue `ξ ∈ G_n`. For every point `x ∈ 𝒫` and every block `β ∈ 𝔅`, the
reward `rw(x, β)` is nonnegative: it is a finite sum of paid rewards `R_a(p)`, each of which is
nonnegative.

## Main results

* `CollatzPosDens.zero_le_trReward`: `0 ≤ rw(x, β)`.

## Implementation notes

The reward is defined for every `x : ℤ × ℤ` and every pair `β : List ℤ × ℤ`, and the
inequality holds in that generality, not only for `x ∈ 𝒫` and `β ∈ 𝔅`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Rewards are nonnegative.** For every point `x` and every block `β`, `0 ≤ rw(x, β)`. -/
@[collatz_pos_dens "lem_tr_reward_nonneg"]
theorem zero_le_trReward (n : ℕ) (ξ : ResidueGroup n) (x : ℤ × ℤ) (β : List ℤ × ℤ) :
    0 ≤ trReward n ξ x β :=
  Finset.sum_nonneg fun _ _ => zero_le_chPaidReward _ _ _ _ _

end CollatzPosDens
