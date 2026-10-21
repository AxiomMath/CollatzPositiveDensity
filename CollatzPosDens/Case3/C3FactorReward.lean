/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockReward
public import CollatzPosDens.StoppingTrace.TrReward

/-!
# The block factor as an exponential of the reward

Fix a level `n` and a residue `ξ ∈ G_n`, and let whiteness, the white factor `w`, the internal
weight `I` and the paid reward all refer to `(n, ξ, ε_*)`. For a point `x` and a block
`β = (c, e) ∈ 𝔅`, `c = (c₁, …, c_m)`, none of whose nonclosing letters lies in `{4, 5}`, the
factor contributed by `β` is a single exponential of its reward:
`w(x + bpt(β)) I(x; β) = exp(-z_* rw(x, β))`.

## Main results

* `CollatzPosDens.chWhiteFactor_mul_chInternalWeight_eq_exp_trReward`: the identity above.

## Implementation notes

Blocks are pairs `β : List ℤ × ℤ` and points are taken in `ℤ × ℤ`, as for
`CollatzPosDens.chBlockPoint`. The point `x` is not required to lie in `𝒫`; the membership `β ∈ 𝔅`
enters only through the hypothesis that the closing letter `β.2` lies in `{4, 5}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For a block `β = (c, e)` with `e ∈ {4, 5}` and no letter of `c` in `{4, 5}`,
`w(x + bpt(β)) I(x; β) = exp(-z_* rw(x, β))`, all at the threshold `ε_*`. -/
@[collatz_pos_dens "lem_c3_factor_reward"]
theorem chWhiteFactor_mul_chInternalWeight_eq_exp_trReward (n : ℕ) (ξ : ResidueGroup n)
    (x : ℤ × ℤ) (β : List ℤ × ℤ) (hc : ∀ a ∈ β.1, a ≠ 4 ∧ a ≠ 5) (he : β.2 = 4 ∨ β.2 = 5) :
    chWhiteFactor n ξ (epsStar : ℝ) (x + chBlockPoint β) *
        chInternalWeight n ξ (epsStar : ℝ) x β =
      Real.exp (-(zStar : ℝ) * trReward n ξ x β) := by
  obtain ⟨c, e⟩ := β
  rw [chWhiteFactor_mul_chInternalWeight n ξ _ x _ hc he, trReward_eq_sum_add, mul_add,
    Real.exp_add, Finset.mul_sum, Real.exp_sum]
  congr 1
  rw [Finset.prod_range fun i => Real.exp (-(zStar : ℝ) *
    chPaidReward n ξ (epsStar : ℝ) (c.getD i 0) (x + ((i : ℤ) + 1, (c.take (i + 1)).sum)))]
  exact Finset.prod_congr rfl fun i _ => by simp

end CollatzPosDens
