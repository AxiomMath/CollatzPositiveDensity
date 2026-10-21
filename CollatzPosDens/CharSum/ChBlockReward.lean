/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChWhiteFactor

/-!
# The reward of a block

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and let `z_*` be the transfer
exponent. Let `β = (c, e)` be a block, `c = (c₁, …, c_m)`, with closing letter `e ∈ {4, 5}` and
no nonclosing letter in `{4, 5}`, and let `x` be a point. The white factor at the block's end
point `y = x + bpt(β)` exactly cancels the unit reward removed from the closing letter by the
residual reward, so that
`w(y) I(x; β) = ∏_{i=1}^m exp(-z_* R_{c_i}(x + (i, c₁ + ⋯ + c_i))) · exp(-z_* R_e(y))`,
where `R` is the paid reward.

## Main results

* `CollatzPosDens.chWhiteFactor_mul_chInternalWeight`: the identity above.

## Implementation notes

As for `CollatzPosDens.chInternalWeight`, a block is a pair `β : List ℤ × ℤ`, the point `x` is
taken in `ℤ × ℤ`, and the index `i : Fin m` is `0`-based. The membership `β ∈ 𝔅` enters only
through the hypothesis that the closing letter `β.2` lies in `{4, 5}`, which is needed: at a white
end point and a closing letter outside `{4, 5}` the two sides differ by the factor `e^{-z_*}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For a block `β = (c, e)` with `e ∈ {4, 5}` and no letter of `c` in `{4, 5}`, the white
factor at `y = x + bpt(β)` times the internal weight is the product of the factors
`exp(-z_* R)` of the paid rewards:
`w(y) I(x; β) = ∏_{i=1}^m exp(-z_* R_{c_i}(x + (i, c₁ + ⋯ + c_i))) · exp(-z_* R_e(y))`. -/
@[collatz_pos_dens "lem_ch_block_reward"]
theorem chWhiteFactor_mul_chInternalWeight (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) (hc : ∀ a ∈ β.1, a ≠ 4 ∧ a ≠ 5) (he : β.2 = 4 ∨ β.2 = 5) :
    chWhiteFactor n ξ ε (x + chBlockPoint β) * chInternalWeight n ξ ε x β =
      (∏ i : Fin β.1.length,
        Real.exp (-(zStar : ℝ) *
          chPaidReward n ξ ε β.1[i] (x + ((i : ℤ) + 1, (β.1.take (i + 1)).sum)))) *
        Real.exp (-(zStar : ℝ) * chPaidReward n ξ ε β.2 (x + chBlockPoint β)) := by
  have hprod : (∏ i : Fin β.1.length,
      Real.exp (-(zStar : ℝ) *
        chResidualReward n ξ ε β.1[i] (x + ((i : ℤ) + 1, (β.1.take (i + 1)).sum)))) =
      ∏ i : Fin β.1.length,
        Real.exp (-(zStar : ℝ) *
          chPaidReward n ξ ε β.1[i] (x + ((i : ℤ) + 1, (β.1.take (i + 1)).sum))) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    have h := hc β.1[i] (List.getElem_mem i.2)
    rw [chResidualReward_of_ne h.1 h.2]
  have hlast : chWhiteFactor n ξ ε (x + chBlockPoint β) *
      Real.exp (-(zStar : ℝ) * chResidualReward n ξ ε β.2 (x + chBlockPoint β)) =
      Real.exp (-(zStar : ℝ) * chPaidReward n ξ ε β.2 (x + chBlockPoint β)) := by
    by_cases hw : IsBkWhite n ξ ε (x + chBlockPoint β)
    · rw [chWhiteFactor_of_isBkWhite hw, chResidualReward_of_mem he hw, ← Real.exp_add]
      ring_nf
    · rw [chWhiteFactor_of_not_isBkWhite hw, chResidualReward_of_not_isBkWhite hw, one_mul]
  rw [chInternalWeight, hprod, mul_left_comm, hlast]

end CollatzPosDens
