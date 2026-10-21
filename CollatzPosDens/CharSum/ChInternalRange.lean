/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChResidualNonneg

/-!
# The range of the internal weight

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. For every point `x` and every block
`β`, the internal weight satisfies `0 < I(x; β) ≤ 1`. Indeed `I(x; β)` is the exponential of
`-z_*` times a finite sum of residual rewards; the transfer exponent `z_*` is positive and every
residual reward is nonnegative, so the exponent is nonpositive.

## Main results

* `CollatzPosDens.chInternalWeight_le_one`: `I(x; β) ≤ 1`.
* `CollatzPosDens.chInternalWeight_mem_Ioc`: `I(x; β) ∈ (0, 1]`.

## Implementation notes

The bounds hold for every pair `β : List ℤ × ℤ` and every `x : ℤ × ℤ`, not only for blocks
`β ∈ 𝔅` and points `x ∈ ℕ × ℤ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The internal weight is at most `1`. -/
lemma chInternalWeight_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) : chInternalWeight n ξ ε x β ≤ 1 := by
  rw [chInternalWeight_eq_exp, Real.exp_le_one_iff]
  have hz : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
  refine mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz.le) ?_
  exact add_nonneg (Finset.sum_nonneg fun i _ => zero_le_chResidualReward ..)
    (zero_le_chResidualReward ..)

/-- For every point `x` and every block `β`, the internal weight satisfies
`0 < I(x; β) ≤ 1`. -/
@[collatz_pos_dens "lem_ch_internal_range"]
theorem chInternalWeight_mem_Ioc (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) : chInternalWeight n ξ ε x β ∈ Set.Ioc 0 1 :=
  ⟨chInternalWeight_pos n ξ ε x β, chInternalWeight_le_one n ξ ε x β⟩

end CollatzPosDens
