/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrTreeCost

/-!
# The tree cost lies in `[0, 1]`

For every cutoff `cut : ℕ → ℕ`, every set of triples `W ⊆ ℕ × ℕ × ℕ`, all `r h : ℕ` and every
real `X`, the tree cost `CollatzPosDens.trTreeCost cut W r h X` lies in the closed interval
`[0, 1]`.

## Main results

* `CollatzPosDens.trTreeCost_mem_Icc`: `trTreeCost cut W r h X ∈ Set.Icc 0 1`.

## Implementation notes

The bound holds for every set `W`, not only for bounded policies, and is stated without a
boundedness hypothesis. The two inequalities are `CollatzPosDens.trTreeCost_nonneg` and
`CollatzPosDens.trTreeCost_le_one`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The tree cost lies in `[0, 1]`: `0 ≤ trTreeCost cut W r h X ≤ 1` for every cutoff `cut`,
every set of triples `W`, all `r h : ℕ` and every real `X`. -/
@[collatz_pos_dens "lem_tr_tree_cost_range"]
theorem trTreeCost_mem_Icc (cut : ℕ → ℕ) (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ) (X : ℝ) :
    trTreeCost cut W r h X ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨trTreeCost_nonneg cut W r h X, trTreeCost_le_one cut W r h X⟩

end CollatzPosDens
