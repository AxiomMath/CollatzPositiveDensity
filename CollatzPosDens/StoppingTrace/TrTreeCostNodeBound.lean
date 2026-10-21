/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrTreeCostRange

/-!
# A one-node bound for the tree cost

Let `cut : ℕ → ℕ`, let `W` be a bounded policy, `r, h ∈ ℕ` and `X` real. Suppose that for
every `2 ≤ c ≤ cut(h)` real numbers `f_c, g_c` are given with `ψ^cut_{r,h,c}(X) ≤ f_c`, and
either `g_c ≥ 1`, or `(r, h, c) ∈ W` and `F^{cut,W}_{r+1,h+c}(X) ≤ g_c`. Then
`F^{cut,W}_{r,h}(X) ≤ 1 - ∑_{c=2}^{cut(h)} ϖ(c) (1 - f_c g_c)`. Here `ψ^cut_{r,h,c}(X)` is
`CollatzPosDens.trTreeFactor`, `F^{cut,W}_{r,h}(X)` is `CollatzPosDens.trTreeCost` and `ϖ` is
`CollatzPosDens.varpi`.

## Main results

* `CollatzPosDens.trTreeCost_le_of_node_bound`: the one-node bound
  `F^{cut,W}_{r,h}(X) ≤ 1 - ∑_{c=2}^{cut(h)} ϖ(c) (1 - f_c g_c)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- One-node bound for the tree cost: if `ψ^cut_{r,h,c}(X) ≤ f_c` and either `1 ≤ g_c`, or
`(r, h, c) ∈ W` and `F^{cut,W}_{r+1,h+c}(X) ≤ g_c`, for every `2 ≤ c ≤ cut(h)`, then
`F^{cut,W}_{r,h}(X) ≤ 1 - ∑_{c=2}^{cut(h)} ϖ(c) (1 - f_c g_c)`. -/
@[collatz_pos_dens "lem_tr_tree_cost_node_bound"]
theorem trTreeCost_le_of_node_bound {cut : ℕ → ℕ} {W : Set (ℕ × ℕ × ℕ)}
    (hW : IsBoundedPolicy W) {r h : ℕ} {X : ℝ} {f g : ℕ → ℝ}
    (hf : ∀ c, 2 ≤ c → c ≤ cut h → trTreeFactor cut r h c X ≤ f c)
    (hg : ∀ c, 2 ≤ c → c ≤ cut h →
      1 ≤ g c ∨ ((r, h, c) ∈ W ∧ trTreeCost cut W (r + 1) (h + c) X ≤ g c)) :
    trTreeCost cut W r h X ≤
      1 - ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) * (1 - f c * g c) := by
  classical
  rw [trTreeCost_eq hW]
  refine sub_le_sub_left (Finset.sum_le_sum fun c hc => ?_) 1
  obtain ⟨hc2, hch⟩ := Finset.mem_Icc.mp hc
  set G : ℝ := if (r, h, c) ∈ W then trTreeCost cut W (r + 1) (h + c) X else 1 with hGdef
  have hG : G ∈ Set.Icc (0 : ℝ) 1 := by
    rw [hGdef]; split_ifs
    · exact trTreeCost_mem_Icc _ _ _ _ _
    · exact ⟨zero_le_one, le_rfl⟩
  have hGg : G ≤ g c := by
    rcases hg c hc2 hch with h1 | ⟨hmem, hle⟩
    · exact hG.2.trans h1
    · rwa [hGdef, ite_eq_left_of_eq_true _ _ (eq_true hmem)]
  have hψ0 := (trTreeFactor_pos cut r h c X).le
  have hψf := hf c hc2 hch
  have hprod : trTreeFactor cut r h c X * G ≤ f c * g c :=
    mul_le_mul hψf hGg hG.1 (hψ0.trans hψf)
  exact mul_le_mul_of_nonneg_left (by linarith) (varpi_nonneg _)

end CollatzPosDens
