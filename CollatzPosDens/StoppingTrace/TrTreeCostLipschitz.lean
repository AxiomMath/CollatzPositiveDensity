/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCapLipschitz
public import CollatzPosDens.StoppingTrace.TrTreeCostRange
public import CollatzPosDens.StoppingTrace.TrTreeLip

/-!
# A tree cost is Lipschitz

Let `cut : ℕ → ℕ` and let `W` be a bounded policy. For `r, h ∈ ℕ` and real `X, X'` the tree cost
satisfies `|F^{cut,W}_{r,h}(X) - F^{cut,W}_{r,h}(X')| ≤ L^{cut,W}_{r,h} |X - X'|`, where
`L^{cut,W}_{r,h}` is the constant `CollatzPosDens.trTreeLip`.

The proof is by downward induction on `h`, for all `r` at once. For `2 ≤ c ≤ cut(h)` the
retained factor `ψ^cut_{r,h,c}(X) = Φ^cap_c(9^r X / 2^{h+c})` is Lipschitz with constant
`ℓ_c 9^r 2^{-h-c}`, by `CollatzPosDens.abs_trCapFactor_sub_le`, and `ℓ_2 = 0`. The continuation
value `G_{r,h,c}` is Lipschitz with constant `L^{cut,W}_{r+1,h+c}` when `(r, h, c) ∈ W`, by
induction, and constant otherwise. For `p, p', g, g' ∈ [0, 1]` one has
`|p g - p' g'| ≤ |p - p'| + |g - g'|`, and all retained factors and continuation values lie in
`[0, 1]`. Summing against the nonnegative weights `ϖ(c)` gives the claim.

## Main results

* `CollatzPosDens.abs_trTreeCost_sub_le`: the tree cost `F^{cut,W}_{r,h}` is Lipschitz with
  constant `L^{cut,W}_{r,h}`.

## Implementation notes

The bound holds for every set `W ⊆ ℕ × ℕ × ℕ`, not only for bounded policies: the recursions
defining `CollatzPosDens.trTreeCost` and `CollatzPosDens.trTreeLip` refine a child under the
same condition, so the induction never uses that `W` is bounded. The statement is therefore
given without that hypothesis.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `p, p', g, g' ∈ [0, 1]`, `|p g - p' g'| ≤ |p - p'| + |g - g'|`. -/
private theorem abs_mul_sub_mul_le_of_mem_Icc {p p' g g' : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hg' : g' ∈ Set.Icc (0 : ℝ) 1) :
    |p * g - p' * g'| ≤ |p - p'| + |g - g'| := by
  have h : p * g - p' * g' = p * (g - g') + (p - p') * g' := by ring
  rw [h]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hp.1, abs_of_nonneg hg'.1]
  have h1 : p * |g - g'| ≤ |g - g'| := mul_le_of_le_one_left (abs_nonneg _) hp.2
  have h2 : |p - p'| * g' ≤ |p - p'| := mul_le_of_le_one_right (abs_nonneg _) hg'.2
  linarith

/-- The retained factor `ψ^cut_{r,h,c}` is Lipschitz with constant `ℓ_c 9^r 2^{-h} 2^{-c}`. -/
private theorem abs_trTreeFactor_sub_le (cut : ℕ → ℕ) (r h : ℕ) (c : ℤ) (X X' : ℝ) :
    |trTreeFactor cut r h c X - trTreeFactor cut r h c X'| ≤
      (trLipConst c : ℝ) * (9 : ℝ) ^ r * (2 : ℝ) ^ (-(h : ℤ)) * (2 : ℝ) ^ (-c) * |X - X'| := by
  by_cases hc : 2 ≤ c ∧ c ≤ (cut h : ℤ)
  · rw [trTreeFactor_of_mem hc.1 hc.2, trTreeFactor_of_mem hc.1 hc.2]
    refine (abs_trCapFactor_sub_le c _ _).trans (le_of_eq ?_)
    have h2 : (2 : ℝ) ^ ((h : ℤ) + c) = (2 : ℝ) ^ (h : ℤ) * (2 : ℝ) ^ c :=
      zpow_add₀ (by norm_num) _ _
    have h3 : 9 ^ r * X / (2 : ℝ) ^ ((h : ℤ) + c) - 9 ^ r * X' / (2 : ℝ) ^ ((h : ℤ) + c) =
        (9 ^ r * (2 : ℝ) ^ (-(h : ℤ)) * (2 : ℝ) ^ (-c)) * (X - X') := by
      rw [h2, zpow_neg, zpow_neg]
      field_simp
    rw [h3, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 9 ^ r * (2 : ℝ) ^ (-(h : ℤ)) *
      (2 : ℝ) ^ (-c))]
    ring
  · rw [trTreeFactor_of_not_mem hc, trTreeFactor_of_not_mem hc, sub_self, abs_zero]
    have := trLipConst_nonneg c
    have : (0 : ℝ) ≤ (trLipConst c : ℝ) := by exact_mod_cast this
    positivity

open Classical in
/-- **A tree cost is Lipschitz**: for every cutoff `cut`, every set of triples `W` (in particular
every bounded policy), `r, h ∈ ℕ` and real `X, X'`,
`|F^{cut,W}_{r,h}(X) - F^{cut,W}_{r,h}(X')| ≤ L^{cut,W}_{r,h} |X - X'|`. -/
@[collatz_pos_dens "lem_tr_tree_cost_lipschitz"]
theorem abs_trTreeCost_sub_le (cut : ℕ → ℕ) (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ) (X X' : ℝ) :
    |trTreeCost cut W r h X - trTreeCost cut W r h X'| ≤ trTreeLip cut W r h * |X - X'| := by
  suffices ∀ n r h, policyBound W + 1 - h = n →
      |trTreeCost cut W r h X - trTreeCost cut W r h X'| ≤ trTreeLip cut W r h * |X - X'| from
    this _ r h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r h hn
    set K := policyBound W with hK
    set P : ℕ → Prop := fun c => (r, h, c) ∈ W ∧ 1 ≤ c ∧ h + c ≤ K with hP
    set G : ℕ → ℝ → ℝ := fun c Y =>
      if _hc : P c then trTreeCost cut W (r + 1) (h + c) Y else 1 with hG
    set A : ℤ → ℝ := fun c =>
      (trLipConst c : ℝ) * (9 : ℝ) ^ r * (2 : ℝ) ^ (-(h : ℤ)) * (2 : ℝ) ^ (-c) with hA
    set B : ℕ → ℝ := fun c => if P c then trTreeLip cut W (r + 1) (h + c) else 0 with hB
    have hGmem : ∀ c Y, G c Y ∈ Set.Icc (0 : ℝ) 1 := fun c Y => by
      simp only [hG]
      split_ifs
      · exact trTreeCost_mem_Icc _ _ _ _ _
      · exact ⟨zero_le_one, le_rfl⟩
    have hGlip : ∀ c, |G c X - G c X'| ≤ B c * |X - X'| := fun c => by
      simp only [hG, hB]
      split_ifs with hc
      · exact ih _ (by omega) _ _ rfl
      · simp
    have hpt : ∀ c : ℕ, |trTreeFactor cut r h c X * G c X - trTreeFactor cut r h c X' * G c X'| ≤
        (A c + B c) * |X - X'| := fun c => by
      refine (abs_mul_sub_mul_le_of_mem_Icc
        ⟨(trTreeFactor_pos cut r h c X).le, trTreeFactor_le_one cut r h c X⟩
        (hGmem c X')).trans ?_
      rw [add_mul]
      exact add_le_add (abs_trTreeFactor_sub_le cut r h c X X') (hGlip c)
    have hF : ∀ Y, trTreeCost cut W r h Y = 1 - ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) *
        (1 - trTreeFactor cut r h c Y * G c Y) := fun Y => by
      rw [trTreeCost]
    have hdiff : trTreeCost cut W r h X - trTreeCost cut W r h X' =
        ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) *
          (trTreeFactor cut r h c X * G c X - trTreeFactor cut r h c X' * G c X') := by
      rw [hF, hF, sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    have hAsum : ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) * A c =
        (9 : ℝ) ^ r * (2 : ℝ) ^ (-(h : ℤ)) *
          ∑ c ∈ Finset.Icc (3 : ℤ) (cut h), varpi c * (trLipConst c : ℝ) * (2 : ℝ) ^ (-c) := by
      rw [Finset.mul_sum]
      have h1 : ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) * A c =
          ∑ c ∈ Finset.Icc 3 (cut h), varpi (c : ℤ) * A c := by
        refine (Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) ?_).symm
        intro c hc hc'
        simp only [Finset.mem_Icc, not_and, not_le] at hc hc'
        obtain rfl : c = 2 := by omega
        simp [hA, trLipConst_of_not_mem]
      have h2 : Finset.Icc (3 : ℤ) (cut h) = (Finset.Icc 3 (cut h)).map Nat.castEmbedding := by
        ext c
        simp only [Finset.mem_Icc, Finset.mem_map, Nat.castEmbedding_apply]
        constructor
        · rintro ⟨h₁, h₂⟩
          exact ⟨c.toNat, ⟨by omega, by omega⟩, by omega⟩
        · rintro ⟨c, ⟨h₁, h₂⟩, rfl⟩
          exact ⟨by exact_mod_cast h₁, by exact_mod_cast h₂⟩
      rw [h1, h2, Finset.sum_map]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hA, Nat.castEmbedding_apply]
      ring
    have hBsum : ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) * B c ≤
        ∑ c ∈ ((Finset.range (K + 1)).filter fun c =>
            (r, h, c) ∈ W ∧ 1 ≤ c ∧ h + c ≤ K).attach,
          varpi (c.1 : ℤ) * trTreeLip cut W (r + 1) (h + c.1) := by
      rw [Finset.sum_attach (f := fun c : ℕ => varpi (c : ℤ) * trTreeLip cut W (r + 1) (h + c))]
      simp only [hB, mul_ite, mul_zero]
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun c _ _ =>
        mul_nonneg (varpi_nonneg _) (trTreeLip_nonneg _ _ _ _)
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_range] at hc ⊢
      exact ⟨by omega, hc.2⟩
    have hLip : ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) * (A c + B c) ≤
        trTreeLip cut W r h := by
      rw [trTreeLip]
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hAsum]
      exact add_le_add_right hBsum _
    rw [hdiff]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ c ∈ Finset.Icc 2 (cut h), |varpi (c : ℤ) *
          (trTreeFactor cut r h c X * G c X - trTreeFactor cut r h c X' * G c X')|
        ≤ ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) * ((A c + B c) * |X - X'|) := by
          refine Finset.sum_le_sum fun c _ => ?_
          rw [abs_mul, abs_of_nonneg (varpi_nonneg _)]
          exact mul_le_mul_of_nonneg_left (hpt c) (varpi_nonneg _)
      _ = (∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) * (A c + B c)) * |X - X'| := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ trTreeLip cut W r h * |X - X'| :=
          mul_le_mul_of_nonneg_right hLip (abs_nonneg _)

end CollatzPosDens
