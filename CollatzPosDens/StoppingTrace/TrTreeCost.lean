/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.StoppingTrace.TrTreeFactor
public import CollatzPosDens.StoppingTrace.TrTreeLip
public import CollatzPosDens.StoppingTrace.TrTreePolicy

/-!
# The tree cost

Let `cut : ℕ → ℕ` and let `W` be a bounded policy. For `r, h ∈ ℕ` and a real number `X`, the
tree cost `F^{cut,W}_{r,h}(X)` is defined, for all `r` at once, by downward recursion on `h`:
`F^{cut,W}_{r,h}(X) = 1 - ∑_{c=2}^{cut(h)} ϖ(c) (1 - ψ^cut_{r,h,c}(X) G_{r,h,c}(X))`,
where `G_{r,h,c}(X) = F^{cut,W}_{r+1,h+c}(X)` if `(r, h, c) ∈ W` and `G_{r,h,c}(X) = 1`
otherwise. Here `ϖ` is the Pascal holding-time law `CollatzPosDens.varpi` and `ψ^cut_{r,h,c}`
the retained factor `CollatzPosDens.trTreeFactor`. The recursion is well founded because every
`(r, h, c) ∈ W` has `c ≥ 2` and `h + c` bounded. A triple `(r, h, c) ∈ W` thus refines the
child `c` of the node `(r, h)` by a further level, while a child outside `W` is charged only its
retained factor.

## Main definitions

* `CollatzPosDens.trTreeCost`: the tree cost `F^{cut,W}_{r,h}(X)`.

## Main results

* `CollatzPosDens.trTreeCost_eq`: the defining recursion of the tree cost.
* `CollatzPosDens.trTreeCost_of_forall_notMem`: a node without children in `W` is charged
  only its retained factors.
* `CollatzPosDens.trTreeCost_nonneg`, `CollatzPosDens.trTreeCost_le_one`:
  `0 ≤ F^{cut,W}_{r,h}(X) ≤ 1`.

## Implementation notes

The continuation lengths `c` of a policy are natural numbers, cast to `ℤ` in `ϖ(c)` and in
`ψ^cut_{r,h,c}`. The recursion is by well-founded recursion on `K + 1 - h`, where
`K = CollatzPosDens.policyBound W`; a child `c` is refined only when `(r, h, c) ∈ W` and
`h + c ≤ K`, which for a bounded policy is no restriction. For a set `W` that is not a bounded
policy the value is unspecified.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Classical in
/-- The tree cost: `F^{cut,W}_{r,h}(X) = 1 - ∑_{c=2}^{cut(h)} ϖ(c) (1 - ψ^cut_{r,h,c}(X) G)`,
where `G = F^{cut,W}_{r+1,h+c}(X)` if `(r, h, c) ∈ W` and `G = 1` otherwise, by downward
recursion on `h`. -/
@[collatz_pos_dens "def_tr_tree_cost"]
noncomputable def trTreeCost (cut : ℕ → ℕ) (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ) (X : ℝ) : ℝ :=
  1 - ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) *
    (1 - trTreeFactor cut r h c X *
      if _hc : (r, h, c) ∈ W ∧ 1 ≤ c ∧ h + c ≤ policyBound W then
        trTreeCost cut W (r + 1) (h + c) X
      else 1)
termination_by policyBound W + 1 - h
decreasing_by omega

/-- The defining recursion of the tree cost: `F^{cut,W}_{r,h}(X) = 1 -
∑_{c=2}^{cut(h)} ϖ(c) (1 - ψ^cut_{r,h,c}(X) G_{r,h,c}(X))`, where
`G_{r,h,c}(X) = F^{cut,W}_{r+1,h+c}(X)` if `(r, h, c) ∈ W` and `1` otherwise. -/
@[collatz_pos_dens "def_tr_tree_cost"]
theorem trTreeCost_eq {cut : ℕ → ℕ} {W : Set (ℕ × ℕ × ℕ)} (hW : IsBoundedPolicy W)
    [DecidablePred (· ∈ W)] (r h : ℕ) (X : ℝ) :
    trTreeCost cut W r h X =
      1 - ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) *
        (1 - trTreeFactor cut r h c X *
          if (r, h, c) ∈ W then trTreeCost cut W (r + 1) (h + c) X else 1) := by
  rw [trTreeCost]
  congr 1
  refine Finset.sum_congr rfl fun c hc => ?_
  have hc2 := (Finset.mem_Icc.mp hc).1
  by_cases hrc : (r, h, c) ∈ W
  · have := (hW.le_policyBound hrc).2
    simp only at this
    rw [dite_eq_left_of_eq_true (eq_true ⟨hrc, by omega, this⟩),
      ite_eq_left_of_eq_true _ _ (eq_true hrc)]
  · rw [dite_eq_right_of_eq_false (eq_false fun h' => hrc h'.1),
      ite_eq_right_of_eq_false _ _ (eq_false hrc)]

/-- A node `(r, h)` without children in `W` is charged only its retained factors:
`F^{cut,W}_{r,h}(X) = 1 - ∑_{c=2}^{cut(h)} ϖ(c) (1 - ψ^cut_{r,h,c}(X))`. -/
theorem trTreeCost_of_forall_notMem {cut : ℕ → ℕ} {W : Set (ℕ × ℕ × ℕ)}
    (hW : IsBoundedPolicy W) {r h : ℕ} (hrh : ∀ c, (r, h, c) ∉ W) (X : ℝ) :
    trTreeCost cut W r h X =
      1 - ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) * (1 - trTreeFactor cut r h c X) := by
  classical
  rw [trTreeCost_eq hW]
  simp [hrh]

/-- The Pascal weights of the lengths `2 ≤ c ≤ n` sum to at most `1`. -/
private theorem sum_Icc_varpi_le_one (n : ℕ) :
    ∑ c ∈ Finset.Icc 2 n, varpi (c : ℤ) ≤ 1 := by
  have h := sum_le_hasSum (Finset.range (n - 1)) (fun i _ => varpi_nonneg _)
    hasSum_varpi_add_two
  refine le_trans (le_of_eq ?_) h
  rcases Nat.lt_or_ge n 1 with hn | hn
  · obtain rfl : n = 0 := by omega
    simp
  · rw [Finset.range_eq_Ico]
    have := Finset.sum_Ico_add' (fun c : ℕ => varpi (c : ℤ)) 0 (n - 1) 2
    simp only [Nat.cast_add, Nat.cast_ofNat, zero_add] at this
    rw [this, show n - 1 + 2 = n + 1 by omega]
    rfl

open Classical in
/-- The tree cost lies in `[0, 1]`. -/
private theorem trTreeCost_mem_Icc (cut : ℕ → ℕ) (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ) (X : ℝ) :
    0 ≤ trTreeCost cut W r h X ∧ trTreeCost cut W r h X ≤ 1 := by
  suffices ∀ n r h, policyBound W + 1 - h = n →
      0 ≤ trTreeCost cut W r h X ∧ trTreeCost cut W r h X ≤ 1 from this _ r h rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro r h hn
    have hterm : ∀ c ∈ Finset.Icc 2 (cut h),
        0 ≤ 1 - trTreeFactor cut r h c X *
          (if _hc : (r, h, c) ∈ W ∧ 1 ≤ c ∧ h + c ≤ policyBound W then
            trTreeCost cut W (r + 1) (h + c) X else 1) ∧
        1 - trTreeFactor cut r h c X *
          (if _hc : (r, h, c) ∈ W ∧ 1 ≤ c ∧ h + c ≤ policyBound W then
            trTreeCost cut W (r + 1) (h + c) X else 1) ≤ 1 := by
      intro c _
      have hψ0 := (trTreeFactor_pos cut r h c X).le
      have hψ1 := trTreeFactor_le_one cut r h c X
      have hG : 0 ≤ (if _hc : (r, h, c) ∈ W ∧ 1 ≤ c ∧ h + c ≤ policyBound W then
            trTreeCost cut W (r + 1) (h + c) X else 1) ∧
          (if _hc : (r, h, c) ∈ W ∧ 1 ≤ c ∧ h + c ≤ policyBound W then
            trTreeCost cut W (r + 1) (h + c) X else (1 : ℝ)) ≤ 1 := by
        split_ifs with hc
        · exact ih _ (by omega) _ _ rfl
        · exact ⟨zero_le_one, le_rfl⟩
      constructor
      · nlinarith [mul_le_mul hψ1 hG.2 hG.1 zero_le_one]
      · nlinarith [mul_nonneg hψ0 hG.1]
    rw [trTreeCost]
    constructor
    · have hle : ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) *
            (1 - trTreeFactor cut r h c X *
              (if _hc : (r, h, c) ∈ W ∧ 1 ≤ c ∧ h + c ≤ policyBound W then
                trTreeCost cut W (r + 1) (h + c) X else 1)) ≤
          ∑ c ∈ Finset.Icc 2 (cut h), varpi (c : ℤ) :=
        Finset.sum_le_sum fun c hc =>
          mul_le_of_le_one_right (varpi_nonneg _) (hterm c hc).2
      linarith [sum_Icc_varpi_le_one (cut h)]
    · have := Finset.sum_nonneg fun (c : ℕ) hc =>
        mul_nonneg (varpi_nonneg (c : ℤ)) (hterm c hc).1
      linarith

/-- The tree cost is nonnegative. -/
theorem trTreeCost_nonneg (cut : ℕ → ℕ) (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ) (X : ℝ) :
    0 ≤ trTreeCost cut W r h X :=
  (trTreeCost_mem_Icc cut W r h X).1

/-- The tree cost is at most `1`. -/
theorem trTreeCost_le_one (cut : ℕ → ℕ) (W : Set (ℕ × ℕ × ℕ)) (r h : ℕ) (X : ℝ) :
    trTreeCost cut W r h X ≤ 1 :=
  (trTreeCost_mem_Icc cut W r h X).2

end CollatzPosDens
