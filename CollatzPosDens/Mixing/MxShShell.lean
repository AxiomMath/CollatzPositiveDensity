/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import CollatzPosDens.Attr

/-!
# Offset shells

For `j ∈ ℕ` the offset shell is the half-open real interval
$$I^{\mathrm{sh}}_0 = [0, 1), \qquad I^{\mathrm{sh}}_j = [2^{j-1}, 2^j) \quad (j \ge 1).$$
The shells are pairwise disjoint and cover `[0, ∞)`, so every nonnegative real lies in exactly
one of them.

## Main definitions

* `CollatzPosDens.mxShShell`: the offset shell `I^{sh}_j`.

## Main results

* `CollatzPosDens.mem_mxShShell_zero`, `CollatzPosDens.mem_mxShShell_succ`: membership.
* `CollatzPosDens.mxShShell_subset_Ico`: `I^{sh}_j ⊆ [0, 2^j)`.
* `CollatzPosDens.mxShShell_eq_Ico_add`: `I^{sh}_j = [α_j, α_j + λ_j)` with `λ_j ≤ 2^j`.
* `CollatzPosDens.pairwise_disjoint_mxShShell`: the shells are pairwise disjoint.
* `CollatzPosDens.iUnion_mxShShell`: the shells cover `[0, ∞)`.
* `CollatzPosDens.existsUnique_mem_mxShShell`: every `x ≥ 0` lies in exactly one shell.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset shell `I^{sh}_j`: `[0, 1)` for `j = 0` and `[2^{j-1}, 2^j)` for `j ≥ 1`. -/
@[collatz_pos_dens "def_mx_sh_shell"]
def mxShShell : ℕ → Set ℝ
  | 0 => Set.Ico 0 1
  | j + 1 => Set.Ico (2 ^ j) (2 ^ (j + 1))

/-- The zeroth offset shell is `[0, 1)`. -/
@[simp]
theorem mxShShell_zero : mxShShell 0 = Set.Ico 0 1 := rfl

/-- The offset shell of index `j + 1` is `[2^j, 2^{j+1})`. -/
@[simp]
theorem mxShShell_succ (j : ℕ) : mxShShell (j + 1) = Set.Ico (2 ^ j) (2 ^ (j + 1)) := rfl

/-- `x` lies in the zeroth offset shell iff `0 ≤ x < 1`. -/
theorem mem_mxShShell_zero {x : ℝ} : x ∈ mxShShell 0 ↔ 0 ≤ x ∧ x < 1 := Iff.rfl

/-- `x` lies in the offset shell of index `j + 1` iff `2^j ≤ x < 2^{j+1}`. -/
theorem mem_mxShShell_succ {j : ℕ} {x : ℝ} :
    x ∈ mxShShell (j + 1) ↔ 2 ^ j ≤ x ∧ x < 2 ^ (j + 1) := Iff.rfl

/-- For `j ≥ 1` the offset shell is `[2^{j-1}, 2^j)`. -/
theorem mxShShell_of_ne_zero {j : ℕ} (hj : j ≠ 0) :
    mxShShell j = Set.Ico (2 ^ (j - 1)) (2 ^ j) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  simp

/-- Every shell lies in `[0, 2^j)`. -/
theorem mxShShell_subset_Ico (j : ℕ) : mxShShell j ⊆ Set.Ico 0 (2 ^ j) := by
  cases j with
  | zero => simp
  | succ i =>
    rw [mxShShell_succ]
    exact Set.Ico_subset_Ico_left (by positivity)

/-- Every element of an offset shell is nonnegative. -/
theorem nonneg_of_mem_mxShShell {j : ℕ} {x : ℝ} (hx : x ∈ mxShShell j) : 0 ≤ x :=
  (mxShShell_subset_Ico j hx).1

/-- Every element of the offset shell of index `j` is less than `2^j`. -/
theorem lt_two_pow_of_mem_mxShShell {j : ℕ} {x : ℝ} (hx : x ∈ mxShShell j) : x < 2 ^ j :=
  (mxShShell_subset_Ico j hx).2

/-- The shell written as `[α_j, α_j + λ_j)` with `(α_j, λ_j) = (0, 1)` for `j = 0` and
`(2^{j-1}, 2^{j-1})` for `j ≥ 1`; its length satisfies `λ_j ≤ 2^j`. -/
theorem mxShShell_eq_Ico_add (j : ℕ) :
    ∃ α l : ℝ, 0 ≤ α ∧ 0 < l ∧ l ≤ 2 ^ j ∧ mxShShell j = Set.Ico α (α + l) := by
  cases j with
  | zero => exact ⟨0, 1, le_rfl, one_pos, by simp, by simp⟩
  | succ i =>
    refine ⟨2 ^ i, 2 ^ i, by positivity, by positivity, ?_, ?_⟩
    · exact pow_le_pow_right₀ (by norm_num) (Nat.le_succ i)
    · rw [mxShShell_succ, pow_succ]
      congr 1
      ring

/-- A shell of positive index lies in `[2^{j-1}, ∞)`. -/
theorem le_of_mem_mxShShell_succ {j : ℕ} {x : ℝ} (hx : x ∈ mxShShell (j + 1)) : 2 ^ j ≤ x :=
  hx.1

/-- The offset shells are pairwise disjoint. -/
theorem pairwise_disjoint_mxShShell : Pairwise (Function.onFun Disjoint mxShShell) := by
  refine (pairwise_disjoint_on mxShShell).2 fun m n hmn => ?_
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
  rw [Set.disjoint_left]
  intro x hm hn
  have h1 := lt_two_pow_of_mem_mxShShell hm
  have h2 : (2 : ℝ) ^ (m + k) ≤ x := le_of_mem_mxShShell_succ (by simpa [add_assoc] using hn)
  have h3 : (2 : ℝ) ^ m ≤ 2 ^ (m + k) := pow_le_pow_right₀ (by norm_num) (Nat.le_add_right m k)
  linarith

/-- Offset shells of distinct indices are disjoint. -/
theorem disjoint_mxShShell {i j : ℕ} (h : i ≠ j) : Disjoint (mxShShell i) (mxShShell j) :=
  pairwise_disjoint_mxShShell h

/-- Every `x ≥ 0` lies in some offset shell. -/
theorem exists_mem_mxShShell {x : ℝ} (hx : 0 ≤ x) : ∃ j, x ∈ mxShShell j := by
  rcases lt_or_ge x 1 with h | h
  · exact ⟨0, hx, h⟩
  · obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near h (by norm_num : (1 : ℝ) < 2)
    exact ⟨n + 1, hn1, hn2⟩

/-- Every `x ≥ 0` lies in exactly one offset shell. -/
theorem existsUnique_mem_mxShShell {x : ℝ} (hx : 0 ≤ x) : ∃! j, x ∈ mxShShell j := by
  obtain ⟨j, hj⟩ := exists_mem_mxShShell hx
  refine ⟨j, hj, fun i hi => ?_⟩
  by_contra hne
  exact Set.disjoint_left.1 (disjoint_mxShShell hne) hi hj

/-- The offset shells cover `[0, ∞)`. -/
theorem iUnion_mxShShell : ⋃ j, mxShShell j = Set.Ici 0 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ici]
  exact ⟨fun ⟨j, hj⟩ => nonneg_of_mem_mxShShell hj, exists_mem_mxShShell⟩

end CollatzPosDens
