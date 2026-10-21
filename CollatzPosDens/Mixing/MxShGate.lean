/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShHeight
public import CollatzPosDens.Mixing.MxShShell
public import CollatzPosDens.Mixing.MxShSubsetOffset

/-!
# Exposed patterns of a gate

For natural numbers `n`, `d` and `j`, the *exposed patterns* of the gate `(d, j)` of the shell cut
are the `d`-element subsets `β` of `{1, …, H^{sh}_n - 1}`, where `H^{sh}_n = ⌈n log₂ 3⌉` is the
crossing height, whose offset `Of(β)` lies in the shell `I^{sh}_j`:
$$\mathrm{Hd}^{\mathrm{sh}}_n(d, j) = \{\beta \subseteq \{1, \dots, H^{\mathrm{sh}}_n - 1\} :
  |\beta| = d,\ \mathrm{Of}(\beta) \in I^{\mathrm{sh}}_j\}.$$
Since offsets are nonnegative and the shells partition `[0, ∞)`, for fixed `(n, d)` the sets
`Hd^{sh}_n(d, j)`, `j ∈ ℕ`, partition the `d`-element subsets of `{1, …, H^{sh}_n - 1}`.

## Main definitions

* `CollatzPosDens.shRetainedHeads`: the finite set `Hd^{sh}_n(d, j)` of exposed patterns.

## Main results

* `CollatzPosDens.mem_shRetainedHeads`: the defining membership condition.
* `CollatzPosDens.shRetainedHeads_subset_powersetCard`: `Hd^{sh}_n(d, j)` consists of
  `d`-element subsets of `{1, …, H^{sh}_n - 1}`.
* `CollatzPosDens.card_shRetainedHeads_le_choose`: `#Hd^{sh}_n(d, j) ≤ C(H^{sh}_n - 1, d)`.
* `CollatzPosDens.disjoint_shRetainedHeads`: the sets are pairwise disjoint in `j`.
* `CollatzPosDens.existsUnique_mem_shRetainedHeads`: every `d`-element subset of
  `{1, …, H^{sh}_n - 1}` lies in exactly one of them.

## Implementation notes

The source states the definition for `n ≥ 1`; the Lean definition takes all natural numbers.
The subset offset is rational and the shells are real intervals, so the condition reads
`(Of(β) : ℝ) ∈ mxShShell j`. The exposed patterns form a `Finset` of `Finset ℕ`, so that their
number is the cardinality `#Hd^{sh}_n(d, j)`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

open Classical in
/-- The set `Hd^{sh}_n(d, j)` of *exposed patterns* of the gate `(d, j)`: the `d`-element subsets
`β ⊆ {1, …, H^{sh}_n - 1}` whose offset `Of(β)` lies in the shell `I^{sh}_j`. -/
@[collatz_pos_dens "def_mx_sh_gate"]
noncomputable def shRetainedHeads (n d j : ℕ) : Finset (Finset ℕ) :=
  {β ∈ (Icc 1 (shHeight n - 1)).powersetCard d | ((setOffset β : ℚ) : ℝ) ∈ mxShShell j}

/-- Membership in `Hd^{sh}_n(d, j)`: `β ⊆ {1, …, H^{sh}_n - 1}`, `|β| = d` and
`Of(β) ∈ I^{sh}_j`. -/
theorem mem_shRetainedHeads {n d j : ℕ} {β : Finset ℕ} :
    β ∈ shRetainedHeads n d j ↔
      β ⊆ Icc 1 (shHeight n - 1) ∧ #β = d ∧ ((setOffset β : ℚ) : ℝ) ∈ mxShShell j := by
  classical
  simp [shRetainedHeads, mem_powersetCard, and_assoc]

/-- The exposed patterns are `d`-element subsets of `{1, …, H^{sh}_n - 1}`. -/
theorem shRetainedHeads_subset_powersetCard (n d j : ℕ) :
    shRetainedHeads n d j ⊆ (Icc 1 (shHeight n - 1)).powersetCard d := by
  classical
  exact filter_subset _ _

/-- An exposed pattern of the gate `(d, j)` is contained in `{1, …, H^{sh}_n - 1}`. -/
theorem subset_Icc_of_mem_shRetainedHeads {n d j : ℕ} {β : Finset ℕ}
    (hβ : β ∈ shRetainedHeads n d j) : β ⊆ Icc 1 (shHeight n - 1) :=
  (mem_shRetainedHeads.1 hβ).1

/-- An exposed pattern of the gate `(d, j)` has exactly `d` elements. -/
theorem card_eq_of_mem_shRetainedHeads {n d j : ℕ} {β : Finset ℕ}
    (hβ : β ∈ shRetainedHeads n d j) : #β = d :=
  (mem_shRetainedHeads.1 hβ).2.1

/-- The offset `Of(β)` of an exposed pattern `β` of the gate `(d, j)` lies in the shell
`I^{sh}_j`. -/
theorem setOffset_mem_mxShShell_of_mem_shRetainedHeads {n d j : ℕ} {β : Finset ℕ}
    (hβ : β ∈ shRetainedHeads n d j) : ((setOffset β : ℚ) : ℝ) ∈ mxShShell j :=
  (mem_shRetainedHeads.1 hβ).2.2

/-- There are at most `C(H^{sh}_n - 1, d)` exposed patterns. -/
theorem card_shRetainedHeads_le_choose (n d j : ℕ) :
    #(shRetainedHeads n d j) ≤ (shHeight n - 1).choose d := by
  refine (card_le_card (shRetainedHeads_subset_powersetCard n d j)).trans ?_
  simp

/-- For fixed `(n, d)` the sets of exposed patterns are pairwise disjoint in `j`. -/
theorem disjoint_shRetainedHeads (n d : ℕ) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (shRetainedHeads n d i) (shRetainedHeads n d j) := by
  rw [Finset.disjoint_left]
  exact fun _ hi hj => Set.disjoint_left.1 (disjoint_mxShShell hij)
    (setOffset_mem_mxShShell_of_mem_shRetainedHeads hi)
    (setOffset_mem_mxShShell_of_mem_shRetainedHeads hj)

/-- Every `d`-element subset of `{1, …, H^{sh}_n - 1}` is an exposed pattern of exactly one gate
`(d, j)`. -/
theorem existsUnique_mem_shRetainedHeads {n d : ℕ} {β : Finset ℕ}
    (hβ : β ∈ (Icc 1 (shHeight n - 1)).powersetCard d) : ∃! j, β ∈ shRetainedHeads n d j := by
  rw [mem_powersetCard] at hβ
  obtain ⟨j, hj, huniq⟩ := existsUnique_mem_mxShShell (x := ((setOffset β : ℚ) : ℝ))
    (by exact_mod_cast setOffset_nonneg β)
  exact ⟨j, mem_shRetainedHeads.2 ⟨hβ.1, hβ.2, hj⟩,
    fun i hi => huniq i (setOffset_mem_mxShShell_of_mem_shRetainedHeads hi)⟩

end CollatzPosDens
