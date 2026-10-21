/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.StoppingTrace.TrAtoms
public import CollatzPosDens.Transfer.S02B
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Transfer.S02Xd
public import CollatzPosDens.Transfer.S02Xl

/-!
# The common fresh deviation event

Fix a level `n`, put `J = ⌊n/2⌋` and fix a Fourier index `ι : CollatzPosDens.FIndex`. Write
`𝒜_n` for the set of atoms `CollatzPosDens.trAtoms n`, `V_*(ι)` for `CollatzPosDens.Vstar ι`, and
`X_l(ι, u)`, `X_d(ι, u)` for the allowances `CollatzPosDens.Xl ι u`, `CollatzPosDens.Xd ι u`. The
common fresh deviation event `Dev^fr(ι)` is the set of fresh atoms `a = ((r, ℓ), β) ∈ 𝒜_n` whose
block word `β = (β¹, …, β^J)` deviates early: there is an integer `u` with
`1 ≤ u ≤ min(V_*(ι) - 1, J)` such that either the vertical sum is large,
`∑_{k ≤ u} l(β^k) ≥ X_l(ι, u)`, or the drift-free sum is large,
`|∑_{k ≤ u} (4 j(β^k) - l(β^k))| ≥ 4 X_d(ι, u)`. Here `j(β^k)` and `l(β^k)` are the coordinates
`CollatzPosDens.bkJ` and `CollatzPosDens.bkL` of the block point
`bpt(β^k) = CollatzPosDens.chBlockPoint β^k`.

## Main definitions

* `CollatzPosDens.c3FreshDev`: the event `Dev^fr(ι)`, a set of fresh atoms in `𝒜_n`.

## Main results

* `CollatzPosDens.mem_c3FreshDev`: the membership criterion.
* `CollatzPosDens.c3FreshDev_subset_trAtoms`: `Dev^fr(ι) ⊆ 𝒜_n`.
* `CollatzPosDens.mem_c3FreshDev_iff_blockPoint_sum`: the criterion in terms of the partial
  sums `h₁ + ⋯ + h_u` of the block points `h_k = bpt(β^k)`.
* `CollatzPosDens.mk_mem_c3FreshDev_congr`: membership does not depend on the displacement
  `(r, ℓ)`.

## Implementation notes

As in `CollatzPosDens.trAtoms`, an atom is an element of `(ℕ × ℤ) × List (List ℤ × ℤ)` and the
set carries the condition `a ∈ 𝒜_n` explicitly. The sum over `k ≤ u` is the sum over the first
`u` blocks `β.take u`; since `u ≤ J = β.length` this is exactly `β¹, …, β^u`. The allowances
`X_l` and `X_d` take rational values, so the comparisons are made in `ℚ`, the integer sums
being cast. The integer `u ≥ 1` is taken in `ℕ`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The common fresh deviation event `Dev^fr(ι)` at the Fourier index `ι`: the atoms
`a = ((r, ℓ), β) ∈ 𝒜_n` for which there is `u` with `1 ≤ u ≤ min(V_*(ι) - 1, ⌊n/2⌋)` and
`∑_{k ≤ u} l(β^k) ≥ X_l(ι, u)` or `|∑_{k ≤ u} (4 j(β^k) - l(β^k))| ≥ 4 X_d(ι, u)`, where
`(j(β^k), l(β^k)) = bpt(β^k)`. -/
@[collatz_pos_dens "def_c3_fresh_dev"]
def c3FreshDev (ι : FIndex) (n : ℕ) : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧ ∃ u : ℕ, 1 ≤ u ∧ u ≤ min (Vstar ι - 1) (n / 2) ∧
    (Xl ι u ≤ (((a.2.take u).map fun b ↦ bkL (chBlockPoint b)).sum : ℚ) ∨
      4 * Xd ι u ≤
        |(((a.2.take u).map fun b ↦ 4 * bkJ (chBlockPoint b) - bkL (chBlockPoint b)).sum : ℚ)|)}

variable {ι : FIndex} {n : ℕ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)}

/-- Membership in `Dev^fr(ι)`. -/
theorem mem_c3FreshDev :
    a ∈ c3FreshDev ι n ↔ a ∈ trAtoms n ∧ ∃ u : ℕ, 1 ≤ u ∧ u ≤ min (Vstar ι - 1) (n / 2) ∧
      (Xl ι u ≤ (((a.2.take u).map fun b ↦ bkL (chBlockPoint b)).sum : ℚ) ∨
        4 * Xd ι u ≤
          |(((a.2.take u).map fun b ↦ 4 * bkJ (chBlockPoint b) - bkL (chBlockPoint b)).sum : ℚ)|) :=
  Iff.rfl

/-- `Dev^fr(ι) ⊆ 𝒜_n`. -/
theorem c3FreshDev_subset_trAtoms (ι : FIndex) (n : ℕ) : c3FreshDev ι n ⊆ trAtoms n :=
  fun _ ha ↦ ha.1

/-- The block-point form of the deviation sums: `∑_{k ≤ u} l(β^k) = l(h₁ + ⋯ + h_u)` and
`∑_{k ≤ u} (4 j(β^k) - l(β^k)) = 4 j(h₁ + ⋯ + h_u) - l(h₁ + ⋯ + h_u)` with `h_k = bpt(β^k)`. -/
theorem mem_c3FreshDev_iff_blockPoint_sum :
    a ∈ c3FreshDev ι n ↔ a ∈ trAtoms n ∧ ∃ u : ℕ, 1 ≤ u ∧ u ≤ min (Vstar ι - 1) (n / 2) ∧
      (Xl ι u ≤ (bkL ((a.2.take u).map chBlockPoint).sum : ℚ) ∨
        4 * Xd ι u ≤ |((4 * bkJ ((a.2.take u).map chBlockPoint).sum -
          bkL ((a.2.take u).map chBlockPoint).sum : ℤ) : ℚ)|) := by
  have hL (L : List (List ℤ × ℤ)) :
      bkL (L.map chBlockPoint).sum = (L.map fun b ↦ bkL (chBlockPoint b)).sum := by
    rw [bkL_list_sum, List.map_map]; rfl
  have hD (L : List (List ℤ × ℤ)) :
      4 * bkJ (L.map chBlockPoint).sum - bkL (L.map chBlockPoint).sum =
        (L.map fun b ↦ 4 * bkJ (chBlockPoint b) - bkL (chBlockPoint b)).sum := by
    induction L with
    | nil => simp
    | cons b L ih =>
      simp only [List.map_cons, List.sum_cons, bkJ, bkL, Prod.fst_add, Prod.snd_add] at ih ⊢
      rw [← ih]; ring
  rw [mem_c3FreshDev]
  simp_rw [hD, hL]

/-- Membership of `((r, ℓ), β)` in `Dev^fr(ι)` depends on the block word `β` only. -/
theorem mk_mem_c3FreshDev_congr {r r' : ℕ} {ℓ ℓ' : ℤ} {β : List (List ℤ × ℤ)} :
    ((r, ℓ), β) ∈ c3FreshDev ι n ↔ ((r', ℓ'), β) ∈ c3FreshDev ι n :=
  Iff.rfl

end CollatzPosDens
