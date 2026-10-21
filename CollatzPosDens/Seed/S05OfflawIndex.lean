/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Seed.S05OfflawGrid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Find

/-!
# The grid index

For a real number `y` with `0 ≤ y ≤ ξ_6198`, the *grid index* `ι(y)` is the largest
`k ≤ 6198` with `ξ_k ≤ y`, where `(ξ_k)` is the offset grid `CollatzPosDens.offlawGrid`.
The set of such `k` is finite and contains `k = 0`, since `ξ_0 = 0`.

## Main definitions

* `CollatzPosDens.offlawIndex y`: the grid index `ι(y)`.

## Main results

* `CollatzPosDens.offlawIndex_le`: `ι(y) ≤ 6198`.
* `CollatzPosDens.offlawGrid_offlawIndex_le`: `ξ_{ι(y)} ≤ y` for `0 ≤ y`.
* `CollatzPosDens.le_offlawIndex`: `k ≤ ι(y)` whenever `k ≤ 6198` and `ξ_k ≤ y`.
* `CollatzPosDens.lt_offlawGrid_offlawIndex_succ`: `y < ξ_{ι(y)+1}` when `ι(y) < 6198`.
* `CollatzPosDens.offlawIndex_eq_iff`: `ι(y) = k` is characterised by
  `ξ_k ≤ y` and (`k = 6198` or `y < ξ_{k+1}`).
* `CollatzPosDens.offlawIndex_mono`: `ι` is monotone.
* `CollatzPosDens.offlawIndex_offlawGrid`: `ι(ξ_k) = k` for `k ≤ 6198`.

## Implementation notes

The index is defined for every real `y`, as `Nat.findGreatest` of the predicate `ξ_k ≤ y`
below `6198`; the range `0 ≤ y ≤ ξ_6198` is a hypothesis of the lemmas that need it, not of
the definition. For `y < 0` the value is `0`. The upper restriction `y ≤ ξ_6198` is never
needed: for larger `y` the maximum is `6198`.

## References

* [Mazur, *Collatz positive density*], §16.6.
-/

@[expose] public section

namespace CollatzPosDens

open Classical in
/-- **Grid index** `ι(y) = max {k ≤ 6198 : ξ_k ≤ y}` (and `0` if no such `k` exists, which
happens only for `y < 0`). -/
@[collatz_pos_dens "def_s05_offlaw_index"]
noncomputable def offlawIndex (y : ℝ) : ℕ :=
  Nat.findGreatest (fun k => ((offlawGrid k : ℚ) : ℝ) ≤ y) 6198

/-- The grid index is at most `6198`. -/
theorem offlawIndex_le (y : ℝ) : offlawIndex y ≤ 6198 :=
  Nat.findGreatest_le _

/-- Any `k ≤ 6198` with `ξ_k ≤ y` is at most the grid index. -/
theorem le_offlawIndex {y : ℝ} {k : ℕ} (hk : k ≤ 6198) (hy : ((offlawGrid k : ℚ) : ℝ) ≤ y) :
    k ≤ offlawIndex y := by
  classical
  unfold offlawIndex
  exact Nat.le_findGreatest hk hy

/-- For `0 ≤ y`, the grid point at the grid index lies below `y`. -/
theorem offlawGrid_offlawIndex_le {y : ℝ} (hy : 0 ≤ y) :
    ((offlawGrid (offlawIndex y) : ℚ) : ℝ) ≤ y := by
  classical
  unfold offlawIndex
  exact Nat.findGreatest_spec (P := fun k => ((offlawGrid k : ℚ) : ℝ) ≤ y)
    (Nat.zero_le 6198) (by simpa using hy)

/-- No grid point of index in `(ι(y), 6198]` lies below `y`. -/
theorem lt_offlawGrid_of_offlawIndex_lt {y : ℝ} {k : ℕ} (hk : offlawIndex y < k)
    (hk' : k ≤ 6198) : y < ((offlawGrid k : ℚ) : ℝ) := by
  classical
  unfold offlawIndex at hk
  exact lt_of_not_ge (Nat.findGreatest_is_greatest hk hk')

/-- Below the last index, the next grid point exceeds `y`. -/
theorem lt_offlawGrid_offlawIndex_succ {y : ℝ} (h : offlawIndex y < 6198) :
    y < ((offlawGrid (offlawIndex y + 1) : ℚ) : ℝ) :=
  lt_offlawGrid_of_offlawIndex_lt (Nat.lt_succ_self _) h

/-- Characterisation of the grid index for `0 ≤ y`: `ι(y) = k` iff `k ≤ 6198`, `ξ_k ≤ y`,
and either `k = 6198` or `y < ξ_{k+1}`. -/
theorem offlawIndex_eq_iff {y : ℝ} (hy : 0 ≤ y) {k : ℕ} :
    offlawIndex y = k ↔ k ≤ 6198 ∧ ((offlawGrid k : ℚ) : ℝ) ≤ y ∧
      (k = 6198 ∨ y < ((offlawGrid (k + 1) : ℚ) : ℝ)) := by
  constructor
  · rintro rfl
    refine ⟨offlawIndex_le y, offlawGrid_offlawIndex_le hy, ?_⟩
    rcases (offlawIndex_le y).lt_or_eq with h | h
    · exact Or.inr (lt_offlawGrid_offlawIndex_succ h)
    · exact Or.inl h
  · rintro ⟨hk, hξ, hnext⟩
    refine le_antisymm ?_ (le_offlawIndex hk hξ)
    by_contra hlt
    push Not at hlt
    have hle : ((offlawGrid (k + 1) : ℚ) : ℝ) ≤ y := by
      have hmono : offlawGrid (k + 1) ≤ offlawGrid (offlawIndex y) :=
        offlawGrid_strictMono.monotone hlt
      exact le_trans (by exact_mod_cast hmono) (offlawGrid_offlawIndex_le hy)
    rcases hnext with rfl | hnext
    · exact absurd (offlawIndex_le y) (by omega)
    · exact absurd hle (not_le.mpr hnext)

/-- The grid index is monotone: the set `{k ≤ 6198 : ξ_k ≤ y}` grows with `y`. -/
theorem offlawIndex_mono : Monotone offlawIndex := by
  classical
  intro y y' h
  unfold offlawIndex
  exact Nat.findGreatest_mono_left (fun _ hk => le_trans hk h) 6198

/-- The grid index of a grid point is its index: `ι(ξ_k) = k` for `k ≤ 6198`. -/
theorem offlawIndex_offlawGrid {k : ℕ} (hk : k ≤ 6198) :
    offlawIndex ((offlawGrid k : ℚ) : ℝ) = k := by
  have h0 : (0 : ℝ) ≤ ((offlawGrid k : ℚ) : ℝ) := by exact_mod_cast offlawGrid_nonneg k
  rw [offlawIndex_eq_iff h0]
  refine ⟨hk, le_rfl, ?_⟩
  rcases hk.lt_or_eq with h | h
  · exact Or.inr (by exact_mod_cast offlawGrid_strictMono (Nat.lt_succ_self k))
  · exact Or.inl h

/-- The grid index of a negative number is `0`. -/
theorem offlawIndex_of_neg {y : ℝ} (hy : y < 0) : offlawIndex y = 0 := by
  classical
  unfold offlawIndex
  rw [Nat.findGreatest_eq_zero_iff]
  intro k _ _ hk
  have : (0 : ℝ) ≤ ((offlawGrid k : ℚ) : ℝ) := by exact_mod_cast offlawGrid_nonneg k
  linarith

/-- `ι(0) = 0`. -/
@[simp] theorem offlawIndex_zero : offlawIndex 0 = 0 := by
  simpa using offlawIndex_offlawGrid (k := 0) (Nat.zero_le _)

end CollatzPosDens
