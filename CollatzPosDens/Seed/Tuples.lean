/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.Selector

/-!
# Selected central tuples

For `n ∈ ℕ`, the set `𝔗_n` of *selected central tuples* consists of the tuples
`t = (w₀, …, w_{n-1})` of words with `w_j ∈ 𝒞(b_j, K_j)` for every `j < n`, where `b_j = scale j`
and `K_j = cap j`, such that, if `n ≥ 5`, the five-block selector
`Sel(w₀, …, w₄) = fiveBlockSelector w₀ w₁ w₂ w₃ w₄` holds. Only the first five entries are
restricted by the selector; every later entry is an arbitrary word of its central family.

## Main definitions

* `CollatzPosDens.selectedTuples n`: the set `𝔗_n`, as a set of maps `Fin n → Word`.

## Main results

* `CollatzPosDens.mem_selectedTuples`: the defining membership condition.
* `CollatzPosDens.selectedTuples_finite`: the set `𝔗_n` is finite.
* `CollatzPosDens.selectedTuples_mem_centralFamily`: each entry lies in its central family.
* `CollatzPosDens.selectedTuples_selector`: for `n ≥ 5`, the selector holds.
* `CollatzPosDens.selectedTuples_restrict`: the restriction of a tuple of `𝔗_n` to its first
  `m ≤ n` entries lies in `𝔗_m`.
* `CollatzPosDens.mem_selectedTuples_of_lt_five`: for `n < 5`, membership is entrywise
  membership in the central families.

## Implementation notes

A tuple of length `n` is a map `Fin n → Word`. The conditional "if `n ≥ 5`" is a dependent
implication `∀ h : 5 ≤ n, …`, whose proof is used to index the first five entries.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The selected central tuples `𝔗_n`: tuples `t = (w₀, …, w_{n-1})` with
`w_j ∈ 𝒞(b_j, K_j)` for every `j < n` and, if `n ≥ 5`, `Sel(w₀, …, w₄)`. -/
@[collatz_pos_dens "def_s05_tuples"]
noncomputable def selectedTuples (n : ℕ) : Set (Fin n → Word) :=
  {t | (∀ j : Fin n, t j ∈ centralFamily (scale j) (cap j)) ∧
    ∀ h : 5 ≤ n, fiveBlockSelector (t ⟨0, by omega⟩) (t ⟨1, by omega⟩) (t ⟨2, by omega⟩)
      (t ⟨3, by omega⟩) (t ⟨4, by omega⟩)}

/-- Membership in the selected central tuples `𝔗_n`. -/
theorem mem_selectedTuples {n : ℕ} {t : Fin n → Word} :
    t ∈ selectedTuples n ↔ (∀ j : Fin n, t j ∈ centralFamily (scale j) (cap j)) ∧
      ∀ h : 5 ≤ n, fiveBlockSelector (t ⟨0, by omega⟩) (t ⟨1, by omega⟩) (t ⟨2, by omega⟩)
        (t ⟨3, by omega⟩) (t ⟨4, by omega⟩) :=
  Iff.rfl

/-- Each entry of a tuple of `𝔗_n` lies in its central family `𝒞(b_j, K_j)`. -/
theorem selectedTuples_mem_centralFamily {n : ℕ} {t : Fin n → Word}
    (ht : t ∈ selectedTuples n) (j : Fin n) : t j ∈ centralFamily (scale j) (cap j) :=
  ht.1 j

/-- For `n ≥ 5`, the first five entries of a tuple of `𝔗_n` satisfy the selector. -/
theorem selectedTuples_selector {n : ℕ} {t : Fin n → Word} (ht : t ∈ selectedTuples n)
    (h : 5 ≤ n) : fiveBlockSelector (t ⟨0, by omega⟩) (t ⟨1, by omega⟩) (t ⟨2, by omega⟩)
      (t ⟨3, by omega⟩) (t ⟨4, by omega⟩) :=
  ht.2 h

/-- For `n < 5`, membership in `𝔗_n` is entrywise membership in the central families. -/
theorem mem_selectedTuples_of_lt_five {n : ℕ} (hn : n < 5) {t : Fin n → Word} :
    t ∈ selectedTuples n ↔ ∀ j : Fin n, t j ∈ centralFamily (scale j) (cap j) :=
  ⟨fun ht => ht.1, fun ht => ⟨ht, fun h => absurd h (by omega)⟩⟩

/-- The restriction of a tuple of `𝔗_n` to its first `m ≤ n` entries lies in `𝔗_m`. -/
theorem selectedTuples_restrict {m n : ℕ} (hmn : m ≤ n) {t : Fin n → Word}
    (ht : t ∈ selectedTuples n) : (fun i : Fin m => t (Fin.castLE hmn i)) ∈ selectedTuples m :=
  ⟨fun j => ht.1 (Fin.castLE hmn j), fun h => ht.2 (h.trans hmn)⟩

/-- The set `𝔗_n` of selected central tuples is finite. -/
theorem selectedTuples_finite (n : ℕ) : (selectedTuples n).Finite :=
  (Set.Finite.pi (t := fun j : Fin n => centralFamily (scale j) (cap j)) fun _ =>
    centralFamily_finite _ _).subset fun _ ht => Set.mem_univ_pi.2 ht.1

/-- `𝔗_0` consists of the empty tuple. -/
@[simp]
theorem selectedTuples_zero : selectedTuples 0 = Set.univ :=
  Set.eq_univ_of_forall fun t => (mem_selectedTuples_of_lt_five (by omega)).2 (fun j => j.elim0)

end CollatzPosDens
