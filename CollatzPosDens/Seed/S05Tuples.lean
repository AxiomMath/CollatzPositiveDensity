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
public import CollatzPosDens.Seed.S05Selector

/-!
# Selected central tuples

For `n ∈ ℕ`, the set `𝔗_n` of *selected central tuples* consists of the tuples
`τ = (w₀, …, w_{n-1})` of words (the empty tuple if `n = 0`) with `w_j ∈ 𝒞(b_j, K_j)` for every
`0 ≤ j < n`, where `b_j` are the scales and `K_j` the caps, that satisfy the selector
`Sel_n(τ)`. The selector restricts only the entries `w_j` with `j < j_e = 29` (the generation
`selEnd`); every later entry is an arbitrary word of its central family.

## Main definitions

* `CollatzPosDens.selectedTuples n`: the set `𝔗_n`, as a set of maps `Fin n → Word`.

## Main results

* `CollatzPosDens.mem_selectedTuples`: the defining membership condition.
* `CollatzPosDens.selectedTuples_finite`: the set `𝔗_n` is finite.
* `CollatzPosDens.selectedTuples_mem_centralFamily`: each entry lies in its central family.
* `CollatzPosDens.selectedTuples_selector`: the selector holds.
* `CollatzPosDens.selectedTuples_restrict`: the restriction of a tuple of `𝔗_n` to
  `(w₀, …, w_{m-1})`, for `m ≤ n`, lies in `𝔗_m`.
* `CollatzPosDens.selectedTuples_zero`: `𝔗_0` consists of the empty tuple.

## Implementation notes

A tuple `(w₀, …, w_{n-1})` is a map `τ : Fin n → Word`, its entry `j` being required to lie in
`𝒞(b_j, K_j)`; for `n = 0` the index type is empty.

## References

* [Mazur, *Collatz positive density*, §16.1]
-/

@[expose] public section

namespace CollatzPosDens

/-- The selected central tuples `𝔗_n`: tuples `τ = (w₀, …, w_{n-1})` with `w_j ∈ 𝒞(b_j, K_j)` for
every `0 ≤ j < n`, that satisfy the selector `Sel_n(τ)`. -/
@[collatz_pos_dens "def_s05_tuples"]
noncomputable def selectedTuples (n : ℕ) : Set (Fin n → Word) :=
  {τ | (∀ k : Fin n, τ k ∈ centralFamily (scale k) (cap k)) ∧ selector n τ}

/-- Membership in the selected central tuples `𝔗_n`. -/
theorem mem_selectedTuples {n : ℕ} {τ : Fin n → Word} :
    τ ∈ selectedTuples n ↔
      (∀ k : Fin n, τ k ∈ centralFamily (scale k) (cap k)) ∧ selector n τ :=
  Iff.rfl

/-- Each entry `w_k` of a tuple of `𝔗_n` lies in its central family `𝒞(b_k, K_k)`. -/
theorem selectedTuples_mem_centralFamily {n : ℕ} {τ : Fin n → Word}
    (hτ : τ ∈ selectedTuples n) (k : Fin n) : τ k ∈ centralFamily (scale k) (cap k) :=
  hτ.1 k

/-- A tuple of `𝔗_n` satisfies the selector `Sel_n`. -/
theorem selectedTuples_selector {n : ℕ} {τ : Fin n → Word}
    (hτ : τ ∈ selectedTuples n) : selector n τ :=
  hτ.2

/-- `𝔗_0` consists of the empty tuple. -/
theorem selectedTuples_zero : selectedTuples 0 = Set.univ :=
  Set.eq_univ_of_forall fun τ => mem_selectedTuples.2 ⟨fun k => k.elim0, selector_zero τ⟩

/-- The restriction `(w₀, …, w_{m-1})` of a tuple `(w₀, …, w_{n-1})` of `𝔗_n`, for `m ≤ n`, lies
in `𝔗_m`. -/
theorem selectedTuples_restrict {m n : ℕ} (hmn : m ≤ n) {τ : Fin n → Word}
    (hτ : τ ∈ selectedTuples n) :
    (fun k : Fin m => τ (Fin.castLE hmn k)) ∈ selectedTuples m :=
  mem_selectedTuples.2 ⟨fun k => hτ.1 (Fin.castLE hmn k), hτ.2.restrict hmn⟩

/-- The set `𝔗_n` of selected central tuples is finite. -/
theorem selectedTuples_finite (n : ℕ) : (selectedTuples n).Finite :=
  (Set.Finite.pi (t := fun k : Fin n => centralFamily (scale k) (cap k))
    fun _ => centralFamily_finite _ _).subset fun _ hτ => Set.mem_univ_pi.2 hτ.1

end CollatzPosDens
