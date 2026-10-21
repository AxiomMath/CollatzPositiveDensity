/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Function
public import CollatzPosDens.Attr

/-!
# Splitting subsets of `{1, …, N}` at a position

For `q ≤ N`, a subset `S ⊆ {1, …, N}` is determined by its part `S ∩ {1, …, q}` below the cut and
by its part above the cut shifted down by `q`, `{s - q : s ∈ S, s > q} ⊆ {1, …, N - q}`.
Conversely every pair `(β, T)` with `β ⊆ {1, …, q}` and `T ⊆ {1, …, N - q}` arises, from
`S = β ∪ {t + q : t ∈ T}`, and `|S| = |β| + |T|`. So the splitting map is a bijection from the
`d`-subsets of `{1, …, N}` onto the pairs `(β, T)` of this kind with `|β| + |T| = d`.

## Main definitions

* `CollatzPosDens.splitAt q S`: the pair `(S ∩ {1, …, q}, {s - q : s ∈ S, s > q})`.
* `CollatzPosDens.joinAt q β T`: the set `β ∪ {t + q : t ∈ T}`, inverse to `splitAt q`.

## Main results

* `CollatzPosDens.bijOn_splitAt`: for `q ≤ N`, `splitAt q` is a bijection from the `d`-subsets of
  `{1, …, N}` onto the pairs `(β, T)` with `β ⊆ {1, …, q}`, `T ⊆ {1, …, N - q}` and
  `|β| + |T| = d`.
* `CollatzPosDens.joinAt_splitAt`, `CollatzPosDens.splitAt_joinAt`: the two maps are mutually
  inverse on these sets.
* `CollatzPosDens.card_joinAt`: `|β ∪ {t + q : t ∈ T}| = |β| + |T|` for `β ⊆ {1, …, q}`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Split a set of positive integers at the position `q`: the pair consisting of its part
`S ∩ {1, …, q}` and of its part above `q` shifted down by `q`, `{s - q : s ∈ S, s > q}`. -/
def splitAt (q : ℕ) (S : Finset ℕ) : Finset ℕ × Finset ℕ :=
  (S ∩ Icc 1 q, (S.filter (q < ·)).image (· - q))

/-- Join a pair of sets at the position `q`: the set `β ∪ {t + q : t ∈ T}`. -/
def joinAt (q : ℕ) (β T : Finset ℕ) : Finset ℕ :=
  β ∪ T.image (· + q)

/-- The first component of `splitAt q S` is `S ∩ {1, …, q}`. -/
@[simp]
theorem splitAt_fst (q : ℕ) (S : Finset ℕ) : (splitAt q S).1 = S ∩ Icc 1 q := rfl

/-- The second component of `splitAt q S` is `{s - q : s ∈ S, s > q}`. -/
@[simp]
theorem splitAt_snd (q : ℕ) (S : Finset ℕ) :
    (splitAt q S).2 = (S.filter (q < ·)).image (· - q) := rfl

/-- `s ∈ β ∪ {t + q : t ∈ T}` if and only if `s ∈ β` or `s = t + q` for some `t ∈ T`. -/
theorem mem_joinAt {q : ℕ} {β T : Finset ℕ} {s : ℕ} :
    s ∈ joinAt q β T ↔ s ∈ β ∨ ∃ t ∈ T, t + q = s := by
  simp [joinAt]

/-- The two parts of `joinAt q β T` are disjoint when `β ⊆ {1, …, q}` and `0 ∉ T`, so its
cardinality is `|β| + |T|`. -/
theorem card_joinAt {q : ℕ} {β T : Finset ℕ} (hβ : β ⊆ Icc 1 q) (hT : 0 ∉ T) :
    (joinAt q β T).card = β.card + T.card := by
  rw [joinAt, card_union_of_disjoint, card_image_of_injective _ (add_left_injective q)]
  rw [disjoint_left]
  intro s hs ht
  obtain ⟨t, ht', rfl⟩ := mem_image.1 ht
  have h1 := (mem_Icc.1 (hβ hs)).2
  have h2 : t ≠ 0 := fun h => hT (h ▸ ht')
  omega

/-- Joining the two parts of `S` at `q` recovers `S`, provided `0 ∉ S`. -/
theorem joinAt_splitAt {q : ℕ} {S : Finset ℕ} (hS : 0 ∉ S) :
    joinAt q (splitAt q S).1 (splitAt q S).2 = S := by
  ext s
  simp only [splitAt_fst, splitAt_snd, mem_joinAt, mem_inter, mem_Icc, mem_image, mem_filter]
  constructor
  · rintro (⟨hs, -⟩ | ⟨-, ⟨a, ⟨ha, hqa⟩, rfl⟩, rfl⟩)
    · exact hs
    · rwa [Nat.sub_add_cancel hqa.le]
  · intro hs
    have h0 : s ≠ 0 := fun h => hS (h ▸ hs)
    by_cases hsq : s ≤ q
    · exact Or.inl ⟨hs, by omega, hsq⟩
    · exact Or.inr ⟨s - q, ⟨s, ⟨hs, by omega⟩, rfl⟩, by omega⟩

/-- Splitting `β ∪ {t + q : t ∈ T}` at `q` recovers `(β, T)`, provided `β ⊆ {1, …, q}` and
`0 ∉ T`. -/
theorem splitAt_joinAt {q : ℕ} {β T : Finset ℕ} (hβ : β ⊆ Icc 1 q) (hT : 0 ∉ T) :
    splitAt q (joinAt q β T) = (β, T) := by
  refine Prod.ext ?_ ?_
  · ext s
    simp only [splitAt_fst, mem_inter, mem_joinAt]
    constructor
    · rintro ⟨hs | ⟨t, ht, rfl⟩, hsq⟩
      · exact hs
      · have h2 : t ≠ 0 := fun h => hT (h ▸ ht)
        have := (mem_Icc.1 hsq).2
        omega
    · intro hs
      exact ⟨Or.inl hs, hβ hs⟩
  · ext t
    simp only [splitAt_snd, mem_image, mem_filter, mem_joinAt]
    constructor
    · rintro ⟨s, ⟨hs | ⟨t', ht', rfl⟩, hqs⟩, rfl⟩
      · have := (mem_Icc.1 (hβ hs)).2
        omega
      · rwa [Nat.add_sub_cancel]
    · intro ht
      have h2 : t ≠ 0 := fun h => hT (h ▸ ht)
      exact ⟨t + q, ⟨Or.inr ⟨t, ht, rfl⟩, by omega⟩, Nat.add_sub_cancel t q⟩

/-- **Splitting subsets at a position.** For `q ≤ N`, the map
`S ↦ (S ∩ {1, …, q}, {s - q : s ∈ S, s > q})` is a bijection from the `d`-subsets of
`{1, …, N}` onto the pairs `(β, T)` with `β ⊆ {1, …, q}`, `T ⊆ {1, …, N - q}` and
`|β| + |T| = d`. Its inverse is `(β, T) ↦ β ∪ {t + q : t ∈ T}` (`joinAt_splitAt`,
`splitAt_joinAt`). -/
@[collatz_pos_dens "lem_mx_sh_split_bij"]
theorem bijOn_splitAt {N q : ℕ} (d : ℕ) (hq : q ≤ N) :
    Set.BijOn (splitAt q) (powersetCard d (Icc 1 N) : Set (Finset ℕ))
      {p | p.1 ⊆ Icc 1 q ∧ p.2 ⊆ Icc 1 (N - q) ∧ p.1.card + p.2.card = d} := by
  have h0 : ∀ {S : Finset ℕ} {M : ℕ}, S ⊆ Icc 1 M → 0 ∉ S := fun hS h => by
    simpa using (mem_Icc.1 (hS h)).1
  refine Set.InvOn.bijOn (f' := fun p => joinAt q p.1 p.2) ⟨?_, ?_⟩ ?_ ?_
  · rintro S hS
    rw [mem_coe, mem_powersetCard] at hS
    exact joinAt_splitAt (h0 hS.1)
  · rintro ⟨β, T⟩ ⟨hβ, hT, -⟩
    exact splitAt_joinAt hβ (h0 hT)
  · rintro S hS
    rw [mem_coe, mem_powersetCard] at hS
    refine ⟨inter_subset_right, ?_, ?_⟩
    · intro t ht
      simp only [splitAt_snd, mem_image, mem_filter] at ht
      obtain ⟨s, ⟨hs, hqs⟩, rfl⟩ := ht
      have := mem_Icc.1 (hS.1 hs)
      exact mem_Icc.2 ⟨by omega, by omega⟩
    · have hS0 := h0 hS.1
      have hc := card_joinAt (q := q) (β := (splitAt q S).1) (T := (splitAt q S).2)
        inter_subset_right ?_
      · rw [joinAt_splitAt hS0, hS.2] at hc
        exact hc.symm
      simp only [splitAt_snd, mem_image, mem_filter, not_exists, not_and]
      intro s hs hqs
      omega
  · rintro ⟨β, T⟩ ⟨hβ, hT, hd⟩
    rw [mem_coe, mem_powersetCard]
    refine ⟨?_, by rw [card_joinAt hβ (h0 hT), hd]⟩
    intro s hs
    rcases mem_joinAt.1 hs with hs | ⟨t, ht, rfl⟩
    · have := mem_Icc.1 (hβ hs)
      exact mem_Icc.2 ⟨this.1, by omega⟩
    · have := mem_Icc.1 (hT ht)
      exact mem_Icc.2 ⟨by omega, by omega⟩

end CollatzPosDens
