/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.StoppingTrace.TrEntryWord
public import CollatzPosDens.StoppingTrace.TrRawSum
public import CollatzPosDens.StoppingTrace.TrTreeLeaves
public import CollatzPosDens.StoppingTrace.TrTreeValid

/-!
# Every entry word begins with exactly one leaf of a valid policy

Let `v` be a point and let `W ⊆ ℕ × ℕ × ℕ` be a policy valid at `v`. Then for every entry list
`u ∈ 𝓔(v)`, with `M_u = j(Bp_{|u|}(u))`, exactly one leaf `λ ∈ 𝔏^W(0, 0)` is a prefix of the
raw word `z = raw_{M_u}(u)`.

Uniqueness holds because `𝔏^W(0, 0)` is prefix-free and two prefixes of one word are comparable.
For existence, write `σ_i` for the sum of the first `i` letters of `z` and `e_i` for the triple
`(i - 1, σ_{i-1}, z_i)`, so that `λ = (z_1, …, z_k)` is a leaf as soon as `k` is the least index
with `e_k ∉ W`. Such an index exists because `e_{M_u} ∉ W`: the raw word `z` is the
concatenation `c¹ (e¹) ⋯ c^q (e^q)` of the blocks of `u`, so it is nonempty with last letter the
closing letter `e^q ∈ {4, 5}`, and `v + (M_u, σ_{M_u}) = x_q(v, u)` is black with
`l(x_q(v, u)) > l_*(v)`. If `e_{M_u}` were in `W`, validity of `W` at `v` would make this point
not black or of height at most `l_*(v)`.

## Main results

* `CollatzPosDens.exists_mem_trTreeLeaves_prefix_append_singleton`: a word `w ++ [x]` whose last
  letter is terminal in the state reached after reading `w` has a prefix in `𝔏^W(r, h)`.
* `CollatzPosDens.mem_closing_of_flatMap_eq_append_singleton`: the last letter of the raw
  concatenation of a list of blocks is the closing letter of its last block.
* `CollatzPosDens.existsUnique_mem_trTreeLeaves_prefix_chRaw`: for `W` valid at `v`, every entry
  list `u ∈ 𝓔(v)` has a raw word beginning with exactly one leaf of `𝔏^W(0, 0)`.

## Implementation notes

A prefix `λ <+: z` of a word `z` has `|λ| ≤ |z|`, so the condition "`z` has length at least
`|λ|` and begins with `λ`" is the single relation `λ <+: z`. The result is stated for every point
`v` and every colour scale `ε`, without assuming that `v` is black. Only the last triple `e_{M_u}`
is shown to be terminal; that every continued triple `e_i` has `i < M_u` follows from this. Here
`M_u` is `(chBlockPath u u.length).1.toNat`, as in `CollatzPosDens.trRawSum`.

## References

* [Mazur, *Collatz positive density*], §9.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- A word `w ++ [x]` whose last letter `x` is terminal in the state `(r + |w|, h + Σ w)`
reached after reading `w` from `(r, h)` begins with a leaf of `𝔏^W(r, h)`. -/
lemma exists_mem_trTreeLeaves_prefix_append_singleton {W : Set (ℕ × ℕ × ℕ)} {w : List ℤ}
    {x : ℤ} {r h : ℕ} (hx : ¬PolicyMem W (r + w.length) (h + w.sum) x) :
    ∃ l ∈ trTreeLeaves W r h, l <+: w ++ [x] := by
  induction w generalizing r h with
  | nil => exact ⟨[x], singleton_mem_trTreeLeaves.2 (by simpa using hx), List.prefix_refl _⟩
  | cons c w ih =>
    by_cases hc : PolicyMem W r h c
    · obtain ⟨n, m, hm, hn, rfl⟩ := hc
      obtain rfl : n = h := Int.natCast_inj.1 hn
      obtain ⟨l, hl, hlw⟩ := ih (r := r + 1) (h := n + m) (by
        simpa [Nat.add_right_comm r 1, add_assoc, add_comm 1] using hx)
      exact ⟨(m : ℤ) :: l, (cons_mem_trTreeLeaves (ne_nil_of_mem_trTreeLeaves hl)).2
        ⟨m, rfl, hm, hl⟩, List.cons_prefix_cons.2 ⟨rfl, hlw⟩⟩
    · exact ⟨[c], singleton_mem_trTreeLeaves.2 hc, by simp [List.cons_prefix_cons]⟩

/-- The last letter of the raw concatenation `c¹ (e¹) ⋯ c^q (e^q)` of a list of blocks is the
closing letter of its last block. -/
lemma mem_closing_of_flatMap_eq_append_singleton {u : List (List ℤ × ℤ)} {S : Set ℤ}
    (hS : ∀ b ∈ u, b.2 ∈ S) {w : List ℤ} {x : ℤ}
    (h : (u.flatMap fun b ↦ b.1 ++ [b.2]) = w ++ [x]) : x ∈ S := by
  rcases List.eq_nil_or_concat' u with rfl | ⟨L, b, rfl⟩
  · simp at h
  · have h' : (L.flatMap fun b ↦ b.1 ++ [b.2]) ++ b.1 ++ [b.2] = w ++ [x] := by
      simpa [List.flatMap_append] using h
    obtain ⟨-, hx⟩ := List.append_inj' h' rfl
    simp only [List.cons.injEq, and_true] at hx
    exact hx ▸ hS b (by simp)

/-- **Every entry word begins with exactly one leaf of a valid policy.** Let `W ⊆ ℕ × ℕ × ℕ` be
valid at `v`. Then for every entry list `u ∈ 𝓔(v)`, with `M_u = j(Bp_{|u|}(u))`, there is exactly
one `λ ∈ 𝔏^W(0, 0)` such that the raw word `raw_{M_u}(u)` has length at least `|λ|` and begins
with `λ`. -/
@[collatz_pos_dens "lem_tr_tree_leaf_prefix"]
theorem existsUnique_mem_trTreeLeaves_prefix_chRaw {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    {v : ℤ × ℤ} {W : Set (ℕ × ℕ × ℕ)} (hW : TrTreeValid n ξ ε v W)
    {u : List (List ℤ × ℤ)} (hu : u ∈ trEntryWords n ξ ε v) :
    ∃! l, l ∈ trTreeLeaves W 0 0 ∧ l <+: chRaw (chBlockPath u u.length).1.toNat u := by
  have hfst := toNat_chBlockPath_fst u
  have hsnd := sum_flatMap_eq_chBlockPath_snd u
  rw [chRaw_toNat_chBlockPath_fst]
  set z := u.flatMap fun b ↦ b.1 ++ [b.2] with hz
  have hne : z ≠ [] := by
    obtain ⟨b, u', rfl⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos
      (trEntryWords_length_pos hu))
    simp [hz]
  obtain ⟨w, x, hwx⟩ := (List.eq_nil_or_concat' z).resolve_left hne
  have hx45 : x = 4 ∨ x = 5 := by
    simpa using mem_closing_of_flatMap_eq_append_singleton hu.1 hwx
  have hterm : ¬PolicyMem W ((0 : ℕ) + w.length) (((0 : ℕ) : ℤ) + w.sum) x := by
    rintro ⟨a, b, hab, ha, hb⟩
    have hb45 : b = 4 ∨ b = 5 := by omega
    have hpt : v + ((((0 + w.length) + 1 : ℕ) : ℤ), ((a + b : ℕ) : ℤ)) =
        trPath v u u.length := by
      rw [trPath_eq_add_chBlockPath]
      congr 1
      refine Prod.ext ?_ ?_
      · rw [← Int.toNat_of_nonneg (chBlockPath_fst_nonneg u u.length), hfst, hwx]
        simp
      · rw [← hsnd, hwx]
        push_cast
        simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
        omega
    rcases hW _ _ _ hab hb45 with hnb | hle
    · exact hnb (hpt ▸ trEntryWords_bkBlack hu)
    · rw [hpt] at hle
      exact absurd hle (not_le.2 (trEntryWords_bkColTop_lt hu))
  obtain ⟨l, hl, hlz⟩ := exists_mem_trTreeLeaves_prefix_append_singleton hterm
  rw [← hwx] at hlz
  exact ⟨l, ⟨hl, hlz⟩, fun l' ⟨hl', hl'z⟩ ↦
    eq_of_prefix_of_prefix_of_mem_trTreeLeaves hl' hl hl'z hlz⟩

end CollatzPosDens
