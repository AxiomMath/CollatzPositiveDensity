/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChPenalty
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.CharSum.ChRaw3Factor
public import CollatzPosDens.CharSum.ChWhiteFactor

/-!
# The penalty of a raw prefix is a product along block points

Fix `n`, `ξ ∈ G_n` and `ε`, and let `J = ⌊n/2⌋`. Let `β = (β¹, …, βᴺ)` be blocks
`βᵏ = (cᵏ, eᵏ)` with closing letters `eᵏ ∈ {4, 5}` and nonzero block weight `bw(βᵏ) ≠ 0`. Then
the penalty of the raw word factors along the block path:
`Pen(raw_J(β)) = ∏_{k=1}^N w(Bp_k(β)) · ∏_{k=1}^N I(Bp_{k-1}(β); βᵏ)`.

Since `bw(βᵏ) ≠ 0`, no nonclosing letter lies in `{4, 5}`, so the letters `4, 5` of the
concatenation `c¹ (e¹) ⋯ cᴺ (eᴺ)` are exactly the closing letters, the `k`-th one sitting at the
point `Bp_k(β)`; the letters `3` are nonclosing, and their factors `w₃` assemble into the
internal weights. Letters beyond position `J` sit at points of first coordinate `> ⌊n/2⌋`, which
are not white, so they contribute the factor `1`.

## Main results

* `CollatzPosDens.chPenalty_chRaw`: the factorization above.
* `CollatzPosDens.chPenalty_chRaw_chPenaltyFrom_eq_one_of_le`: the shifted penalty starting
  beyond `⌊n/2⌋` is `1`.
* `CollatzPosDens.chPenalty_chRaw_chPenaltyFrom_flatMap`: the shifted penalty of the full
  concatenation `c¹ (e¹) ⋯ cᴺ (eᴺ)`.

## Implementation notes

Blocks are `List ℤ × ℤ` and lists of blocks `List (List ℤ × ℤ)`, so `N = β.length`; the closing
letters are required to lie in `{4, 5}` by an explicit hypothesis. The products over
`1 ≤ k ≤ N` are taken over `k : Fin N`, indexed from `0`, so `Bp_k(β)` and `Bp_{k-1}(β)` become
`chBlockPath β (k + 1)` and `chBlockPath β k`, and `βᵏ` becomes `β[k]`. Rather than fixing
`J = ⌊n/2⌋` and assuming `N ≥ J`, the statement is proved for every `J ≥ ⌊n/2⌋`, and the
hypothesis `N ≥ J` is not needed.

## References

* [Mazur, *Collatz positive density*], §7.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The shifted penalty is `1` once the starting index is at least `⌊n/2⌋`: every point it
visits has first coordinate `> ⌊n/2⌋`, hence is not white. -/
theorem chPenalty_chRaw_chPenaltyFrom_eq_one_of_le {n : ℕ} (ξ : ResidueGroup n) (ε : ℝ) {j : ℤ}
    (hj : ((n / 2 : ℕ) : ℤ) ≤ j) (s : ℤ) (b : List ℤ) : chPenaltyFrom n ξ ε j s b = 1 := by
  have hw : ∀ i : ℕ, ¬ IsBkWhite n ξ ε (j + (i + 1 : ℕ), s + (b.take (i + 1)).sum) := by
    intro i h
    have := h.bkJ_le
    simp only [bkJ] at this
    omega
  rw [chPenaltyFrom, Finset.prod_eq_one fun i _ => chWhiteFactor_of_not_isBkWhite (hw i),
    Finset.prod_eq_one fun i _ => chRaw3Factor_of_not_isBkWhite (hw i), one_mul]

/-- On a word with no letter in `{4, 5}`, the shifted penalty started at `x` is the internal
weight `I(x; (c, e))`. -/
private theorem chPenaltyFrom_eq_chInternalWeight (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    (c : List ℤ) (hc : ∀ a ∈ c, a ∉ ({4, 5} : Set ℤ)) (j s e : ℤ) :
    chPenaltyFrom n ξ ε j s c = chInternalWeight n ξ ε (j, s) (c, e) := by
  induction c generalizing j s with
  | nil => simp
  | cons a c ih =>
    have ha : a ∉ ({4, 5} : Finset ℤ) := by
      have := hc a List.mem_cons_self
      simpa using this
    rw [chPenaltyFrom_cons, chInternalWeight_cons, ite_eq_right ha, one_mul,
      ih (fun b hb => hc b (List.mem_cons_of_mem _ hb))]
    rfl

/-- The shifted penalty of the full concatenation `c¹ (e¹) ⋯ cᴺ (eᴺ)` of blocks with closing
letters in `{4, 5}` and nonclosing letters outside `{4, 5}`, started at `x = (j, s)`, is
`∏_k w(x + Bp_k(β)) · ∏_k I(x + Bp_{k-1}(β); βᵏ)`. -/
theorem chPenalty_chRaw_chPenaltyFrom_flatMap (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    {β : List (List ℤ × ℤ)} (he : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ))
    (hc : ∀ b ∈ β, ∀ a ∈ b.1, a ∉ ({4, 5} : Set ℤ)) (j s : ℤ) :
    chPenaltyFrom n ξ ε j s (β.flatMap fun b => b.1 ++ [b.2]) =
      (∏ k : Fin β.length, chWhiteFactor n ξ ε ((j, s) + chBlockPath β (k + 1))) *
        ∏ k : Fin β.length, chInternalWeight n ξ ε ((j, s) + chBlockPath β k) β[k] := by
  induction β generalizing j s with
  | nil => simp
  | cons b β ih =>
    obtain ⟨c, e⟩ := b
    have he' : e ∈ ({4, 5} : Finset ℤ) := by
      have := he _ List.mem_cons_self
      simpa using this
    have he3 : e ≠ 3 := by
      intro h; subst h; simp at he'
    have hpt : ((j, s) + chBlockPoint (c, e) : ℤ × ℤ) =
        (j + c.length + 1, s + c.sum + e) := by
      ext <;> simp [chBlockPoint] <;> ring
    rw [List.flatMap_cons, chPenaltyFrom_append, chPenaltyFrom_append,
      chPenaltyFrom_eq_chInternalWeight n ξ ε c (hc _ List.mem_cons_self) j s e,
      ih (fun b hb => he b (List.mem_cons_of_mem _ hb))
        (fun b hb => hc b (List.mem_cons_of_mem _ hb))]
    simp only [List.length_cons, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      chBlockPath_cons_succ, chBlockPath_zero,
      add_zero, chPenaltyFrom_cons, chPenaltyFrom_nil, ite_eq_left he', ite_eq_right he3, mul_one,
      List.length_append, List.length_cons, List.length_nil, List.sum_append, List.sum_cons,
      List.sum_nil]
    have hx : ∀ p : ℤ × ℤ, (j, s) + (chBlockPoint (c, e) + p) =
        (j + (c.length : ℤ) + 1, s + c.sum + e) + p := by
      intro p; rw [← add_assoc, hpt]
    have hg0 : ((c, e) :: β)[(0 : Fin (β.length + 1))] = (c, e) := rfl
    have hgs : ∀ x : Fin β.length, ((c, e) :: β)[x.succ] = β[x] := fun _ => rfl
    simp only [hx, hg0, hgs, hpt]
    push_cast
    ring_nf

/-- **Penalty of a raw prefix.** Let `β = (β¹, …, βᴺ)` be blocks with closing letters in `{4, 5}`
and `bw(βᵏ) ≠ 0` for all `k`. Then for `J = ⌊n/2⌋`, and more generally for every `J ≥ ⌊n/2⌋`,
`Pen(raw_J(β)) = ∏_{k=1}^N w(Bp_k(β)) · ∏_{k=1}^N I(Bp_{k-1}(β); βᵏ)`. -/
@[collatz_pos_dens "lem_ch_raw_penalty"]
theorem chPenalty_chRaw {n : ℕ} (ξ : ResidueGroup n) (ε : ℝ) {J : ℕ} (hJ : n / 2 ≤ J)
    {β : List (List ℤ × ℤ)} (he : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ))
    (hbw : ∀ b ∈ β, chBlockWeight b ≠ 0) :
    chPenalty n ξ ε (chRaw J β) =
      (∏ k : Fin β.length, chWhiteFactor n ξ ε (chBlockPath β (k + 1))) *
        ∏ k : Fin β.length, chInternalWeight n ξ ε (chBlockPath β k) β[k] := by
  set z := β.flatMap fun b => b.1 ++ [b.2] with hz
  have key : chPenalty n ξ ε (chRaw J β) = chPenalty n ξ ε z := by
    rw [chRaw_def, ← hz]
    rcases le_total z.length J with h | h
    · rw [List.take_of_length_le h]
    · conv_rhs => rw [← List.take_append_drop J z]
      rw [chPenalty_append, chPenalty_chRaw_chPenaltyFrom_eq_one_of_le _ _ ?_, mul_one]
      rw [List.length_take_of_le h]
      omega
  have hc : ∀ b ∈ β, ∀ a ∈ b.1, a ∉ ({4, 5} : Set ℤ) :=
    fun b hb a ha h45 => hbw b hb (chBlockWeight_eq_zero_of_mem ha h45)
  rw [key, chPenalty, hz, chPenalty_chRaw_chPenaltyFrom_flatMap n ξ ε he hc]
  simp [← Prod.zero_eq_mk]

end CollatzPosDens
