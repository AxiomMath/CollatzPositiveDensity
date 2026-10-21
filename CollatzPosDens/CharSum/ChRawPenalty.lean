/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockReward
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChPenalty
public import CollatzPosDens.CharSum.ChRaw
public import CollatzPosDens.CharSum.ChRewardBeyond
public import CollatzPosDens.CharSum.ChWhiteFactor

/-!
# The penalty of a raw prefix is a product along block points

Fix `n`, `ξ ∈ G_n` and `ε`, and let `J = ⌊n/2⌋`. Let `β = (β¹, …, βᴺ)` be blocks
`βᵏ = (cᵏ, eᵏ)` with closing letters `eᵏ ∈ {4, 5}` and nonzero block weight `bw(βᵏ) ≠ 0`. Then
the penalty of the raw word factors along the block path:
`Pen(raw_J(β)) = ∏_{k=1}^N w(Bp_k(β)) · ∏_{k=1}^N I(Bp_{k-1}(β); βᵏ)`.

Since `bw(βᵏ) ≠ 0`, no nonclosing letter lies in `{4, 5}`. The letters of block `k` occupy the
positions `j(Bp_{k-1}(β)) + 1, …, j(Bp_k(β))` of the concatenation `c¹ (e¹) ⋯ cᴺ (eᴺ)`, so by
`chWhiteFactor_mul_chInternalWeight` the factor `w(Bp_k(β)) I(Bp_{k-1}(β); βᵏ)` is the product
of the penalty factors `exp(-z_* R)` of the letters of block `k`. Letters beyond position `J`
sit at points of first coordinate `> ⌊n/2⌋`, where the paid reward vanishes, so they contribute
the factor `1`.

## Main results

* `CollatzPosDens.chPenalty_chRaw`: the factorization above.
* `CollatzPosDens.chPenaltyFrom_eq_one_of_le`: the shifted penalty starting beyond `⌊n/2⌋`
  is `1`.
* `CollatzPosDens.chPenaltyFrom_flatMap`: the shifted penalty of the full concatenation
  `c¹ (e¹) ⋯ cᴺ (eᴺ)`.

## Implementation notes

Blocks are `List ℤ × ℤ` and lists of blocks `List (List ℤ × ℤ)`, so `N = β.length`; the closing
letters are required to lie in `{4, 5}` by an explicit hypothesis. The products over
`1 ≤ k ≤ N` are taken over `k : Fin N`, indexed from `0`, so `Bp_k(β)` and `Bp_{k-1}(β)` become
`chBlockPath β (k + 1)` and `chBlockPath β k`, and `βᵏ` becomes `β[k]`. The statement
is proved for every `J ≥ ⌊n/2⌋`, not only for `J = ⌊n/2⌋`, and needs no lower bound on `N`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The shifted penalty is `1` once the starting index is at least `⌊n/2⌋`: every point it
visits has first coordinate `> ⌊n/2⌋`, where the paid reward vanishes. -/
theorem chPenaltyFrom_eq_one_of_le {n : ℕ} (ξ : ResidueGroup n) (ε : ℝ) {j : ℤ}
    (hj : ((n / 2 : ℕ) : ℤ) ≤ j) (s : ℤ) (b : List ℤ) : chPenaltyFrom n ξ ε j s b = 1 := by
  refine Finset.prod_eq_one fun i _ => ?_
  rw [chPaidReward_eq_zero_of_half_lt_bkJ ξ ε _ (by simp only [bkJ]; omega), mul_zero,
    Real.exp_zero]

/-- The shifted penalty started at `x = (j, s)` as a product over `Fin`. -/
theorem chPenaltyFrom_eq_prod_fin (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ)
    (c : List ℤ) :
    chPenaltyFrom n ξ ε j s c =
      ∏ i : Fin c.length, Real.exp (-(zStar : ℝ) *
        chPaidReward n ξ ε c[i] ((j, s) + ((i : ℤ) + 1, (c.take (i + 1)).sum))) := by
  rw [chPenaltyFrom, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.2, Option.getD_some]
  congr 3

/-- The shifted penalty of a single block `c (e)` with `e ∈ {4, 5}` and no letter of `c` in
`{4, 5}`, started at `x`, is `w(x + bpt(c, e)) I(x; (c, e))`. -/
theorem chPenaltyFrom_append_singleton (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ)
    (c : List ℤ) (e : ℤ) (hc : ∀ a ∈ c, a ∉ ({4, 5} : Set ℤ)) (he : e ∈ ({4, 5} : Set ℤ)) :
    chPenaltyFrom n ξ ε j s (c ++ [e]) =
      chWhiteFactor n ξ ε ((j, s) + chBlockPoint (c, e)) *
        chInternalWeight n ξ ε (j, s) (c, e) := by
  rw [chWhiteFactor_mul_chInternalWeight n ξ ε (j, s) (c, e)
    (fun a ha => by simpa [not_or] using hc a ha) (by simpa using he),
    chPenaltyFrom_append, chPenaltyFrom_eq_prod_fin, chPenaltyFrom_cons, chPenaltyFrom_nil,
    mul_one]
  congr 1
  have hp : ((j, s) + chBlockPoint (c, e) : ℤ × ℤ) = (j + c.length + 1, s + c.sum + e) := by
    ext <;> simp [chBlockPoint] <;> ring
  rw [hp]

/-- The shifted penalty of the full concatenation `c¹ (e¹) ⋯ cᴺ (eᴺ)` of blocks with closing
letters in `{4, 5}` and nonclosing letters outside `{4, 5}`, started at `x = (j, s)`, is
`∏_k w(x + Bp_k(β)) · ∏_k I(x + Bp_{k-1}(β); βᵏ)`. -/
theorem chPenaltyFrom_flatMap (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    {β : List (List ℤ × ℤ)} (he : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ))
    (hc : ∀ b ∈ β, ∀ a ∈ b.1, a ∉ ({4, 5} : Set ℤ)) (j s : ℤ) :
    chPenaltyFrom n ξ ε j s (β.flatMap fun b => b.1 ++ [b.2]) =
      (∏ k : Fin β.length, chWhiteFactor n ξ ε ((j, s) + chBlockPath β (k + 1))) *
        ∏ k : Fin β.length, chInternalWeight n ξ ε ((j, s) + chBlockPath β k) β[k] := by
  induction β generalizing j s with
  | nil => simp
  | cons b β ih =>
    obtain ⟨c, e⟩ := b
    have hpt : ((j, s) + chBlockPoint (c, e) : ℤ × ℤ) =
        (j + ((c ++ [e]).length : ℕ), s + (c ++ [e]).sum) := by
      ext <;> simp [chBlockPoint]
    rw [List.flatMap_cons, chPenaltyFrom_append,
      chPenaltyFrom_append_singleton n ξ ε j s c e (hc _ List.mem_cons_self)
        (he _ List.mem_cons_self),
      ih (fun b hb => he b (List.mem_cons_of_mem _ hb))
        (fun b hb => hc b (List.mem_cons_of_mem _ hb))]
    simp only [List.length_cons, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
      chBlockPath_cons_succ, chBlockPath_zero, add_zero]
    have hx : ∀ p : ℤ × ℤ, (j, s) + (chBlockPoint (c, e) + p) =
        (j + ((c ++ [e]).length : ℕ), s + (c ++ [e]).sum) + p := fun p => by
      rw [← add_assoc, hpt]
    have hg0 : ((c, e) :: β)[(0 : Fin (β.length + 1))] = (c, e) := rfl
    have hgs : ∀ x : Fin β.length, ((c, e) :: β)[x.succ] = β[x] := fun _ => rfl
    simp only [hx, hg0, hgs, hpt]
    ring

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
      rw [chPenalty_append, chPenaltyFrom_eq_one_of_le _ _ ?_, mul_one]
      rw [List.length_take_of_le h]
      omega
  have hc : ∀ b ∈ β, ∀ a ∈ b.1, a ∉ ({4, 5} : Set ℤ) :=
    fun b hb a ha h45 => hbw b hb (chBlockWeight_eq_zero_of_mem ha h45)
  rw [key, chPenalty, hz, chPenaltyFrom_flatMap n ξ ε he hc]
  simp [← Prod.zero_eq_mk]

end CollatzPosDens
