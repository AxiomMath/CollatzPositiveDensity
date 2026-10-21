/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.CharSum.ChBlockListMass

/-!
# The finite-horizon white products

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`; let `w` be the white factor and
`I` the internal weight of a block. For `K ∈ ℕ` and `p ∈ 𝒫`, the finite-horizon white product is
`Q^{(K)}(p) = ∑_{β ∈ 𝔅^K} (∏_{k=1}^K bw(βᵏ)) (∏_{i=0}^K w(p + Bp_i(β)))
  (∏_{k=1}^K I(p + Bp_{k-1}(β); βᵏ))`.
Since the block weights of `K`-lists of blocks form a probability distribution, this is the
expected product of the white factors at the block path points started at `p`, together with the
internal weights of the blocks read from those points.

## Main definitions

* `CollatzPosDens.chQFinite n ξ ε K p`: the finite-horizon white product `Q^{(K)}(p)`.
* `CollatzPosDens.chQFiniteTerm n ξ ε K p β`: the term of its defining series at `β ∈ 𝔅^K`.

## Main results

* `CollatzPosDens.chWhiteFactor_mul_chInternalWeight_le_one`: for a block `b` of nonzero
  weight, `w(x + bpt(b)) I(x; b) ≤ 1`.
* `CollatzPosDens.chQFiniteTerm_nonneg`, `CollatzPosDens.chQFiniteTerm_le`: each term
  of the defining series lies between `0` and `∏_k bw(βᵏ)`.
* `CollatzPosDens.summable_chQFiniteTerm`: the defining series converges.
* `CollatzPosDens.chQFinite_nonneg`: `Q^{(K)}(p) ≥ 0`.
* `CollatzPosDens.chQFinite_zero`: `Q^{(0)}(p) = w(p)`.

## Implementation notes

As in `CollatzPosDens.hasSum_prod_chBlockWeight`, a block is a pair `List ℤ × ℤ`, the
alphabet `𝔅` is the subtype of pairs whose closing letter lies in `{4, 5}`, and a list
`β ∈ 𝔅^K` is a function `β : Fin K → 𝔅`; the block path `Bp_i(β)` is evaluated on the list
`(β¹, …, β^K)`. The index `k` of the products over blocks is `0`-based, so the `1`-based
`βᵏ` and `Bp_{k-1}(β)` appear as `β k` and `Bp_k(β)` for `k : Fin K`. The sum over `𝔅^K` is a
`tsum`; its convergence is `summable_chQFiniteTerm`. The base point `p` ranges over all of
`ℤ × ℤ`, not only over `𝒫`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The term of the series defining `Q^{(K)}(p)` at a list `β ∈ 𝔅^K`:
`(∏_k bw(βᵏ)) (∏_{i=0}^K w(p + Bp_i(β))) (∏_k I(p + Bp_{k-1}(β); βᵏ))`. -/
noncomputable def chQFiniteTerm (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ)
    (β : Fin K → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) : ℝ :=
  (∏ k, chBlockWeight (β k)) *
    (∏ i ∈ Finset.range (K + 1),
      chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) i)) *
    ∏ k : Fin K, chInternalWeight n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k)

/-- The finite-horizon white product
`Q^{(K)}(p) = ∑_{β ∈ 𝔅^K} (∏_{k=1}^K bw(βᵏ)) (∏_{i=0}^K w(p + Bp_i(β)))
(∏_{k=1}^K I(p + Bp_{k-1}(β); βᵏ))`, for the white factor and internal weight of `n, ξ, ε`. -/
@[collatz_pos_dens "def_ch_Qfinite"]
noncomputable def chQFinite (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ) : ℝ :=
  ∑' β : Fin K → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
    (∏ k, chBlockWeight (β k)) *
      (∏ i ∈ Finset.range (K + 1),
        chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) i)) *
      ∏ k : Fin K, chInternalWeight n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k)

/-- `Q^{(K)}(p)` is the sum of the terms `chQFiniteTerm`. -/
theorem chQFinite_eq_tsum (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ) :
    chQFinite n ξ ε K p = ∑' β, chQFiniteTerm n ξ ε K p β :=
  rfl

/-- The terms of the series defining `Q^{(K)}(p)` are nonnegative. -/
theorem chQFiniteTerm_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ)
    (β : Fin K → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) :
    0 ≤ chQFiniteTerm n ξ ε K p β :=
  mul_nonneg (mul_nonneg (prod_chBlockWeight_nonneg β)
    (Finset.prod_nonneg fun _ _ ↦ chWhiteFactor_nonneg _ _ _ _))
    (Finset.prod_nonneg fun _ _ ↦ chInternalWeight_nonneg _ _ _ _ _)

/-- For a block `b` of nonzero weight started at `x`, the white factor at the end point
`x + bpt(b)` compensates the internal weight: `w(x + bpt(b)) I(x; b) ≤ 1`. The only letter of
`b` with a possibly negative residual reward is its closing letter, at the end point, and
there the unit reward removed from it is the white factor. -/
theorem chWhiteFactor_mul_chInternalWeight_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ)
    (x : ℤ × ℤ) {b : List ℤ × ℤ} (hb : chBlockWeight b ≠ 0) :
    chWhiteFactor n ξ ε (x + chBlockPoint b) * chInternalWeight n ξ ε x b ≤ 1 := by
  have hz : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
  have hprod : ∏ i : Fin b.1.length,
      Real.exp (-(zStar : ℝ) *
        chResidualReward n ξ ε b.1[i] (x + ((i : ℤ) + 1, (b.1.take (i + 1)).sum))) ≤ 1 := by
    refine Finset.prod_le_one₀ (fun _ _ ↦ (Real.exp_pos _).le) fun i _ ↦ ?_
    have hmem : b.1[i] ∉ ({4, 5} : Set ℤ) := fun h ↦
      hb (chBlockWeight_eq_zero_of_mem (List.getElem_mem _) h)
    have h₄ : b.1[i] ≠ 4 := fun h ↦ hmem (by simp [h])
    have h₅ : b.1[i] ≠ 5 := fun h ↦ hmem (by simp [h])
    rw [Real.exp_le_one_iff, chResidualReward_of_ne h₄ h₅, neg_mul]
    exact neg_nonpos.2 (mul_nonneg hz.le chPaidReward_nonneg)
  have hlast : chWhiteFactor n ξ ε (x + chBlockPoint b) *
      Real.exp (-(zStar : ℝ) * chResidualReward n ξ ε b.2 (x + chBlockPoint b)) ≤ 1 := by
    have hR := chPaidReward_nonneg (n := n) (ξ := ξ) (ε := ε) (c := b.2)
      (p := x + chBlockPoint b)
    by_cases hw : IsBkWhite n ξ ε (x + chBlockPoint b)
    · rw [chWhiteFactor_of_isBkWhite hw, ← Real.exp_add, Real.exp_le_one_iff]
      have : -1 ≤ chResidualReward n ξ ε b.2 (x + chBlockPoint b) := by
        unfold chResidualReward; split_ifs <;> linarith
      nlinarith
    · rw [chWhiteFactor_of_not_isBkWhite hw, one_mul, Real.exp_le_one_iff,
        chResidualReward_of_not_isBkWhite hw, neg_mul]
      exact neg_nonpos.2 (mul_nonneg hz.le hR)
  rw [chInternalWeight, mul_left_comm]
  exact (mul_le_of_le_one_left
    (mul_nonneg (chWhiteFactor_nonneg _ _ _ _) (Real.exp_pos _).le) hprod).trans hlast

/-- Each term of the series defining `Q^{(K)}(p)` is at most the weight `∏_k bw(βᵏ)`: pairing
the white factor at `Bp_k(β)` with the internal weight of `βᵏ`, each pair is at most `1`. -/
theorem chQFiniteTerm_le (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ)
    (β : Fin K → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) :
    chQFiniteTerm n ξ ε K p β ≤ ∏ k, chBlockWeight (β k) := by
  have h0 := prod_chBlockWeight_nonneg β
  by_cases hβ : ∃ k, chBlockWeight (β k) = 0
  · obtain ⟨k, hk⟩ := hβ
    rw [chQFiniteTerm, Finset.prod_eq_zero (Finset.mem_univ k) hk, zero_mul, zero_mul]
  push Not at hβ
  set B := List.ofFn fun k ↦ (β k).1
  have hpath : ∀ k : Fin K, chBlockPath B (k + 1) = chBlockPath B k + chBlockPoint (β k).1 := by
    intro k
    rw [chBlockPath_succ B (by simp [B])]
    simp [B]
  have hsplit : ∏ i ∈ Finset.range (K + 1), chWhiteFactor n ξ ε (p + chBlockPath B i) =
      chWhiteFactor n ξ ε (p + chBlockPath B 0) *
        ∏ k : Fin K, chWhiteFactor n ξ ε (p + chBlockPath B k + chBlockPoint (β k).1) := by
    rw [Finset.prod_range_succ', mul_comm, ← Fin.prod_univ_eq_prod_range]
    congr 1
    refine Finset.prod_congr rfl fun k _ ↦ ?_
    rw [hpath, add_assoc]
  have hpair : ∏ k : Fin K, chWhiteFactor n ξ ε (p + chBlockPath B k + chBlockPoint (β k).1) *
      chInternalWeight n ξ ε (p + chBlockPath B k) (β k) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ mul_nonneg (chWhiteFactor_nonneg _ _ _ _)
      (chInternalWeight_nonneg _ _ _ _ _))
      fun k _ ↦ chWhiteFactor_mul_chInternalWeight_le_one n ξ ε _ (hβ k)
  have heq : chQFiniteTerm n ξ ε K p β = (∏ k, chBlockWeight (β k)) *
      (chWhiteFactor n ξ ε (p + chBlockPath B 0) *
        ∏ k : Fin K, chWhiteFactor n ξ ε (p + chBlockPath B k + chBlockPoint (β k).1) *
          chInternalWeight n ξ ε (p + chBlockPath B k) (β k)) := by
    rw [chQFiniteTerm, hsplit, Finset.prod_mul_distrib]
    ring
  rw [heq]
  refine mul_le_of_le_one_right h0 ?_
  exact (mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ ↦ mul_nonneg
    (chWhiteFactor_nonneg _ _ _ _) (chInternalWeight_nonneg _ _ _ _ _))
    (chWhiteFactor_le_one _ _ _ _)).trans hpair

/-- The series defining `Q^{(K)}(p)` converges. -/
theorem summable_chQFiniteTerm (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ) :
    Summable (chQFiniteTerm n ξ ε K p) :=
  Summable.of_nonneg_of_le (chQFiniteTerm_nonneg n ξ ε K p) (chQFiniteTerm_le n ξ ε K p)
    (hasSum_prod_chBlockWeight K).summable

/-- The finite-horizon white product is nonnegative. -/
theorem chQFinite_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ) :
    0 ≤ chQFinite n ξ ε K p :=
  tsum_nonneg (chQFiniteTerm_nonneg n ξ ε K p)

/-- At horizon `0` the finite-horizon white product is the white factor: `Q^{(0)}(p) = w(p)`. -/
@[simp]
theorem chQFinite_zero (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (p : ℤ × ℤ) :
    chQFinite n ξ ε 0 p = chWhiteFactor n ξ ε p := by
  simp [chQFinite, tsum_fintype]

end CollatzPosDens
