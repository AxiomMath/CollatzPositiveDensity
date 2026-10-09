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
`ℤ × ℤ` rather than only `p ∈ 𝒫`.

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

/-- Each term of the series defining `Q^{(K)}(p)` is at most the weight `∏_k bw(βᵏ)`. -/
theorem chQFiniteTerm_le (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (K : ℕ) (p : ℤ × ℤ)
    (β : Fin K → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) :
    chQFiniteTerm n ξ ε K p β ≤ ∏ k, chBlockWeight (β k) := by
  have hw : ∏ i ∈ Finset.range (K + 1),
      chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) i) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ chWhiteFactor_nonneg _ _ _ _)
      fun _ _ ↦ chWhiteFactor_le_one _ _ _ _
  have hI : ∏ k : Fin K,
      chInternalWeight n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ chInternalWeight_nonneg _ _ _ _ _)
      fun _ _ ↦ chInternalWeight_le_one _ _ _ _ _
  have h0 := prod_chBlockWeight_nonneg β
  unfold chQFiniteTerm
  calc _ ≤ (∏ k, chBlockWeight (β k)) * 1 * 1 := by
        gcongr
        · exact Finset.prod_nonneg fun _ _ ↦ chInternalWeight_nonneg _ _ _ _ _
    _ = _ := by ring

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
  rw [chQFinite, tsum_fintype, Fintype.sum_unique]
  simp

end CollatzPosDens
