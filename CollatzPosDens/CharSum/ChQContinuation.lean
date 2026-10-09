/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChQ
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockWeight
public import CollatzPosDens.CharSum.ChInternalWeight
public import CollatzPosDens.CharSum.ChWhiteFactor
public import CollatzPosDens.CharSum.ChQRange
public import CollatzPosDens.CharSum.ChQRecursion

/-!
# The continuation identity for the renewal function `Q`

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`. Iterating the renewal recursion
`Q(p) = w(p) ∑_{β ∈ 𝔅} bw(β) I(p; β) Q(p + bpt(β))` `P` times gives, for every `p ∈ 𝒫`,
`Q(p) = ∑_{β ∈ 𝔅^P} (∏_{k=1}^P bw(βᵏ)) (∏_{i=0}^{P-1} w(p + Bp_i(β)))
  (∏_{k=1}^P I(p + Bp_{k-1}(β); βᵏ)) Q(p + Bp_P(β))`.
The proof is by induction on `P`. Splitting off the first block `γ` of a list in `𝔅^{P+1}`,
the block path of `(γ) β` is `Bp_0 = 0` and `Bp_{i+1} = bpt(γ) + Bp_i(β)`, so its term factors as
`w(p) bw(γ) I(p; γ)` times the term at `β` of the identity for `P` at the point `p + bpt(γ)`;
all terms are nonnegative and dominated by the summable weights `∏_k bw(βᵏ)`, so the double
sum over `(γ, β)` is the sum over `𝔅^{P+1}`, and the renewal recursion
`CollatzPosDens.chQ_eq_mul_tsum` closes the induction.

## Main results

* `CollatzPosDens.chQ_eq_tsum_blockPath_of_nonneg`: the identity under `0 ≤ j(p)`.
* `CollatzPosDens.chQ_eq_tsum_blockPath`: the continuation identity for `p ∈ 𝒫`.

## Implementation notes

As in `CollatzPosDens.chQFinite`, the alphabet `𝔅` is the subtype of pairs `List ℤ × ℤ`
whose closing letter lies in `{4, 5}`, a list `β ∈ 𝔅^P` is a function `β : Fin P → 𝔅`, and the
block path is evaluated on the list `(β¹, …, β^P)`. The index `k` of the products over blocks
is `0`-based, so `βᵏ` and `Bp_{k-1}(β)` appear as `β k` and `Bp_k(β)` for `k : Fin P`. The sum
over `𝔅^P` is a `tsum`; its terms are dominated by `∏_k bw(βᵏ)`, so it converges.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The term at `β ∈ 𝔅^P` of the continuation identity for `Q` at `p`. -/
private noncomputable def contTerm (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (P : ℕ) (p : ℤ × ℤ)
    (β : Fin P → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) : ℝ :=
  (∏ k, chBlockWeight (β k)) *
    (∏ i ∈ Finset.range P,
      chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) i)) *
    (∏ k : Fin P,
      chInternalWeight n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k)) *
    chQ n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) P)

private lemma contTerm_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (P : ℕ) (p : ℤ × ℤ)
    (β : Fin P → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) :
    0 ≤ contTerm n ξ ε P p β :=
  mul_nonneg (mul_nonneg (mul_nonneg (prod_chBlockWeight_nonneg β)
    (Finset.prod_nonneg fun _ _ ↦ chWhiteFactor_nonneg _ _ _ _))
    (Finset.prod_nonneg fun _ _ ↦ chInternalWeight_nonneg _ _ _ _ _)) (chQ_nonneg _ _ _ _)

private lemma contTerm_le (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (P : ℕ) (p : ℤ × ℤ)
    (β : Fin P → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}) :
    contTerm n ξ ε P p β ≤ ∏ k, chBlockWeight (β k) := by
  have hw : ∏ i ∈ Finset.range P,
      chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) i) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ chWhiteFactor_nonneg _ _ _ _)
      fun _ _ ↦ chWhiteFactor_le_one _ _ _ _
  have hI : ∏ k : Fin P,
      chInternalWeight n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ ↦ chInternalWeight_nonneg _ _ _ _ _)
      fun _ _ ↦ chInternalWeight_le_one _ _ _ _ _
  have hQ := chQ_le_one n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) P)
  have h0 := prod_chBlockWeight_nonneg β
  unfold contTerm
  calc _ ≤ (∏ k, chBlockWeight (β k)) * 1 * 1 * 1 := by
        gcongr
        · exact chQ_nonneg _ _ _ _
        · exact Finset.prod_nonneg fun _ _ ↦ chInternalWeight_nonneg _ _ _ _ _
    _ = _ := by ring

private lemma summable_contTerm (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (P : ℕ) (p : ℤ × ℤ) :
    Summable (contTerm n ξ ε P p) :=
  Summable.of_nonneg_of_le (contTerm_nonneg n ξ ε P p) (contTerm_le n ξ ε P p)
    (hasSum_prod_chBlockWeight P).summable

/-- The continuation identity for `Q` at any base point with `0 ≤ j(p)`. -/
theorem chQ_eq_tsum_blockPath_of_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (P : ℕ)
    {p : ℤ × ℤ} (hp : 0 ≤ bkJ p) :
    chQ n ξ ε p =
      ∑' β : Fin P → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
        (∏ k, chBlockWeight (β k)) *
          (∏ i ∈ Finset.range P,
            chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) i)) *
          (∏ k : Fin P,
            chInternalWeight n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k)) *
          chQ n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) P) := by
  change chQ n ξ ε p = ∑' β, contTerm n ξ ε P p β
  induction P generalizing p with
  | zero =>
    rw [tsum_fintype, Fintype.sum_unique]
    simp [contTerm]
  | succ P ih =>
    set e := Fin.consEquiv fun _ : Fin (P + 1) ↦ {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)}
    have hFe : ∀ x, contTerm n ξ ε (P + 1) p (e x) =
        chWhiteFactor n ξ ε p * (chBlockWeight x.1 * chInternalWeight n ξ ε p x.1 *
          contTerm n ξ ε P (p + chBlockPoint x.1) x.2) := by
      rintro ⟨a, γ⟩
      simp only [contTerm]
      rw [Finset.prod_range_succ' _ P]
      simp only [e, Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ,
        Fin.prod_univ_succ, chBlockPath_cons_succ, chBlockPath_zero, Fin.val_zero, Fin.val_succ,
        add_zero, add_assoc]
      ring
    have hS : Summable (contTerm n ξ ε (P + 1) p ∘ e) :=
      (e.summable_iff (f := contTerm n ξ ε (P + 1) p)).mpr (summable_contTerm n ξ ε (P + 1) p)
    have hp' : ∀ a : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
        0 ≤ bkJ (p + chBlockPoint a) := fun a ↦ by
      have := chBlockPoint_mem_bkPoints (a : List ℤ × ℤ)
      rw [mem_bkPoints] at this
      simp only [bkJ, Prod.fst_add] at this hp ⊢
      omega
    calc chQ n ξ ε p
        = chWhiteFactor n ξ ε p *
            ∑' a : {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
              chBlockWeight a * chInternalWeight n ξ ε p a *
                ∑' γ, contTerm n ξ ε P (p + chBlockPoint a) γ := by
          rw [chQ_eq_mul_tsum_of_nonneg n ξ ε hp]
          congr 1
          refine tsum_congr fun a ↦ ?_
          rw [← ih (hp' a)]
      _ = ∑' a, ∑' γ, contTerm n ξ ε (P + 1) p (e (a, γ)) := by
          simp only [hFe, tsum_mul_left]
      _ = ∑' x, contTerm n ξ ε (P + 1) p (e x) := hS.tsum_prod.symm
      _ = ∑' β, contTerm n ξ ε (P + 1) p β := e.tsum_eq (contTerm n ξ ε (P + 1) p)

/-- **Continuation identity for `Q`.** For every `P ∈ ℕ` and `p ∈ 𝒫`,
`Q(p) = ∑_{β ∈ 𝔅^P} (∏_{k=1}^P bw(βᵏ)) (∏_{i=0}^{P-1} w(p + Bp_i(β)))
(∏_{k=1}^P I(p + Bp_{k-1}(β); βᵏ)) Q(p + Bp_P(β))`. -/
@[collatz_pos_dens "lem_ch_Q_continuation"]
theorem chQ_eq_tsum_blockPath (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (P : ℕ)
    {p : ℤ × ℤ} (hp : p ∈ bkPoints) :
    chQ n ξ ε p =
      ∑' β : Fin P → {b : List ℤ × ℤ // b.2 ∈ ({4, 5} : Set ℤ)},
        (∏ k, chBlockWeight (β k)) *
          (∏ i ∈ Finset.range P,
            chWhiteFactor n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) i)) *
          (∏ k : Fin P,
            chInternalWeight n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) k) (β k)) *
          chQ n ξ ε (p + chBlockPath (List.ofFn fun k ↦ (β k).1) P) :=
  chQ_eq_tsum_blockPath_of_nonneg n ξ ε P (by have := mem_bkPoints.mp hp; omega)

end CollatzPosDens
