/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascalTotal
public import CollatzPosDens.StoppingTrace.TrTreeCost
public import CollatzPosDens.StoppingTrace.TrTreeLeaves
public import Mathlib.Algebra.Order.Group.Indicator

/-!
# A tree cost is a sum over its leaves

Let `cut : ℕ → ℕ` and let `W` be a bounded policy with `c ≤ cut(h)` for every `(r, h, c) ∈ W`.
For `r, h ∈ ℕ` and a real number `X`, the tree cost `F^{cut,W}_{r,h}(X)` is the sum, over the
leaves `λ ∈ 𝔏^W(r, h)`, of the nonnegative weights
`∏_{i=1}^{|λ|} ϖ(λᵢ) ψ^cut_{r+i-1, h+λ₁+⋯+λᵢ₋₁, λᵢ}(X)`.

The proof is by downward induction on `h`, for all `r` at once. The leaves at `(r, h)` are the
one-letter words `(c)` with `(r, h, c) ∉ W` and the words `(c) λ'` with `(r, h, c) ∈ W` and
`λ' ∈ 𝔏^W(r + 1, h + c)`, so by induction the leaf sum is
`∑_{c ∈ ℤ} ϖ(c) ψ^cut_{r,h,c}(X) G_{r,h,c}(X)`. Since `ϖ(c) = 0` for `c ≤ 1`, since
`ψ^cut_{r,h,c} = G_{r,h,c} = 1` for `c > cut(h)`, and since `∑_c ϖ(c) = 1`, this is
`1 - ∑_{c=2}^{cut(h)} ϖ(c) (1 - ψ^cut_{r,h,c}(X) G_{r,h,c}(X)) = F^{cut,W}_{r,h}(X)`.

## Main results

* `CollatzPosDens.hasSum_trTreeLeaves_trTreeCost`: the leaf expansion of the tree cost.
* `CollatzPosDens.trTreeLeaves_term_nonneg`: its terms are nonnegative.

## Implementation notes

The letters of a leaf are integers, while the retained factor `ψ^cut_{r,h,c}` takes a natural
height `h`. The height `h + λ₁ + ⋯ + λᵢ₋₁` at which the `i`-th letter of a leaf is read is a
natural number, since the letters `λ₁, …, λᵢ₋₁` are continued, hence lie in `W`; it is written
`Int.toNat (h + λ₁ + ⋯ + λᵢ₋₁)`. Letters are indexed from `0`, so the factor of index `i` is the
factor of the letter `λᵢ₊₁`. The series is a `HasSum` over the subtype of leaves; its terms being
nonnegative, it converges unconditionally.

## References

* [Mazur, *Collatz positive density*], Section 9.7.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The weight `∏_{i} ϖ(λᵢ) ψ^cut_{r+i-1, h+λ₁+⋯+λᵢ₋₁, λᵢ}(X)` of a word `λ` read from `(r, h)`. -/
private noncomputable def leafTerm (cut : ℕ → ℕ) (r h : ℕ) (X : ℝ) (l : List ℤ) : ℝ :=
  ∏ i : Fin l.length,
    varpi l[i] * trTreeFactor cut (r + i) ((h : ℤ) + (l.take i).sum).toNat l[i] X

private lemma leafTerm_nonneg (cut : ℕ → ℕ) (r h : ℕ) (X : ℝ) (l : List ℤ) :
    0 ≤ leafTerm cut r h X l :=
  Finset.prod_nonneg fun _ _ => mul_nonneg (varpi_nonneg _) (trTreeFactor_pos _ _ _ _ _).le

private lemma leafTerm_cons (cut : ℕ → ℕ) (r h : ℕ) (X : ℝ) (c : ℤ) (t : List ℤ) :
    leafTerm cut r h X (c :: t) = varpi c * trTreeFactor cut r h c X *
      ∏ i : Fin t.length,
        varpi t[i] * trTreeFactor cut (r + 1 + i) ((h : ℤ) + c + (t.take i).sum).toNat t[i] X := by
  unfold leafTerm
  refine (Fin.prod_univ_succ (n := t.length) _).trans ?_
  simp only [Fin.val_zero, List.take_zero, List.sum_nil, add_zero, Int.toNat_natCast,
    Fin.val_succ, List.take_succ_cons, List.sum_cons, List.getElem_cons_succ,
    List.getElem_cons_zero, Fin.getElem_fin]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← add_assoc (h : ℤ), show r + (i + 1) = r + 1 + i by omega]

private lemma leafTerm_singleton (cut : ℕ → ℕ) (r h : ℕ) (X : ℝ) (c : ℤ) :
    leafTerm cut r h X [c] = varpi c * trTreeFactor cut r h c X := by
  rw [leafTerm_cons]
  simp

private lemma leafTerm_natCast_cons (cut : ℕ → ℕ) (r h : ℕ) (X : ℝ) (m : ℕ) (t : List ℤ) :
    leafTerm cut r h X ((m : ℤ) :: t) =
      varpi m * trTreeFactor cut r h m X * leafTerm cut (r + 1) (h + m) X t := by
  rw [leafTerm_cons]
  rfl

open Classical in
/-- The one-step expansion `F^{cut,W}_{r,h}(X) = ∑_{c ∈ ℤ} ϖ(c) ψ^cut_{r,h,c}(X) G_{r,h,c}(X)`. -/
private lemma hasSum_varpi_mul_trTreeCost {cut : ℕ → ℕ} {W : Set (ℕ × ℕ × ℕ)}
    (hW : IsBoundedPolicy W) (hcut : ∀ p ∈ W, p.2.2 ≤ cut p.2.1) (r h : ℕ) (X : ℝ) :
    HasSum (fun c : ℤ => varpi c * (trTreeFactor cut r h c X *
        if PolicyMem W r h c then trTreeCost cut W (r + 1) (h + c.toNat) X else 1))
      (trTreeCost cut W r h X) := by
  set G : ℤ → ℝ := fun c =>
    if PolicyMem W r h c then trTreeCost cut W (r + 1) (h + c.toNat) X else 1 with hG
  set g : ℤ → ℝ := fun c => varpi c * (1 - trTreeFactor cut r h c X * G c) with hg
  set S : Finset ℤ := (Finset.Icc 2 (cut h)).map Nat.castEmbedding with hS
  have hzero : ∀ c ∉ S, g c = 0 := by
    intro c hc
    rcases le_or_gt c 1 with hc1 | hc1
    · simp [hg, varpi_of_le_one hc1]
    have hcut' : (cut h : ℤ) < c := by
      by_contra hle
      refine hc (Finset.mem_map.2 ⟨c.toNat, Finset.mem_Icc.2 ⟨by omega, by omega⟩, ?_⟩)
      simp only [Nat.castEmbedding_apply]
      omega
    have hψ : trTreeFactor cut r h c X = 1 := trTreeFactor_of_not_mem (by omega) X
    have hGc : G c = 1 := by
      have hn : ¬ PolicyMem W r h c := by
        rintro ⟨n, m, hm, hn, rfl⟩
        obtain rfl : n = h := by exact_mod_cast hn
        have := hcut _ hm
        simp only at this
        omega
      simp [hG, hn]
    simp [hg, hψ, hGc]
  have h1 := hasSum_varpi.sub (hasSum_sum_of_ne_finset_zero hzero)
  convert h1 using 1
  · funext c
    simp only [hg, hG]
    ring
  · rw [trTreeCost_eq hW, hS, Finset.sum_map]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [hg, hG, policyMem_natCast]

/-- The leaf sum, as an `ℝ≥0∞`-valued series over all integer words. -/
private lemma tsum_leafTerm {cut : ℕ → ℕ} {W : Set (ℕ × ℕ × ℕ)}
    (hW : IsBoundedPolicy W) (hcut : ∀ p ∈ W, p.2.2 ≤ cut p.2.1) (X : ℝ) :
    ∀ n r h, policyBound W + 1 - h = n →
      ∑' l : List ℤ, ENNReal.ofReal ((trTreeLeaves W r h).indicator (leafTerm cut r h X) l) =
        ENNReal.ofReal (trTreeCost cut W r h X) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro r h hn
  set F : List ℤ → ℝ≥0∞ :=
    fun l => ENNReal.ofReal ((trTreeLeaves W r h).indicator (leafTerm cut r h X) l) with hF
  have hinj : Function.Injective (fun p : ℤ × List ℤ => p.1 :: p.2) := by
    rintro ⟨a, s⟩ ⟨b, t⟩ hab
    simp only [List.cons.injEq] at hab
    rw [hab.1, hab.2]
  have hsupp : Function.support F ⊆ Set.range (fun p : ℤ × List ℤ => p.1 :: p.2) := by
    intro l hl
    rcases l with _ | ⟨c, t⟩
    · exact absurd (by simp [hF]) hl
    · exact ⟨(c, t), rfl⟩
  rw [← hinj.tsum_eq hsupp, show (∑' p : ℤ × List ℤ, F (p.1 :: p.2)) =
    ∑' (c : ℤ) (t : List ℤ), F (c :: t) from ENNReal.tsum_prod (f := fun c t => F (c :: t))]
  have hinner : ∀ c : ℤ, ∑' t : List ℤ, F (c :: t) =
      ENNReal.ofReal (varpi c * (trTreeFactor cut r h c X *
        if PolicyMem W r h c then trTreeCost cut W (r + 1) (h + c.toNat) X else 1)) := by
    intro c
    by_cases hc : PolicyMem W r h c
    · obtain ⟨n', m, hm, hn', rfl⟩ := hc
      obtain rfl : n' = h := by exact_mod_cast hn'
      have hK := hW.le_policyBound hm
      simp only at hK
      have hterm : ∀ t : List ℤ, F ((m : ℤ) :: t) =
          ENNReal.ofReal (varpi m * trTreeFactor cut r n' m X) *
            ENNReal.ofReal ((trTreeLeaves W (r + 1) (n' + m)).indicator
              (leafTerm cut (r + 1) (n' + m) X) t) := by
        intro t
        rcases eq_or_ne t [] with rfl | ht
        · have : [(m : ℤ)] ∉ trTreeLeaves W r n' := by
            rw [singleton_mem_trTreeLeaves, not_not, policyMem_natCast]
            exact hm
          simp [hF, this]
        · have hiff : (m : ℤ) :: t ∈ trTreeLeaves W r n' ↔
              t ∈ trTreeLeaves W (r + 1) (n' + m) := by
            rw [cons_mem_trTreeLeaves ht]
            constructor
            · rintro ⟨m', hm', -, ht'⟩
              obtain rfl : m' = m := by exact_mod_cast hm'
              exact ht'
            · exact fun ht' => ⟨m, rfl, hm, ht'⟩
          by_cases ht' : t ∈ trTreeLeaves W (r + 1) (n' + m)
          · rw [hF]
            simp only
            rw [Set.indicator_of_mem (hiff.2 ht'), Set.indicator_of_mem ht',
              leafTerm_natCast_cons, ENNReal.ofReal_mul
                (mul_nonneg (varpi_nonneg _) (trTreeFactor_pos _ _ _ _ _).le)]
          · rw [hF]
            simp only
            rw [Set.indicator_of_notMem (mt hiff.1 ht'), Set.indicator_of_notMem ht']
            simp
      simp_rw [hterm]
      rw [ENNReal.tsum_mul_left, ih _ (by omega) (r + 1) (n' + m) rfl,
        ← ENNReal.ofReal_mul (mul_nonneg (varpi_nonneg _) (trTreeFactor_pos _ _ _ _ _).le),
        ite_eq_left_of_eq_true _ _ (eq_true ⟨n', m, hm, rfl, rfl⟩), Int.toNat_natCast, mul_assoc]
    · rw [tsum_eq_single []]
      · have : [c] ∈ trTreeLeaves W r h := singleton_mem_trTreeLeaves.2 hc
        simp only [hF, Set.indicator_of_mem this, leafTerm_singleton,
          ite_eq_right_of_eq_false _ _ (eq_false hc), mul_one]
      · intro t ht
        have : c :: t ∉ trTreeLeaves W r h := by
          rw [cons_mem_trTreeLeaves ht]
          rintro ⟨m, rfl, hm, -⟩
          exact hc (policyMem_natCast.2 hm)
        simp [hF, this]
  simp_rw [hinner]
  have hs := hasSum_varpi_mul_trTreeCost hW hcut r h X
  have h0 : ∀ c : ℤ, 0 ≤ varpi c * (trTreeFactor cut r h c X *
      if PolicyMem W r h c then trTreeCost cut W (r + 1) (h + c.toNat) X else 1) := by
    intro c
    refine mul_nonneg (varpi_nonneg _) (mul_nonneg (trTreeFactor_pos _ _ _ _ _).le ?_)
    split_ifs
    · exact trTreeCost_nonneg _ _ _ _ _
    · exact zero_le_one
  rw [← ENNReal.ofReal_tsum_of_nonneg h0 hs.summable, hs.tsum_eq]

/-- **A tree cost is a sum over its leaves.** Let `cut : ℕ → ℕ` and let `W` be a bounded policy
with `c ≤ cut(h)` for every `(r, h, c) ∈ W`. Then
`F^{cut,W}_{r,h}(X) = ∑_{λ ∈ 𝔏^W(r, h)} ∏_{i=1}^{|λ|} ϖ(λᵢ) ψ^cut_{r+i-1, h+λ₁+⋯+λᵢ₋₁, λᵢ}(X)`,
with letters indexed from `0`. -/
@[collatz_pos_dens "lem_tr_tree_cost_leaves"]
theorem hasSum_trTreeLeaves_trTreeCost {cut : ℕ → ℕ} {W : Set (ℕ × ℕ × ℕ)}
    (hW : IsBoundedPolicy W) (hcut : ∀ p ∈ W, p.2.2 ≤ cut p.2.1) (r h : ℕ) (X : ℝ) :
    HasSum (fun l : trTreeLeaves W r h => ∏ i : Fin (l : List ℤ).length,
        varpi (l : List ℤ)[i] *
          trTreeFactor cut (r + i) ((h : ℤ) + ((l : List ℤ).take i).sum).toNat (l : List ℤ)[i] X)
      (trTreeCost cut W r h X) := by
  change HasSum (leafTerm cut r h X ∘ Subtype.val) _
  rw [hasSum_subtype_iff_indicator]
  set f : List ℤ → ℝ := (trTreeLeaves W r h).indicator (leafTerm cut r h X) with hf
  have hf0 : ∀ l, 0 ≤ f l := Set.indicator_nonneg fun l _ => leafTerm_nonneg cut r h X l
  have htsum := tsum_leafTerm hW hcut X _ r h rfl
  have hne : ∑' l, ENNReal.ofReal (f l) ≠ ∞ := by
    rw [htsum]
    exact ENNReal.ofReal_ne_top
  have hsum : Summable f := by
    have := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal (hf0 _)] using this
  convert hsum.hasSum
  rw [← ENNReal.toReal_ofReal (trTreeCost_nonneg cut W r h X), ← htsum,
    ENNReal.tsum_toReal_eq fun _ => ENNReal.ofReal_ne_top]
  exact tsum_congr fun l => ENNReal.toReal_ofReal (hf0 l)

/-- The terms of the leaf expansion of a tree cost are nonnegative. -/
@[collatz_pos_dens "lem_tr_tree_cost_leaves"]
theorem trTreeLeaves_term_nonneg (cut : ℕ → ℕ) (r h : ℕ) (X : ℝ) (l : List ℤ) :
    0 ≤ ∏ i : Fin l.length,
      varpi l[i] * trTreeFactor cut (r + i) ((h : ℤ) + (l.take i).sum).toNat l[i] X :=
  leafTerm_nonneg cut r h X l

end CollatzPosDens
