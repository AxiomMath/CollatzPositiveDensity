/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGeom4
public import CollatzPosDens.Renewal.RnHold
public import CollatzPosDens.Renewal.RnHoldWords
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnPascalTotal

/-!
# The horizontal marginal of the holding-time law

For every `j ≥ 1`, summing the holding-time law `η(j, l)` over `l ∈ ℤ` gives the geometric
weight `ν₄₅(j) = (5/16)(11/16)^{j-1}`. Summing over `l` removes the constraint on the letter sum
of the hold words, so `∑_l η(j, l)` is the sum of `∏_{i=1}^j ϖ(c_i)` over all words `c ∈ ℤ^j`
whose first `j - 1` letters avoid `{4, 5}` and whose last letter lies in `{4, 5}` (the restriction
`c_i ≥ 2` is automatic since `ϖ` vanishes on `b ≤ 1`). By Tonelli this factorises as
`(∑_{b ∉ {4,5}} ϖ(b))^{j-1} (ϖ(4) + ϖ(5)) = (11/16)^{j-1} · (5/16)`.

## Main results

* `CollatzPosDens.hasSum_holdLaw`: for `j ≥ 1`, `l ↦ η(j, l)` has sum `ν₄₅(j)`.
* `CollatzPosDens.tsum_holdLaw`: for `j ≥ 1`, `∑_{l ∈ ℤ} η(j, l) = ν₄₅(j)`.

## Implementation notes

The statement is proved as an unconditionally convergent series (`HasSum`), which is the
strongest form; for nonnegative terms it is equivalent to convergence in any order. The
length `j` of a hold word is a natural number, and `ν₄₅` takes an integer argument, so the
right-hand side is `ν₄₅(↑j)`.

## References

* [Mazur, *Collatz positive density*], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The factorised weight of a word of length `n + 1`. -/
private noncomputable def wordW (n : ℕ) (c : Fin (n + 1) → ℤ) : ℝ :=
  (∏ i : Fin n, varpiIn (c i.castSucc)) * varpiLast (c (Fin.last n))

private lemma hasSum_wordW (n : ℕ) : HasSum (wordW n) ((11 / 16) ^ n * (5 / 16)) := by
  have h1 := hasSum_pi_fin_prod_of_nonneg hasSum_varpiIn varpiIn_nonneg n
  have h0 : 0 ≤ fun b : Fin n → ℤ ↦ ∏ i, varpiIn (b i) :=
    fun b ↦ Finset.prod_nonneg fun i _ ↦ varpiIn_nonneg _
  have hs : Summable (fun x : (Fin n → ℤ) × ℤ ↦ (∏ i, varpiIn (x.1 i)) * varpiLast x.2) :=
    Summable.mul_of_nonneg (f := fun b : Fin n → ℤ ↦ ∏ i, varpiIn (b i)) (g := varpiLast)
      h1.summable hasSum_varpiLast.summable h0 varpiLast_nonneg
  have hmul : HasSum (fun x : (Fin n → ℤ) × ℤ ↦ (∏ i, varpiIn (x.1 i)) * varpiLast x.2)
      ((11 / 16) ^ n * (5 / 16)) :=
    HasSum.mul (f := fun b : Fin n → ℤ ↦ ∏ i, varpiIn (b i)) (g := varpiLast) h1 hasSum_varpiLast hs
  have key : (fun x : (Fin n → ℤ) × ℤ ↦ (∏ i, varpiIn (x.1 i)) * varpiLast x.2) =
      wordW n ∘ (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ ↦ ℤ) := by
    funext x
    simp [wordW, Fin.snocEquiv, Fin.snoc_castSucc, Fin.snoc_last]
  rw [key] at hmul
  exact (Equiv.hasSum_iff _).mp hmul

/-- On words of letter sum `l`, the factorised weight is the hold-word weight. -/
private lemma indicator_wordW (n : ℕ) (l : ℤ) (c : Fin (n + 1) → ℤ) :
    {c : Fin (n + 1) → ℤ | ∑ i, c i = l}.indicator (wordW n) c =
      (holdWords (n + 1) l).indicator (fun c ↦ ∏ i, varpi (c i)) c := by
  by_cases hc : c ∈ holdWords (n + 1) l
  · obtain ⟨hi, hlast, hs⟩ := mem_holdWords_succ.1 hc
    rw [Set.indicator_of_mem hc, Set.indicator_of_mem
      (show c ∈ {c : Fin (n + 1) → ℤ | ∑ i, c i = l} from holdWords_sum_eq hc)]
    rw [wordW, Fin.prod_univ_castSucc]
    congr 1
    · exact Finset.prod_congr rfl fun i _ ↦ varpiIn_of_notMem (hi i).2
    · exact varpiLast_of_mem hlast
  · rw [Set.indicator_of_notMem hc]
    by_cases hs : ∑ i, c i = l
    · rw [Set.indicator_of_mem (show c ∈ {c : Fin (n + 1) → ℤ | ∑ i, c i = l} from hs)]
      by_contra hne
      apply hc
      obtain ⟨hpre, hl⟩ := mul_ne_zero_iff.mp hne
      rw [Finset.prod_ne_zero_iff] at hpre
      have hlast : c (Fin.last n) ∈ ({4, 5} : Set ℤ) := by
        by_contra h; exact hl (varpiLast_of_notMem h)
      refine mem_holdWords_succ.2 ⟨fun i ↦ ?_, hlast, ?_⟩
      · have hne := hpre i (Finset.mem_univ _)
        have hn : c i.castSucc ∉ ({4, 5} : Set ℤ) := fun h ↦ hne (varpiIn_of_mem h)
        refine ⟨?_, hn⟩
        by_contra h
        exact hne (by rw [varpiIn_of_notMem hn, varpi_of_le_one (by omega)])
      · rw [← Fin.sum_univ_castSucc]; exact hs
    · exact Set.indicator_of_notMem (show c ∉ {c : Fin (n + 1) → ℤ | ∑ i, c i = l} from hs) _

private lemma holdLaw_succ_eq (n : ℕ) (l : ℤ) :
    holdLaw (n + 1) l = ∑' c : {c : Fin (n + 1) → ℤ // ∑ i, c i = l}, wordW n c := by
  rw [holdLaw_def, tsum_subtype (holdWords (n + 1) l) (fun c ↦ ∏ i, varpi (c i)),
    show (∑' c : {c : Fin (n + 1) → ℤ // ∑ i, c i = l}, wordW n c) =
      ∑' c : ({c | ∑ i, c i = l} : Set (Fin (n + 1) → ℤ)), wordW n c from rfl,
    tsum_subtype {c : Fin (n + 1) → ℤ | ∑ i, c i = l} (wordW n)]
  exact tsum_congr fun c ↦ (indicator_wordW n l c).symm

/-- **Horizontal marginal of the holding-time law.** For every `j ≥ 1`, the series
`∑_{l ∈ ℤ} η(j, l)` converges unconditionally to `ν₄₅(j)`. -/
@[collatz_pos_dens "lem_rn_hold_jmarginal"]
theorem hasSum_holdLaw {j : ℕ} (hj : 1 ≤ j) :
    HasSum (fun l : ℤ ↦ holdLaw j l) (nu45 j) := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have hF := (Equiv.hasSum_iff (f := wordW n)
    (Equiv.sigmaFiberEquiv fun c : Fin (n + 1) → ℤ ↦ ∑ i, c i)).mpr (hasSum_wordW n)
  have hS := hF.sigma fun l ↦ (hF.summable.sigma_factor l).hasSum
  push_cast
  rw [nu45_natCast_add_one, mul_comm]
  convert hS using 2 with l
  exact holdLaw_succ_eq n l

/-- For every `j ≥ 1`, `∑_{l ∈ ℤ} η(j, l) = ν₄₅(j)`. -/
theorem tsum_holdLaw {j : ℕ} (hj : 1 ≤ j) : ∑' l : ℤ, holdLaw j l = nu45 j :=
  (hasSum_holdLaw hj).tsum_eq

end CollatzPosDens
