/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Tstar
public import CollatzPosDens.Transfer.Pinit
public import CollatzPosDens.Transfer.Schedule
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrWhiteCount
public import CollatzPosDens.StoppingTrace.TrCountWhites
public import CollatzPosDens.StoppingTrace.TrRecipeIterMono
public import CollatzPosDens.StoppingTrace.TrSurvivalDomain

/-!
# A first stop by time `T_* + 1`

Let `J = ⌊n/2⌋`, `e ∈ ℤ × ℤ` and `m ∈ ℕ` with `j(e) + m = J`, and suppose `P_* ≤ J`. For an
atom `a ∈ Low^e \ Bad^e_m`, some time `c` with `1 ≤ c ≤ T_* + 1` and `c < J` has `y^e_c(a)`
black.

The proof uses `T_* + 1 = 102 ≤ 1024 = p_0 ≤ p_{r_*} = P_* - 1 ≤ J - 1`. The weighted white count
`N^e_{P_*-1}(a)` is at least the number of white points among `y_1, …, y_{T_*+1}`, and it is at
most `T_*` because `a ∈ Low^e`; so some `y_c` with `1 ≤ c ≤ T_* + 1` is not white. Since
`a ∉ Bad^e_m`, the path stays at level `j(y_c) ≤ J`, so `y_c` is black. Finally
`c ≤ P_* - 1 < J`.

## Main results

* `CollatzPosDens.exists_bkBlack_trFreshPath_of_mem_trLow_diff_trBad`: the first stop
  occurs by time `T_* + 1`.

## Implementation notes

The statement does not assume `n ≥ 1`, that `ξ` is a unit, or that `e ∈ 𝒫`, since the argument
does not use them. The time `c` is a natural number, which loses nothing since `c ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `J = ⌊n/2⌋`, `j(e) + m = J`, `P_* ≤ J` and `a ∈ Low^e \ Bad^e_m`. Then some `c` with
`1 ≤ c ≤ T_* + 1` and `c < J` has `y^e_c(a)` black. -/
@[collatz_pos_dens "lem_tr_survival_first_hit"]
theorem exists_bkBlack_trFreshPath_of_mem_trLow_diff_trBad {n : ℕ} {ξ : ResidueGroup n}
    {e : ℤ × ℤ} {m : ℕ} (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ)) (hP : pStar ≤ n / 2)
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trLow n ξ e \ trBad n e m) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ tStar + 1 ∧ c < n / 2 ∧
      BkBlack n ξ (epsStar : ℝ) (trFreshPath e a c) := by
  obtain ⟨hlow, hbad⟩ := ha
  have hatom : a ∈ trAtoms n := hlow.1
  have hTP : tStar + 1 ≤ pStar - 1 := by
    have h1 := pInit_le_schedule rStar
    have h2 := pStar_def
    rw [pInit_def] at h1
    rw [tStar_def]
    omega
  have hlen : pStar - 1 ≤ a.2.length := by rw [trAtoms_length hatom]; omega
  obtain ⟨c, hc1, hc2, hw⟩ : ∃ c, 1 ≤ c ∧ c ≤ tStar + 1 ∧
      ¬IsBkWhite n ξ (epsStar : ℝ) (trFreshPath e a c) := by
    by_contra! h
    have hsub : Finset.Icc 1 (tStar + 1) ⊆ (Finset.Icc 1 (pStar - 1)).filter fun i =>
        IsBkWhite n ξ (epsStar : ℝ) (trPath (bkJ e + a.1.1, bkL e + a.1.2) a.2 i) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨hi.1, hi.2.trans hTP⟩, h i hi.1 hi.2⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcount := card_white_le_trCount (n := n) (ξ := ξ)
      (bkJ e + a.1.1, bkL e + a.1.2) a.2 hlen
    have hlowle := trWhiteCount_le_of_mem_trLow hlow
    rw [trWhiteCount_def] at hlowle
    have : ((tStar + 1 + 1 - 1 : ℕ) : ℝ) ≤ (tStar : ℝ) :=
      (Nat.cast_le.2 hcard).trans (hcount.trans hlowle)
    have : tStar + 1 + 1 - 1 ≤ tStar := by exact_mod_cast this
    omega
  have hjc := bkJ_trFreshPath_le_of_notMem_trBad hm hatom hbad (t := c) (by omega)
  exact ⟨c, hc1, hc2, by omega, hjc, not_lt.1 fun hlt => hw ⟨hjc, hlt⟩⟩

end CollatzPosDens
