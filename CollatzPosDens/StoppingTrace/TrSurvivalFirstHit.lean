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
public import CollatzPosDens.Transfer.S02Pinit
public import CollatzPosDens.Transfer.S02Schedule
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrWhiteCount
public import CollatzPosDens.StoppingTrace.TrCountWhites
public import CollatzPosDens.StoppingTrace.TrRecipeIterMono
public import CollatzPosDens.StoppingTrace.TrSurvivalDomain

/-!
# A first trace time by time `p_0`

Let `ι ∈ 𝔍`, `J = ⌊n/2⌋`, `e ∈ 𝒫` and `m ∈ ℕ` with `j(e) + m = J`, and suppose `P_*(ι) ≤ J`. For
an atom `a ∈ Low^e(ι) \ Bad^e_m(ι)`, some time `c` with `1 ≤ c ≤ p_0(ι)` and `c < J` has
`y^e_c(a)` black (for `n, ξ, ε_*`).

Indeed `T_*(ι) + 1 = p_init(ι)` (`193` for `ι = o`, `169` for `ι = b`), and
`p_init(ι) = p_0(ι) ≤ p_{r_*(ι)}(ι) = P_*(ι) - 1 ≤ J - 1` by the monotonicity of the schedule
(`CollatzPosDens.schedule_le_schedule`, as `0 < r_*(ι)`). The weighted white count
`N^e_{P_*(ι)-1}(a)` is at least the number of white points among `y_1, …, y_{T_*(ι)+1}`, and it
is at most `T_*(ι)` because `a ∈ Low^e(ι)`; so some `y_c` with `1 ≤ c ≤ T_*(ι) + 1 = p_0(ι)` is
not white. Since `a ∉ Bad^e_m(ι)`, the path stays at level `j(y_c) ≤ J`, so `y_c` is black.
Finally `c ≤ P_*(ι) - 1 < J`.

## Main results

* `CollatzPosDens.exists_bkBlack_trFreshPath_of_mem_trLow_diff_trBad`: the first trace time
  occurs by time `p_0(ι)`.

## Implementation notes

The hypotheses `n ≥ 1`, that `ξ` is a unit and that `e ∈ 𝒫` play no role in the argument and
are dropped. The time `c` is a natural number, which loses nothing since `c ≥ 1`. The bound
`p_0(ι)` is written `schedule ι 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `T_*(ι) + 1 = p_init(ι)` for both Fourier indices. -/
private theorem tStar_add_one_eq_pInit_firstHit (ι : FIndex) : tStar ι + 1 = pInit ι := by
  cases ι <;> rfl

/-- **A first trace time by time `p_0(ι)`.** Let `ι ∈ 𝔍`, `J = ⌊n/2⌋`, `j(e) + m = J`,
`P_*(ι) ≤ J` and `a ∈ Low^e(ι) \ Bad^e_m(ι)`. Then some `c` with `1 ≤ c ≤ p_0(ι)` and `c < J`
has `y^e_c(a)` black. -/
@[collatz_pos_dens "lem_tr_survival_first_hit"]
theorem exists_bkBlack_trFreshPath_of_mem_trLow_diff_trBad {ι : FIndex} {n : ℕ}
    {ξ : ResidueGroup n} {e : ℤ × ℤ} {m : ℕ} (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ))
    (hP : pStar ι ≤ n / 2) {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (ha : a ∈ trLow ι n ξ e \ trBad ι n e m) :
    ∃ c : ℕ, 1 ≤ c ∧ c ≤ schedule ι 0 ∧ c < n / 2 ∧
      BkBlack n ξ (epsStar : ℝ) (trFreshPath e a c) := by
  obtain ⟨hlow, hbad⟩ := ha
  have hatom : a ∈ trAtoms n := hlow.1
  have hT0 : tStar ι + 1 = schedule ι 0 := by
    rw [schedule_zero, tStar_add_one_eq_pInit_firstHit]
  have hTP : tStar ι + 1 ≤ pStar ι - 1 := by
    have h1 := schedule_le_schedule ι (rStar_pos ι) le_rfl
    have := pStar_def ι
    omega
  have hlen : pStar ι - 1 ≤ a.2.length := by rw [trAtoms_length hatom]; omega
  obtain ⟨c, hc1, hc2, hw⟩ : ∃ c, 1 ≤ c ∧ c ≤ tStar ι + 1 ∧
      ¬IsBkWhite n ξ (epsStar : ℝ) (trFreshPath e a c) := by
    by_contra! h
    have hsub : Finset.Icc 1 (tStar ι + 1) ⊆ (Finset.Icc 1 (pStar ι - 1)).filter fun i =>
        IsBkWhite n ξ (epsStar : ℝ) (trPath (bkJ e + a.1.1, bkL e + a.1.2) a.2 i) := by
      intro i hi
      rw [Finset.mem_Icc] at hi
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hi.1, hi.2.trans hTP⟩, h i hi.1 hi.2⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Icc] at hcard
    have hcount := card_white_le_trCount (n := n) (ξ := ξ)
      (bkJ e + a.1.1, bkL e + a.1.2) a.2 (fun b hb => trAtoms_closing_mem hatom hb) hlen
    have hlowle := trWhiteCount_le_of_mem_trLow hlow
    rw [trWhiteCount_def] at hlowle
    have : tStar ι + 1 + 1 - 1 ≤ tStar ι := by
      exact_mod_cast (Nat.cast_le.2 hcard).trans (hcount.trans hlowle)
    omega
  have hjc := bkJ_trFreshPath_le_of_notMem_trBad hm hatom hbad (t := c) (by omega)
  exact ⟨c, hc1, hT0 ▸ hc2, by omega, hjc, not_lt.1 fun hlt => hw ⟨hjc, hlt⟩⟩

end CollatzPosDens
