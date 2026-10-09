/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.Tstar
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Rho
public import CollatzPosDens.Transfer.Schedule
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrClear
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrEstar
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.StoppingTrace.TrListWeight
public import CollatzPosDens.StoppingTrace.TrLive
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrMoment
public import CollatzPosDens.StoppingTrace.TrReward
public import CollatzPosDens.StoppingTrace.TrWhiteCount
public import CollatzPosDens.Renewal.RnFpMass
public import CollatzPosDens.StoppingTrace.TrMomentBound
public import CollatzPosDens.StoppingTrace.TrSurvivalTime

/-!
# The Markov bound for low-count survival

Let `J = ⌊n/2⌋`, let `ξ ∈ G_n` be a unit, `e ∈ 𝒫`, `m ∈ ℕ` with `j(e) + m = J`, `g ∈ ℕ`, and
assume `P_* ≤ J`. Then the fresh law `μ_{e,g}` gives the event
`S = Low^e \ (Bad^e_m ∪ E^{*,e} ∪ Clr)` mass at most `e^{101 γ_*} ϱ_*^{290}`.

For an atom `a = ((r, ℓ), β) ∈ S` with `μ_{e,g}(a) ≠ 0`, the list `β` is live, so
`le_trNu_and_trStopTime_le_schedule` with `i = r_* + 1 = 581` shows that the stopping time
`τ_{581}` of the fresh path is defined and at most `p_{580} = P_* - 1`. The weighted white count
is nondecreasing, so its value at `τ_{581}` is at most `N^e_{P_*-1}(a) ≤ T_* = 101`; hence the
weighted stop moment satisfies `𝒵_{581}(o, β) ≥ e^{-101 γ_*}` with `o = (j(e) + r, l(e) + ℓ)`.
This is a Markov inequality: `μ_{e,g}(a) 1_S(a) ≤ e^{101 γ_*} μ_{e,g}(a) 𝒵_{581}(o, β)`.
Summing over `β ∈ 𝔅^J` with `tsum_trListWeight_mul_trMoment_le` (`R = 581`, `N = J`) bounds the
inner sum by `ϱ_*^{290}`, and the first-passage law restricted to `ℕ × ℤ` has total mass at
most `1` (`tsum_ofReal_firstPassageLaw_natCast_le_one`).

## Main results

* `CollatzPosDens.tsum_trFreshLaw_trLow_diff_le`: the mass bound.

## Implementation notes

The sum is taken in `ℝ≥0∞` over the subtype of the event, of `ENNReal.ofReal μ_{e,g}(a)`, as for
the other sums over fresh atoms; this makes no summability assumption. No hypothesis `n ≥ 1` is
needed, since it follows from `1 ≤ P_* ≤ J`.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- Fresh atoms split as a displacement in `ℕ × ℤ` and a block list of `𝔅^{⌊n/2⌋}`. -/
private def trTraceEventAtomEquiv (n : ℕ) :
    trAtoms n ≃ (ℕ × ℤ) × {β : List (List ℤ × ℤ) //
      β.length = n / 2 ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)} where
  toFun a := (a.1.1, ⟨a.1.2, a.2⟩)
  invFun p := ⟨(p.1, p.2.1), p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The Markov bound for low-count survival.** Let `J = ⌊n/2⌋`, `ξ ∈ G_n` a unit, `e ∈ 𝒫`,
`m ∈ ℕ` with `j(e) + m = J`, `g ∈ ℕ` and `P_* ≤ J`. Then
`∑_{a ∈ Low^e \ (Bad^e_m ∪ E^{*,e} ∪ Clr)} μ_{e,g}(a) ≤ e^{101 γ_*} ϱ_*^{290}`. -/
@[collatz_pos_dens "lem_tr_trace_event"]
theorem tsum_trFreshLaw_trLow_diff_le {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {e : ℤ × ℤ} (he : e ∈ bkPoints) {m : ℕ} (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ)) (g : ℕ)
    (hP : pStar ≤ n / 2) :
    ∑' a : ↥(trLow n ξ e \ (trBad n e m ∪ trEStar n ξ e ∪ trClear n)),
        ENNReal.ofReal (trFreshLaw n e g a) ≤
      ENNReal.ofReal (Real.exp (101 * (gammaStar : ℝ)) * (rhoStar : ℝ) ^ 290) := by
  classical
  set S := trLow n ξ e \ (trBad n e m ∪ trEStar n ξ e ∪ trClear n) with hS
  set K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (101 * (gammaStar : ℝ))) with hK
  have hγ : (0 : ℝ) ≤ gammaStar := by exact_mod_cast gammaStar_pos.le
  have hpt : ∀ a : (ℕ × ℤ) × List (List ℤ × ℤ), S.indicator
      (fun a => ENNReal.ofReal (trFreshLaw n e g a)) a ≤
      (trAtoms n).indicator (fun a => K * ENNReal.ofReal (trFreshLaw n e g a) *
        ENNReal.ofReal (trMoment n ξ (bkJ e + a.1.1, bkL e + a.1.2) a.2 581)) a := by
    intro a
    by_cases haS : a ∈ S
    swap
    · rw [Set.indicator_of_notMem haS]; exact bot_le
    have hlow : a ∈ trLow n ξ e := haS.1
    have hnot : a ∉ trBad n e m ∧ a ∉ trEStar n ξ e ∧ a ∉ trClear n := by
      have := haS.2
      simp only [Set.mem_union, not_or] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
    have hA : a ∈ trAtoms n := hlow.1
    rw [Set.indicator_of_mem haS, Set.indicator_of_mem hA]
    by_cases hlive : TrLive a.2
    swap
    · have : trListWeight a.2 = 0 := by
        rw [trListWeight_eq_zero_iff]
        by_contra h
        push Not at h
        exact hlive h
      simp [trFreshLaw_def, this]
    obtain ⟨-, t, ht, htle⟩ := le_trNu_and_trStopTime_le_schedule hξ he hm hP hlive hlow
      hnot.1 hnot.2.1 hnot.2.2 (i := rStar + 1) (by omega) le_rfl
    rw [show rStar + 1 = 581 by rw [rStar_def]] at ht
    rw [Nat.add_sub_cancel] at htle
    have hZ := trMoment_eq_of_trStopTime_eq_some (n := n) (ξ := ξ)
      (o := (bkJ e + a.1.1, bkL e + a.1.2)) (β := a.2) ht
    rw [hZ]
    have htP : t ≤ pStar - 1 := by rw [pStar_def]; omega
    have hcount : trCount n ξ (bkJ e + a.1.1, bkL e + a.1.2) a.2 t ≤ 101 := by
      have h1 := trCount_mono (n := n) (ξ := ξ) (bkJ e + a.1.1, bkL e + a.1.2) a.2 htP
      have h2 := trWhiteCount_le_of_mem_trLow hlow
      rw [trWhiteCount_def, tStar_def] at h2
      push_cast at h2
      linarith
    have hone : 1 ≤ Real.exp (101 * (gammaStar : ℝ)) *
        Real.exp (-((gammaStar : ℝ) * trCount n ξ (bkJ e + a.1.1, bkL e + a.1.2) a.2 t)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hcount hγ
      linarith
    calc ENNReal.ofReal (trFreshLaw n e g a)
        = 1 * ENNReal.ofReal (trFreshLaw n e g a) := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp (101 * (gammaStar : ℝ)) *
            Real.exp (-((gammaStar : ℝ) *
              trCount n ξ (bkJ e + a.1.1, bkL e + a.1.2) a.2 t))) *
            ENNReal.ofReal (trFreshLaw n e g a) := by
          gcongr
          exact ENNReal.one_le_ofReal.2 hone
      _ = _ := by
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le, hK]
          ring
  have hinner : ∀ rl : ℕ × ℤ,
      ∑' β : {β : List (List ℤ × ℤ) // β.length = n / 2 ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
        ENNReal.ofReal (trListWeight β.1) *
          ENNReal.ofReal (trMoment n ξ (bkJ e + rl.1, bkL e + rl.2) β.1 581) ≤
        ENNReal.ofReal ((rhoStar : ℝ) ^ 290) := by
    intro rl
    have ho : (bkJ e + rl.1, bkL e + rl.2) ∈ bkPoints := by
      rw [mem_bkPoints_mk]
      have := mem_bkPoints.1 he
      omega
    have hN : ((n / 2 : ℕ) : ℤ) < bkJ (bkJ e + rl.1, bkL e + rl.2) + (n / 2 : ℕ) := by
      have := mem_bkPoints.1 ho
      omega
    have h := tsum_trListWeight_mul_trMoment_le hξ ho hN (R := 581) (by norm_num)
    rw [show (581 - 1) / 2 = 290 by norm_num, show 581 - 1 - 2 * 290 = 0 by norm_num, pow_zero,
      mul_one] at h
    exact h
  calc ∑' a : ↥S, ENNReal.ofReal (trFreshLaw n e g a)
      = ∑' a, S.indicator (fun a => ENNReal.ofReal (trFreshLaw n e g a)) a :=
        tsum_subtype S (fun a => ENNReal.ofReal (trFreshLaw n e g a))
    _ ≤ ∑' a, (trAtoms n).indicator (fun a => K * ENNReal.ofReal (trFreshLaw n e g a) *
        ENNReal.ofReal (trMoment n ξ (bkJ e + a.1.1, bkL e + a.1.2) a.2 581)) a :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' a : trAtoms n, K * ENNReal.ofReal (trFreshLaw n e g a) *
        ENNReal.ofReal (trMoment n ξ (bkJ e + a.1.1.1, bkL e + a.1.1.2) a.1.2 581) :=
        (tsum_subtype (trAtoms n) _).symm
    _ = K * ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2)) *
        ∑' β : {β : List (List ℤ × ℤ) // β.length = n / 2 ∧ ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)},
          ENNReal.ofReal (trListWeight β.1) *
            ENNReal.ofReal (trMoment n ξ (bkJ e + rl.1, bkL e + rl.2) β.1 581) := by
        rw [← (trTraceEventAtomEquiv n).symm.tsum_eq, ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
        refine tsum_congr fun rl => ?_
        rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
        refine tsum_congr fun β => ?_
        simp only [trTraceEventAtomEquiv, Equiv.coe_fn_symm_mk, trFreshLaw_def]
        rw [ENNReal.ofReal_mul (firstPassageLaw_nonneg _ _)]
        ring
    _ ≤ K * ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2)) *
        ENNReal.ofReal ((rhoStar : ℝ) ^ 290) := by
        gcongr with rl
        exact hinner rl
    _ = K * ENNReal.ofReal ((rhoStar : ℝ) ^ 290) *
        ∑' rl : ℕ × ℤ, ENNReal.ofReal (firstPassageLaw g ((rl.1 : ℤ), rl.2)) := by
        rw [ENNReal.tsum_mul_right]; ring
    _ ≤ K * ENNReal.ofReal ((rhoStar : ℝ) ^ 290) * 1 := by
        gcongr
        exact tsum_ofReal_firstPassageLaw_natCast_le_one g
    _ = ENNReal.ofReal (Real.exp (101 * (gammaStar : ℝ)) * (rhoStar : ℝ) ^ 290) := by
        rw [mul_one, hK, ENNReal.ofReal_mul (Real.exp_pos _).le]

end CollatzPosDens
