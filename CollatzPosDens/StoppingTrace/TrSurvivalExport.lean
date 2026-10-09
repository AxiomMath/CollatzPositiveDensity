/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.PT
public import CollatzPosDens.Transfer.TraceTerm
public import CollatzPosDens.StoppingTrace.TrBad
public import CollatzPosDens.StoppingTrace.TrClear
public import CollatzPosDens.StoppingTrace.TrClearMass
public import CollatzPosDens.StoppingTrace.TrEstar
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrLow
public import CollatzPosDens.StoppingTrace.TrTraceEvent

/-!
# Mass of the low, non-bad event under the fresh law

Let `J = ⌊n/2⌋`, `ξ ∈ G_n` a unit, `e ∈ 𝒫`, `m ∈ ℕ` with `j(e) + m = J`, `g ∈ ℕ`, and suppose
`P_* ≤ J`. Then the fresh law `μ_{e,g}` gives the event `Low^e \ Bad^e_m` mass at most that of
the large-triangle event `E^{*,e}` plus `1 / P_T + 2^{-43}`.

Indeed `Low^e \ Bad^e_m` is covered by `E^{*,e}`, the failed clearing event `Clr` and the
remainder `Low^e \ (Bad^e_m ∪ E^{*,e} ∪ Clr)`. The second has mass `< 2^{-43}` and the third
mass `≤ e^{101 γ_*} ϱ_*^{290} < 1 / P_T`.

## Main results

* `CollatzPosDens.tsum_trLow_diff_trBad_trFreshLaw_le`: the mass bound.

## Implementation notes

The sums are unconditional sums in `[0, ∞]` of `ENNReal.ofReal` of the (nonnegative) masses, as
for the dependencies, so no summability hypothesis is needed. The hypothesis `n ≥ 1` is not used
and is dropped.

## References

* [Mazur, *Collatz positive density*], §9.9.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- Let `J = ⌊n/2⌋`, `ξ ∈ G_n` a unit, `e ∈ 𝒫`, `m ∈ ℕ` with `j(e) + m = J`, `g ∈ ℕ`, and
`P_* ≤ J`. Then
`∑_{a ∈ Low^e \ Bad^e_m} μ_{e,g}(a) ≤ ∑_{a ∈ E^{*,e}} μ_{e,g}(a) + 1 / P_T + 2^{-43}`. -/
@[collatz_pos_dens "lem_tr_survival_export"]
theorem tsum_trLow_diff_trBad_trFreshLaw_le {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {e : ℤ × ℤ} (he : e ∈ bkPoints) {m : ℕ} (hm : bkJ e + m = ((n / 2 : ℕ) : ℤ)) (g : ℕ)
    (hP : pStar ≤ n / 2) :
    ∑' a : ↥(trLow n ξ e \ trBad n e m), ENNReal.ofReal (trFreshLaw n e g a) ≤
      ∑' a : trEStar n ξ e, ENNReal.ofReal (trFreshLaw n e g a) +
        ENNReal.ofReal (1 / (PT : ℝ)) + ENNReal.ofReal ((2 : ℝ) ^ (-43 : ℤ)) := by
  set μ : (ℕ × ℤ) × List (List ℤ × ℤ) → ℝ≥0∞ := fun a ↦ ENNReal.ofReal (trFreshLaw n e g a)
    with hμ
  set R := trLow n ξ e \ (trBad n e m ∪ trEStar n ξ e ∪ trClear n) with hR
  have hRle : ∑' a : R, μ a ≤ ENNReal.ofReal (1 / (PT : ℝ)) :=
    (tsum_trFreshLaw_trLow_diff_le hξ he hm g hP).trans
      (ENNReal.ofReal_le_ofReal exp_gammaStar_mul_rhoStar_pow_lt.le)
  have hClr : ∑' a : trClear n, μ a ≤ ENNReal.ofReal ((2 : ℝ) ^ (-43 : ℤ)) :=
    (tsum_trFreshLaw_trClear_lt n e g hP).le
  calc ∑' a : ↥(trLow n ξ e \ trBad n e m), μ a
      ≤ ∑' a : trEStar n ξ e, μ a + ∑' a : R, μ a + ∑' a : trClear n, μ a := by
        rw [tsum_subtype (trLow n ξ e \ trBad n e m) μ, tsum_subtype (trEStar n ξ e) μ,
          tsum_subtype R μ, tsum_subtype (trClear n) μ, ← ENNReal.tsum_add, ← ENNReal.tsum_add]
        refine ENNReal.tsum_le_tsum fun a ↦ ?_
        by_cases ha : a ∈ trLow n ξ e \ trBad n e m
        · rw [Set.indicator_of_mem ha]
          by_cases hE : a ∈ trEStar n ξ e
          · rw [Set.indicator_of_mem hE, add_assoc]
            exact le_self_add
          by_cases hC : a ∈ trClear n
          · rw [Set.indicator_of_mem hC]
            exact le_add_self
          have hr : a ∈ R := ⟨ha.1, by simp [ha.2, hE, hC]⟩
          rw [Set.indicator_of_mem hr, add_comm (Set.indicator _ _ a), add_assoc]
          exact le_self_add
        · rw [Set.indicator_of_notMem ha]
          exact bot_le
    _ ≤ ∑' a : trEStar n ξ e, μ a + ENNReal.ofReal (1 / (PT : ℝ)) +
          ENNReal.ofReal ((2 : ℝ) ^ (-43 : ℤ)) := by
        gcongr

end CollatzPosDens
