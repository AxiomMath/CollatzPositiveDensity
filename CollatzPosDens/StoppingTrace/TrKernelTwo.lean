/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Rho
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrKernel
public import CollatzPosDens.StoppingTrace.TrTheta
public import CollatzPosDens.StoppingTrace.TrOmegaValue
public import CollatzPosDens.StoppingTrace.TrDeltaFloor
public import CollatzPosDens.StoppingTrace.TrDeltaZero
public import CollatzPosDens.StoppingTrace.TrGapZeroLoss
public import CollatzPosDens.StoppingTrace.TrGuardGap
public import CollatzPosDens.StoppingTrace.TrKernelTwoBound
public import CollatzPosDens.StoppingTrace.TrLossNonneg
public import CollatzPosDens.StoppingTrace.TrMuValue

/-!
# The two-step rate

Fix a level `n` and a unit `ξ ∈ G_n`; "black" refers to `(n, ξ, ε_*)`. For every black point
`v ∈ 𝒫`, the second power of the entry kernel satisfies `m_2(v) ≤ ϱ_*`, where
`ϱ_* = (1 - d_*)² - Ω_*` is the two-passage rate.

Let `s = gap(v)`. The two-step bound gives
`m_2(v) ≤ (1 - d_*)² - (1 - d_*) δ_tr(s) - ∑_{π ∈ Π_s} a(π) Loss(y_π)`, and the series is
nonnegative since every loss is. If `s ≥ 1`, then `δ_tr(s) ≥ δ_tr(6)` and
`(1 - d_*) δ_tr(6) > Ω_*`. If `s = 0`, then `δ_tr(0) = 0` and the series is at least
`e^{-γ_*} θ_∘ (3/16 + 6701/26392)`, which exceeds `(1 - γ_*) θ_∘ (3/16 + 6701/26392) = Ω_*`
because `e^{-γ_*} > 1 - γ_*` and `θ_∘ > 0`.

## Main results

* `CollatzPosDens.trKernel_two_le_rhoStar`: `m_2(v) ≤ ϱ_*` for every black point `v`.

## Implementation notes

The value `m_2(v)` lies in `[0, ∞]`, and the bound is stated there against `ENNReal.ofReal ϱ_*`;
since `ϱ_* > 0` this is the source's inequality (and asserts in particular that `m_2(v)` is
finite). The hypotheses `n ≥ 1` and `J = ⌊n/2⌋` of the source are standing notation and are not
needed.

## References

* [Mazur, *Collatz positive density*], §9.6.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n}

/-- **The two-step rate.** Let `ξ ∈ G_n` be a unit and `v ∈ 𝒫` a black point. Then
`m_2(v) ≤ ϱ_*`. -/
@[collatz_pos_dens "lem_tr_kernel_two"]
theorem trKernel_two_le_rhoStar (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) :
    trKernel n ξ 2 v ≤ ENNReal.ofReal (rhoStar : ℝ) := by
  have hc0 : 0 < 1 - (dStar : ℝ) := by
    have : (dStar : ℝ) < 1 := by exact_mod_cast dStar_lt_one
    linarith
  have hρ : (rhoStar : ℝ) = (1 - (dStar : ℝ)) ^ 2 - (omegaStar : ℝ) := by
    rw [rhoStar_def]; push_cast; rfl
  have hρ0 : (0 : ℝ) ≤ rhoStar := by exact_mod_cast rhoStar_pos.le
  have hS0 : ∀ s : ℕ, 0 ≤ ∑' π : trPassage s,
      trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) *
        (trBridgeLoss n ξ (trPath v π.1 π.1.length)).toReal := fun s ↦
    tsum_nonneg fun π ↦ mul_nonneg (mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le)
      (EReal.toReal_nonneg (trBridgeLoss_nonneg n ξ _))
  suffices hkey : ∀ r : ℝ, (trKernel n ξ 2 v : EReal) ≤ (r : EReal) → r ≤ rhoStar →
      trKernel n ξ 2 v ≤ ENNReal.ofReal (rhoStar : ℝ) by
    have hbound := trKernel_two_le hξ hv hb
    rcases Nat.eq_zero_or_pos (trGap n ξ (epsStar : ℝ) v) with hgap | hpos
    · have hloss := le_tsum_trPassage_zero_trBridgeLoss hξ hv hb hgap
      rw [hgap, trDelta_zero] at hbound
      refine hkey _ hbound ?_
      have hθ := trTheta_pos
      have hexp : 1 - (gammaStar : ℝ) < Real.exp (-(gammaStar : ℝ)) := by
        have := Real.add_one_lt_exp (x := -(gammaStar : ℝ))
          (by rw [gammaStar_cast]; norm_num)
        linarith
      have hγ : 0 < 1 - (gammaStar : ℝ) := by rw [gammaStar_cast]; norm_num
      have hconv : ∑' π : trPassage 0, ENNReal.ofReal (trListWeight π.1) *
          ENNReal.ofReal (Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length)) *
            (trBridgeLoss n ξ (trPath v π.1 π.1.length)).toENNReal =
          ENNReal.ofReal (∑' π : trPassage 0,
            trListWeight π.1 * Real.exp (-(gammaStar : ℝ) * trCount n ξ v π.1 π.1.length) *
              (trBridgeLoss n ξ (trPath v π.1 π.1.length)).toReal) := by
        rw [ENNReal.ofReal_tsum_of_nonneg
          (fun π ↦ mul_nonneg (mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le)
            (EReal.toReal_nonneg (trBridgeLoss_nonneg n ξ _)))
          (trKernel_two_le_summable hξ hv 0)]
        refine tsum_congr fun π ↦ ?_
        have hy := trPath_mem_bkPoints hv π.1 π.1.length
        rw [(trKernel_two_le_trBridgeLoss_eq hξ hy).1, EReal.real_coe_toENNReal,
          EReal.toReal_coe, ENNReal.ofReal_mul (mul_nonneg (trListWeight_nonneg _)
            (Real.exp_pos _).le), ENNReal.ofReal_mul (trListWeight_nonneg _)]
      rw [hconv, ENNReal.ofReal_le_ofReal_iff (hS0 0)] at hloss
      have : (1 - (gammaStar : ℝ)) * trTheta * (3 / 16 + 6701 / 26392) <
          Real.exp (-(gammaStar : ℝ)) * trTheta * (3 / 16 + 6701 / 26392) := by
        gcongr
      rw [hρ, ← omegaStar_eq_trTheta]
      linarith
    · refine hkey _ hbound ?_
      have h6 := trDelta_six_le hpos
      have hg := omegaStar_lt_one_sub_dStar_mul_trDelta_six
      have : (1 - (dStar : ℝ)) * trDelta 6 ≤
          (1 - (dStar : ℝ)) * trDelta (trGap n ξ (epsStar : ℝ) v) :=
        mul_le_mul_of_nonneg_left h6 hc0.le
      have := hS0 (trGap n ξ (epsStar : ℝ) v)
      rw [hρ]
      linarith
  intro r hr hrρ
  refine EReal.coe_ennreal_le_coe_ennreal_iff.1 ?_
  rw [EReal.coe_ennreal_ofReal, max_eq_left hρ0]
  exact hr.trans (EReal.coe_le_coe_iff.2 hrρ)

end CollatzPosDens
