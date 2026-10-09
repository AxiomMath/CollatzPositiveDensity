/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Dstar
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.Dsc
public import CollatzPosDens.Transfer.DstarEq
public import CollatzPosDens.FourierDecay.ChPrimCoeff
public import CollatzPosDens.FourierDecay.ChQPointwise
public import CollatzPosDens.FourierDecay.ChHoldExpectation
public import CollatzPosDens.CharSum.ChFrontEnd
public import CollatzPosDens.Monotone.MoMonotonicity
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Transfer.RefLaw
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# Explicit decay of the Fourier coefficients at units

For every level `n ≥ 1` and every unit `ξ ∈ G_n`, the Fourier coefficient of the reference law
satisfies `|μ̂_n(ξ)| ≤ C_* / n^{10241/4096}`, where `C_* = (160 D_*)^{10241/4096}`.

Take `ε = ε_* = 8/217` and `A = A_* = 10241/4096`. By `norm_refLawDft_le_tsum_holdLaw_mul_chQ`,
`|μ̂_n(ξ)|` is at most `∑_h η(h) Q(h)`. The weighted maxima satisfy `Q_m ≤ Q_{m-1}` for every
`m ≥ D_*`, and `D_* = D_sc` is a natural number, so `chQ_le_threshold_rpow_mul` gives
`Q(p) ≤ D_*^A d_J(p)^{-A}` for every `p ∈ 𝒫`. The expectation under the holding-time law is then
at most `(160 D_*)^A / n^A = C_* / n^A`.

## Main results

* `CollatzPosDens.norm_refLawDft_le_Cstar_div_rpow`: `|μ̂_n(ξ)| ≤ C_* / n^{10241/4096}` for a
  unit `ξ ∈ G_n`.

## Implementation notes

The exponent `10241/4096` is not an integer, so `n^{10241/4096}` is the real power `Real.rpow`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Explicit decay of the Fourier coefficients.** For `n ≥ 1` and a unit `ξ ∈ G_n`,
`|μ̂_n(ξ)| ≤ C_* / n^{10241/4096}`. -/
@[collatz_pos_dens "lem_ch_primitive_decay"]
theorem norm_refLawDft_le_Cstar_div_rpow {n : ℕ} (hn : 1 ≤ n) {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) :
    ‖refLawDft n ξ‖ ≤ Cstar / (n : ℝ) ^ (10241 / 4096 : ℝ) := by
  have hDR : ((Dstar : ℚ) : ℝ) = (Dsc : ℝ) := by
    rw [Dstar_eq_Dsc, Rat.cast_natCast]
  have hA : (0 : ℝ) ≤ (Aexp : ℝ) := by exact_mod_cast Aexp_pos.le
  have hD : 1 ≤ Dsc := le_trans (by norm_num) two_le_Dsc
  have hmono : ∀ m, Dsc ≤ m → m ≤ n / 2 →
      chQm n ξ (epsStar : ℝ) (Aexp : ℝ) m ≤ chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) :=
    fun m hm _ ↦ chQm_le_chQm_pred_of_Dstar_le hξ (by rw [Dstar_eq_Dsc]; exact_mod_cast hm)
  have hQ := fun (p : ℤ × ℤ) (hp : p ∈ bkPoints) ↦
    chQ_le_threshold_rpow_mul n ξ (epsStar : ℝ) hA hD hmono hp
  have hexp := (holdLaw_chQ_expectation_le hn ξ (epsStar : ℝ)
    (by exact_mod_cast Aexp_pos) (by rw [Aexp_cast]; norm_num) Dsc hQ).2
  refine (norm_refLawDft_le_tsum_holdLaw_mul_chQ n ξ le_rfl).trans (hexp.trans (le_of_eq ?_))
  rw [Cstar_def, hDR, Aexp_cast]

end CollatzPosDens
