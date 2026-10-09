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
public import CollatzPosDens.Transfer.Z
public import CollatzPosDens.Transfer.W
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCover
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChBoundarySuffices
public import CollatzPosDens.CharSum.ChQmBounded
public import CollatzPosDens.Monotone.MoCase1
public import CollatzPosDens.Monotone.MoCase2
public import CollatzPosDens.Case3.C3Case3

/-!
# Monotonicity of the weighted maxima

Take `A = A_* = 10241/4096` and `ε = ε_*`, fix a level `n` and a unit `ξ ∈ G_n`, and write
`J = ⌊n/2⌋`. For every integer `m ≥ D_*` the weighted maxima satisfy `Q_m ≤ Q_{m-1}`.

By `CollatzPosDens.chQm_le_chQm_pred` it suffices to show `Q(p) ≤ m^{-A_*} Q_{m-1}` for every
`p ∈ 𝒫` on the layer `j(p) + m = J`. A white such `p` is handled by
`CollatzPosDens.chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite`, with the extra factor
`e^{-z_* + w_*/2} ≤ 1` (as `w_*/2 = 63/5000 < 21/500 = z_*`). A point on the layer that is not
white is black, hence lies in a triangle `Δ` of the canonical family `𝔗_{n,ξ,ε_*}`; according as
the horizontal gap `l_Δ - l(p)` is at most or exceeds `m / (log m)²`,
`CollatzPosDens.chQ_le_rpow_mul_chQm_of_mem_bkFamily` or
`CollatzPosDens.chQ_le_rpow_mul_chQm_of_gap_gt` applies.

## Main results

* `CollatzPosDens.chQm_le_chQm_pred_of_Dstar_le`: `Q_m ≤ Q_{m-1}` for `m ≥ D_*`.

## Implementation notes

The statement in [mazur2026] also assumes `n ≥ 1` and `m ≤ ⌊n/2⌋`. Neither is needed:
`CollatzPosDens.chQ_le_rpow_mul_chQm_of_gap_gt` obtains the bound it requires from the layer
condition `j(p) + m = ⌊n/2⌋` with `j(p) ≥ 1`. Both are dropped, which generalizes the
statement. The integer `m ≥ D_* ≥ 2` is taken in `ℕ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Monotonicity of the weighted maxima.** With `A = A_*` and `ε = ε_*`, for a unit
`ξ ∈ G_n` and every integer `m ≥ D_*`, `Q_m ≤ Q_{m-1}`. -/
@[collatz_pos_dens "lem_mo_monotonicity"]
theorem chQm_le_chQm_pred_of_Dstar_le {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {m : ℕ} (hm : Dstar ≤ (m : ℚ)) :
    chQm n ξ (epsStar : ℝ) (Aexp : ℝ) m ≤ chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) := by
  obtain ⟨hD1, hDpt, hDexp, hDbad, hDsc, hD1', -⟩ := Dstar_le_iff.1 hm
  have hm1 : 1 ≤ m := by exact_mod_cast hD1'
  have hA : (0 : ℝ) ≤ (Aexp : ℝ) := by exact_mod_cast Aexp_pos.le
  obtain ⟨hε₀, hε⟩ := epsStar_mem_bkRange (K := ℝ)
  have hQ : 0 ≤ chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) := chQm_nonneg _ _ _ _ _
  refine chQm_le_chQm_pred n ξ _ hA hm1 fun p hp hpm => ?_
  have hjJ : bkJ p ≤ ((n / 2 : ℕ) : ℤ) := by omega
  by_cases hw : IsBkWhite n ξ (epsStar : ℝ) p
  · have h := chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite n ξ (epsStar : ℝ)
      (m := m) (by exact_mod_cast hD1) hp hw hpm
    refine h.trans ?_
    have hexp : Real.exp (-(zStar : ℝ) + (wStar : ℝ) / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff, zStar_cast, wStar_cast]; norm_num
    have hz : 0 ≤ (m : ℝ) ^ (-(Aexp : ℝ)) * chQm n ξ (epsStar : ℝ) (Aexp : ℝ) (m - 1) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hQ
    rw [mul_assoc]
    exact mul_le_of_le_one_left hz hexp
  · have hb : BkBlack n ξ (epsStar : ℝ) p :=
      ⟨hjJ, not_lt.1 fun h => hw ⟨hjJ, h⟩⟩
    obtain ⟨Δ, hΔ, hpΔ⟩ := (bkBlack_iff_exists_mem_bkFamily hξ hε₀ hε hp).1 hb
    rcases le_or_gt ((Δ.l - bkL p : ℤ) : ℝ) ((m : ℝ) / Real.log m ^ 2) with hgap | hgap
    · exact chQ_le_rpow_mul_chQm_of_mem_bkFamily hξ (by exact_mod_cast hDpt)
        (by exact_mod_cast hDexp) hpm hΔ hpΔ hgap
    · exact chQ_le_rpow_mul_chQm_of_gap_gt hξ (by exact_mod_cast hDsc)
        (by exact_mod_cast hDbad) hpm hΔ hpΔ hgap

end CollatzPosDens
