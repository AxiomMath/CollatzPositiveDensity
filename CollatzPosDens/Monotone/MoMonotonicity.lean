/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Dstar
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Z
public import CollatzPosDens.Transfer.S02Chi
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkCover
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.CharSum.ChQm
public import CollatzPosDens.CharSum.ChBoundarySuffices
public import CollatzPosDens.CharSum.ChQmBounded
public import CollatzPosDens.Monotone.MoCase1
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.Case3.C3GapTop
public import CollatzPosDens.Case3.C3Case3
public import CollatzPosDens.Case3.C3NeartopPaid
public import CollatzPosDens.Transfer.S02Split
public import CollatzPosDens.Transfer.S02Dbad

/-!
# Monotonicity of the weighted maxima

Fix a Fourier index `ι`, take `A = A_*(ι)` and `ε = ε_*`, fix a level `n` and a unit
`ξ ∈ G_n`, and write `J = ⌊n/2⌋`. For every integer `m ≥ D_*(ι)` the weighted maxima satisfy
`Q_m ≤ Q_{m-1}`. Here `D_*(ι) = max(D_bad(ι), D_sc(ι))` and `D_bad(ι) ≥ 2^43`, so `m ≥ 2^43`.

By `chQm_le_chQm_pred` it suffices to show `Q(p) ≤ m^{-A_*(ι)} Q_{m-1}` for every `p ∈ 𝒫` on
the layer `j(p) + m = J`. A white such `p` is handled by
`chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite`, with the extra factor `e^{-z_* + χ_*/2} < 1` (as
`χ_*/2 = 63/5000 < 133/3125 = z_*`). A point on the layer that is not white is black, hence lies
in a triangle `Δ` of the canonical family `𝔗_{n,ξ,ε_*}`, and `l_Δ - l(p) = gap(p)`. The argument
splits at the level `ς(ι, m)`. If `gap(p) > ς(ι, m)`, `chQ_le_rpow_mul_chQm_of_gap_gt` (which
needs `m ≥ D_sc(ι)` and `m ≥ D_bad(ι)`) applies at the index `ι`. Otherwise
`chQ_le_mul_rpow_neg_chQm_of_trGap_le` (which needs `m ≥ 2^42`) gives
`Q(p) ≤ (1999/2000) m^{-A_*(ι)} Q_{m-1} ≤ m^{-A_*(ι)} Q_{m-1}`.

## Main results

* `CollatzPosDens.chQm_le_chQm_pred_of_Dstar_le`: `Q_m ≤ Q_{m-1}` for `m ≥ D_*(ι)`.

## Implementation notes

No hypotheses `n ≥ 1` or `m ≤ ⌊n/2⌋` are imposed: the layer condition `j(p) + m = ⌊n/2⌋` with
`j(p) ≥ 1` already gives `m < ⌊n/2⌋` wherever a point is examined. The bound `m ≥ 2^42` comes
from `m ≥ D_bad(ι) ≥ 2^43`. The integer `m ≥ D_*(ι) ≥ 2` is taken in `ℕ`, and `D_*(ι)` is a
natural number.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Monotonicity of the weighted maxima.** For a Fourier index `ι`, with `A = A_*(ι)` and
`ε = ε_*`, for a unit `ξ ∈ G_n` and every integer `m ≥ D_*(ι)`, `Q_m ≤ Q_{m-1}`. -/
@[collatz_pos_dens "lem_mo_monotonicity"]
theorem chQm_le_chQm_pred_of_Dstar_le (ι : FIndex) {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {m : ℕ} (hm : Dstar ι ≤ m) :
    chQm n ξ (epsStar : ℝ) (Aexp ι : ℝ) m ≤ chQm n ξ (epsStar : ℝ) (Aexp ι : ℝ) (m - 1) := by
  obtain ⟨hDbad, hDsc⟩ := Dstar_le_iff.1 hm
  have h43 : 2 ^ 43 ≤ m := (two_pow_43_le_Dbad ι).trans hDbad
  have h42 : 2 ^ 42 ≤ m := le_trans (by norm_num) h43
  have hm1 : 1 ≤ m := le_trans (by norm_num) h43
  have h40 : 2 ^ 40 ≤ m := le_trans (by norm_num) h43
  have hA : (0 : ℝ) ≤ (Aexp ι : ℝ) := by exact_mod_cast (Aexp_pos ι).le
  obtain ⟨hε₀, hε⟩ := epsStar_mem_bkRange (K := ℝ)
  refine chQm_le_chQm_pred n ξ _ hA hm1 fun p hp hpm => ?_
  have hjJ : bkJ p ≤ ((n / 2 : ℕ) : ℤ) := by omega
  by_cases hw : IsBkWhite n ξ (epsStar : ℝ) p
  · refine (chQ_le_exp_mul_rpow_mul_chQm_of_isBkWhite ι n ξ (epsStar : ℝ)
      (m := m) h40 hp hw hpm).trans ?_
    have hexp : Real.exp (-(zStar : ℝ) + (chiStar : ℝ) / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff, zStar_cast, chiStar_cast]
      norm_num
    rw [mul_assoc]
    exact mul_le_of_le_one_left
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (chQm_nonneg _ _ _ _ _)) hexp
  · obtain ⟨Δ, hΔ, hpΔ⟩ := (bkBlack_iff_exists_mem_bkFamily hξ hε₀ hε hp).1
      ⟨hjJ, not_lt.1 fun h => hw ⟨hjJ, h⟩⟩
    have hgapEq : Δ.l - bkL p = trGap n ξ (epsStar : ℝ) p := by
      rw [bkFamily_epsStar_l_eq_add_trGap hξ hΔ hpΔ]; ring
    rcases le_or_gt ((trGap n ξ (epsStar : ℝ) p : ℤ) : ℝ) (gapSplit ι m) with hgap | hgap
    · have hb : BkBlack n ξ (epsStar : ℝ) p :=
        (bkBlack_iff_exists_mem_bkFamily hξ hε₀ hε hp).2 ⟨Δ, hΔ, hpΔ⟩
      refine (chQ_le_mul_rpow_neg_chQm_of_trGap_le ι hξ hA le_rfl h42 hp hb hpm hgap).trans ?_
      rw [mul_assoc]
      exact mul_le_of_le_one_left
        (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (chQm_nonneg _ _ _ _ _))
        (by norm_num)
    · exact chQ_le_rpow_mul_chQm_of_gap_gt ι hξ (by exact_mod_cast hDsc)
        (by exact_mod_cast hDbad) hpm hΔ hpΔ hgap

end CollatzPosDens
