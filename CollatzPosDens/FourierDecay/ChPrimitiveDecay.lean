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
public import CollatzPosDens.Transfer.S02DF
public import CollatzPosDens.Transfer.FxRefLawTotal
public import CollatzPosDens.Transfer.RefLaw
public import CollatzPosDens.Transfer.ResidueGroup
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.CharSum.ChDist
public import CollatzPosDens.CharSum.ChFrontEnd
public import CollatzPosDens.Renewal.RnHoldJmarginal
public import CollatzPosDens.Renewal.RnHoldMass
public import CollatzPosDens.Monotone.MoMonotonicity
public import CollatzPosDens.FourierDecay.ChQPointwise
public import CollatzPosDens.FourierDecay.MoSerInverseMoment

/-!
# Explicit decay of the Fourier coefficients at units

For every Fourier index `ι`, every level `n ≥ 1` and every unit `ξ ∈ G_n`, the Fourier
coefficient of the reference law satisfies `|μ̂_n(ξ)| ≤ (D_F(ι) / n)^{A_*(ι)}`, where
`D_F(ι) = 2 D_*(ι) + 6` and `A_*(ι) ∈ {21193/10000, 17/10}`, so `1 < A_*(ι) ≤ 5/2`. Below,
`ι` is fixed and suppressed.

For `n ≤ D_F` this is the trivial bound `|μ̂_n(ξ)| ≤ ∑_y μ_n(y) = 1`. For `n > D_F` let
`J = ⌊n/2⌋ ≥ D_* + 3`. The weighted maxima are monotone, `Q_m ≤ Q_{m-1}` for `m ≥ D_*`
(`chQm_le_chQm_pred_of_Dstar_le`), and `D_* ≥ D_bad ≥ 2^43` is a natural number, so
`chQ_le_threshold_rpow_mul` gives `Q(v) ≤ (D_* - 1)^A d_J(v)^{-A}` on `𝒫`. By
`norm_refLawDft_le_tsum_holdLaw_mul_chQ`, `|μ̂_n(ξ)|` is at most `∑_h η(h) Q(h)`; grouping by
the first coordinate, the horizontal marginal of `η` is `ν₄₅`, and
`tsum_nu45_mul_max_rpow_neg_le_sub` gives `|μ̂_n(ξ)| ≤ ((D_* - 1)/(J - 7/2))^A`. Finally
`(D_* - 1) n ≤ D_F (J - 7/2)` because `n ≤ 2J + 1` and `J ≥ D_* + 3`.

## Main results

* `CollatzPosDens.norm_refLawDft_le_one`: `|μ̂_n(ξ)| ≤ 1`.
* `CollatzPosDens.hasSum_holdLaw_mul_chDist_rpow_neg`: the series `∑_{h ∈ 𝒫} η(h) d_J(h)^{-A}`
  is `∑_{r ≥ 1} ν₄₅(r) max(J - r, 1)^{-A}`.
* `CollatzPosDens.norm_refLawDft_le_Cstar_div_rpow`: `|μ̂_n(ξ)| ≤ (D_F(ι) / n)^{A_*(ι)}` for a
  unit `ξ ∈ G_n`.

## Implementation notes

The exponent `A_*(ι)` is not an integer, so `(D_F(ι) / n)^{A_*(ι)}` is the real power
`Real.rpow` of the real casts of the rationals `D_F(ι)` and `A_*(ι)`.

## References

* [Mazur, *Collatz positive density*], §11.
-/

@[expose] public section

namespace CollatzPosDens

/-- The trivial bound `|μ̂_n(ξ)| ≤ ∑_y μ_n(y) = 1`. -/
theorem norm_refLawDft_le_one (n : ℕ) (ξ : ResidueGroup n) : ‖refLawDft n ξ‖ ≤ 1 := by
  have hfin : ∀ y, refLaw n y ≠ ⊤ := fun y ↦
    ne_top_of_le_ne_top ENNReal.one_ne_top
      ((Finset.single_le_sum (fun _ _ ↦ bot_le) (Finset.mem_univ y)).trans
        (sum_refLaw n).le)
  have htot : ∑ y, (refLaw n y).toReal = 1 := by
    rw [← ENNReal.toReal_sum fun y _ ↦ hfin y, sum_refLaw, ENNReal.toReal_one]
  rw [refLawDft_apply, ← htot]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun y _ ↦ ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg,
    AddChar.norm_apply, mul_one]

/-- Grouping by the first coordinate: for `0 ≤ A`, the series `∑_{h ∈ 𝒫} η(h) d_J(h)^{-A}`,
`J = ⌊n/2⌋`, has sum `∑_{r ≥ 1} ν₄₅(r) max(J - r, 1)^{-A}`. -/
theorem hasSum_holdLaw_mul_chDist_rpow_neg (n : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    HasSum (fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * (chDist n h : ℝ) ^ (-A))
      (∑' r : ℕ, nu45 ((r : ℤ) + 1) *
        (((max ((n / 2 : ℕ) - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A))) := by
  set F : bkPoints → ℝ := fun h ↦ holdLaw h.1.1.toNat h.1.2 * (chDist n h : ℝ) ^ (-A)
  set f : ℕ × ℤ → ℝ := fun x ↦ holdLaw (x.1 + 1) x.2 *
    (((max ((n / 2 : ℕ) - ((x.1 : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A))
  have hd : ∀ x : ℕ × ℤ, (chDist n ((x.1 : ℤ) + 1, x.2) : ℝ) =
      (((max ((n / 2 : ℕ) - ((x.1 : ℤ) + 1)) 1 : ℤ) : ℝ)) := fun x ↦ by
    rw [← Int.cast_natCast (chDist n _), chDist_eq]
    congr 1
    simp only [bkJ]
    omega
  have hf : F ∘ bkPointsEquiv = f := by
    funext x
    simp only [F, f, Function.comp, bkPointsEquiv, Equiv.coe_fn_mk]
    rw [show ((x.1 : ℤ) + 1).toNat = x.1 + 1 by omega, hd]
  have hF0 : ∀ h, 0 ≤ F h := fun h ↦
    mul_nonneg (holdLaw_nonneg _ _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hF1 : ∀ h, F h ≤ holdLaw h.1.1.toNat h.1.2 := fun h ↦
    mul_le_of_le_one_right (holdLaw_nonneg _ _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast one_le_chDist n h)
        (neg_nonpos.2 hA))
  have hFs : Summable F := hasSum_holdLaw_bkPoints.summable.of_nonneg_of_le hF0 hF1
  have hfs : Summable f := by rwa [← hf, bkPointsEquiv.summable_iff]
  have hfib : ∀ m : ℕ, HasSum (fun l : ℤ ↦ f (m, l)) (nu45 ((m : ℤ) + 1) *
      (((max ((n / 2 : ℕ) - ((m : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A))) := fun m ↦ by
    simpa [f] using (hasSum_holdLaw (j := m + 1) (by omega)).mul_right
      ((((max ((n / 2 : ℕ) - ((m : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A)))
  have hsum : ∑' h, F h = ∑' r : ℕ, nu45 ((r : ℤ) + 1) *
      (((max ((n / 2 : ℕ) - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A)) := by
    rw [← bkPointsEquiv.tsum_eq F, show (fun x ↦ F (bkPointsEquiv x)) = f from hf,
      hfs.tsum_prod]
    exact tsum_congr fun m ↦ (hfib m).tsum_eq
  exact hsum ▸ hFs.hasSum

/-- **Explicit decay of the Fourier coefficients.** For a Fourier index `ι`, `n ≥ 1` and a unit
`ξ ∈ G_n`, `|μ̂_n(ξ)| ≤ (D_F(ι) / n)^{A_*(ι)}`. -/
@[collatz_pos_dens "lem_ch_primitive_decay"]
theorem norm_refLawDft_le_Cstar_div_rpow (ι : FIndex) {n : ℕ} (hn : 1 ≤ n) {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) :
    ‖refLawDft n ξ‖ ≤ ((DF ι : ℝ) / n) ^ (Aexp ι : ℝ) := by
  set A : ℝ := (Aexp ι : ℝ) with hAdef
  have hA1 : 1 < A := by rw [hAdef]; exact_mod_cast one_lt_Aexp ι
  have hA52 : A ≤ 5 / 2 := by
    rw [hAdef]
    have : Aexp ι ≤ 5 / 2 := by cases ι <;> norm_num [Aexp]
    exact (Rat.cast_le.2 this).trans_eq (by norm_num)
  have hA0 : 0 ≤ A := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDF : (DF ι : ℝ) = 2 * (Dstar ι : ℝ) + 6 := cast_DF ι
  rcases le_or_gt (n : ℝ) (DF ι : ℝ) with hsmall | hlarge
  · -- small `n`: the trivial bound
    refine (norm_refLawDft_le_one n ξ).trans (Real.one_le_rpow ?_ hA0)
    rwa [one_le_div hnR]
  · -- large `n`
    have hD43 : 2 ^ 43 ≤ Dstar ι := (two_pow_43_le_Dbad ι).trans (Dbad_le_Dstar ι)
    have hnD : 2 * Dstar ι + 6 < n := by
      have : ((2 * Dstar ι + 6 : ℕ) : ℝ) < n := by
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_ofNat]
        linarith
      exact Nat.cast_lt.1 this
    have hJ : Dstar ι + 3 ≤ n / 2 := by omega
    have hmono : ∀ m, Dstar ι ≤ m → m ≤ n / 2 →
        chQm n ξ (epsStar : ℝ) A m ≤ chQm n ξ (epsStar : ℝ) A (m - 1) :=
      fun _ hm _ ↦ chQm_le_chQm_pred_of_Dstar_le ι hξ hm
    have hQ : ∀ h : bkPoints, chQ n ξ (epsStar : ℝ) h ≤
        ((Dstar ι : ℝ) - 1) ^ A * (chDist n h : ℝ) ^ (-A) := fun h ↦
      chQ_le_threshold_rpow_mul n ξ (epsStar : ℝ) hA0 (two_le_Dstar ι) hmono h.2
    have hG := (hasSum_holdLaw_mul_chDist_rpow_neg n hA0).mul_left (((Dstar ι : ℝ) - 1) ^ A)
    have hterm : ∀ h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ (epsStar : ℝ) h ≤
        ((Dstar ι : ℝ) - 1) ^ A * (holdLaw h.1.1.toNat h.1.2 * (chDist n h : ℝ) ^ (-A)) :=
      fun h ↦ by
        rw [mul_left_comm]
        exact mul_le_mul_of_nonneg_left (hQ h) (holdLaw_nonneg _ _)
    have hsf : Summable fun h : bkPoints ↦ holdLaw h.1.1.toNat h.1.2 * chQ n ξ (epsStar : ℝ) h :=
      hG.summable.of_nonneg_of_le
        (fun h ↦ mul_nonneg (holdLaw_nonneg _ _) (chQ_nonneg _ _ _ _)) hterm
    have hJ24 : 2 ^ 24 ≤ n / 2 :=
      (Nat.pow_le_pow_right (by norm_num) (by norm_num) : 2 ^ 24 ≤ 2 ^ 43).trans
        (hD43.trans (by omega))
    have hmom := tsum_nu45_mul_max_rpow_neg_le_sub (A := A) hA1 hA52 (J := ((n / 2 : ℕ) : ℤ))
      (by exact_mod_cast hJ24)
    rw [Int.cast_natCast] at hmom
    set J : ℝ := ((n / 2 : ℕ) : ℝ) with hJdef
    have hJR : (Dstar ι : ℝ) + 3 ≤ J := by
      have := (Nat.cast_le (α := ℝ)).2 hJ
      rwa [Nat.cast_add, Nat.cast_ofNat] at this
    have hn2J : (n : ℝ) ≤ 2 * J + 1 := by
      rw [hJdef]; exact_mod_cast (show n ≤ 2 * (n / 2) + 1 by omega)
    have hD1 : (1 : ℝ) ≤ Dstar ι := Nat.one_le_cast.2 (one_le_Dstar ι)
    have hJpos : 0 < J - 7 / 2 := by linarith
    have hfinal : ((Dstar ι : ℝ) - 1) / (J - 7 / 2) ≤ (DF ι : ℝ) / n := by
      rw [div_le_div_iff₀ hJpos hnR, hDF]
      have h1 := mul_le_mul_of_nonneg_left hn2J (by linarith : (0 : ℝ) ≤ (Dstar ι : ℝ) - 1)
      linarith
    calc ‖refLawDft n ξ‖
        ≤ ∑' h : bkPoints, holdLaw h.1.1.toNat h.1.2 * chQ n ξ (epsStar : ℝ) h :=
          norm_refLawDft_le_tsum_holdLaw_mul_chQ n ξ le_rfl
      _ ≤ ((Dstar ι : ℝ) - 1) ^ A * ∑' r : ℕ, nu45 ((r : ℤ) + 1) *
            (((max ((n / 2 : ℕ) - ((r : ℤ) + 1)) 1 : ℤ) : ℝ) ^ (-A)) :=
          hasSum_le hterm hsf.hasSum hG
      _ ≤ ((Dstar ι : ℝ) - 1) ^ A * (J - 7 / 2) ^ (-A) :=
          mul_le_mul_of_nonneg_left hmom (Real.rpow_nonneg (by linarith) _)
      _ = (((Dstar ι : ℝ) - 1) / (J - 7 / 2)) ^ A := by
          rw [Real.rpow_neg hJpos.le, ← div_eq_mul_inv,
            Real.div_rpow (by linarith) hJpos.le]
      _ ≤ ((DF ι : ℝ) / n) ^ A :=
          Real.rpow_le_rpow (div_nonneg (by linarith) hJpos.le) hfinal hA0

end CollatzPosDens
