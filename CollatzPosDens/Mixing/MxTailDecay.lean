/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FourierDecay.ChPrimitiveDecay
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02DF
public import CollatzPosDens.Characters.FxDft
public import CollatzPosDens.Characters.FxCharacterInt
public import CollatzPosDens.Characters.FxCharacterNeg
public import CollatzPosDens.Mixing.MxTailLaw
public import CollatzPosDens.Mixing.MxDftReduction
public import CollatzPosDens.Transfer.S02Reduction
public import CollatzPosDens.Transfer.S02DyadicReduction
public import CollatzPosDens.Transfer.FxRefLawBounded
public import CollatzPosDens.Transfer.FxRefLawTotal

/-!
# Fourier decay of the tail law

Let `ι` be a Fourier index and `n, k, l, m ∈ ℕ` with `n ≥ 1`, `k < m ≤ n` and
`15 (m - k) ≥ 2 n`. For every `ξ ∈ G_n` with `3^m ξ ≠ 0`,
$$\bigl|\widehat{\mathrm{Tl}_{n,k,l}}(\xi)\bigr| \le
\Bigl(\frac{15}{2} D_F(\iota)\Bigr)^{A_*(\iota)} n^{-A_*(\iota)}.$$
In the proof sketch below `ι` is fixed and suppressed: `D_F = D_F(ι)`, `A_* = A_*(ι)`.

Write `T = n - k - 1`. The transform of the tail law is a Fourier coefficient of the reference
law at level `T`: `Tl̂_{n,k,l}(ξ) = μ̂_T(ω)` with `ω = π_{n,T}(2^{-l} ξ)`, because
`e_n(3^{k+1} y) = e_T(π_{n,T} y)`. The hypothesis `3^m ξ ≠ 0` says that `ω̃` is not divisible
by `3^{n-m}`; writing `ω = 3^j η` with `3 ∤ η̃` and `j < n - m`, the reduction of Fourier
coefficients gives `μ̂_T(ω) = μ̂_r(π_{T,r} η)` with `r = T - j ≥ m - k ≥ 2n / 15`, and the
explicit decay at units bounds this by `(D_F / r)^{A_*}`; since `D_F ≥ 2^42 + 6 > 0` and
`x ↦ x^{A_*}` is monotone on `[0, ∞)`, this is at most `(15 D_F / 2)^{A_*} n^{-A_*}`.

## Main results

* `CollatzPosDens.fxDft_tailLaw_eq_refLawDft`: the transform of the tail law as a Fourier
  coefficient of the reference law.
* `CollatzPosDens.norm_refLawDft_le_of_not_dvd`: decay of `μ̂_T(ω)` when `3^a ∤ ω̃`.
* `CollatzPosDens.norm_fxDft_tailLaw_le`: the Fourier decay of the tail law.

## Implementation notes

The tail law takes values in `[0, ∞]`; as for the reference law, its transform is that of the
complex-valued function `x ↦ Tl_{n,k,l}(x)^ℝ`. The exponent `A_*(ι)` is not an integer, so the
powers are real powers `Real.rpow`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §12.8.
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The Fourier transform of the tail law at level `T + (k + 1)` is a Fourier coefficient of the
reference law at level `T`: `Tl̂_{T+k+1,k,l}(ξ) = μ̂_T(π_{T+k+1,T}(2^{-l} ξ))`. -/
theorem fxDft_tailLaw_eq_refLawDft (T k l : ℕ)
    (ξ : ResidueGroup (T + (k + 1))) :
    fxDft (T + (k + 1)) (fun x => ((tailLaw (T + (k + 1)) k l x).toReal : ℂ)) ξ =
      refLawDft T (residueReduction (Nat.le_add_right T (k + 1)) (2⁻¹ ^ l * ξ)) := by
  set p := residueReduction (Nat.le_add_right T (k + 1))
  rw [fxDft_apply, refLawDft_apply]
  simp only [tailLaw, tailLawCoeff_eq]
  suffices aux : ∀ N, N = T → ∑ x : ResidueGroup (T + (k + 1)),
      ((∑ z ∈ univ.filter (fun z : ResidueGroup N =>
          3 ^ (k + 1) * 2⁻¹ ^ l * (z.val : ResidueGroup (T + (k + 1))) = x),
        refLaw N z).toReal : ℂ) * fxChar (T + (k + 1)) (-(ξ * x)) =
      ∑ y : ResidueGroup T, ((refLaw T y).toReal : ℂ) * fxChar T (-(p (2⁻¹ ^ l * ξ) * y)) from
    aux _ (by omega)
  intro N hNT
  subst N
  have hterm : ∀ z : ResidueGroup T,
      ((refLaw T z).toReal : ℂ) *
          fxChar (T + (k + 1)) (-(ξ * (3 ^ (k + 1) * 2⁻¹ ^ l * (z.val : ResidueGroup _)))) =
        ((refLaw T z).toReal : ℂ) * fxChar T (-(p (2⁻¹ ^ l * ξ) * z)) := fun z => by
    rw [show -(ξ * (3 ^ (k + 1) * 2⁻¹ ^ l * (z.val : ResidueGroup (T + (k + 1))))) =
        3 ^ (k + 1) * (-(2⁻¹ ^ l * ξ * (z.val : ResidueGroup (T + (k + 1))))) by ring,
      fxChar_three_pow_mul, map_neg, map_mul, residueReduction_natCast, ZMod.natCast_zmod_val]
  simp_rw [← hterm]
  rw [← Finset.sum_fiberwise Finset.univ
    (fun z : ResidueGroup T => 3 ^ (k + 1) * 2⁻¹ ^ l * (z.val : ResidueGroup (T + (k + 1))))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.toReal_sum (fun y _ => refLaw_ne_top _ y), Complex.ofReal_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun z hz => by rw [(Finset.mem_filter.1 hz).2]

/-- For a Fourier index `ι`, if `a ≤ T` and `3^a` does not divide the least nonnegative
representative of `ω ∈ G_T`, then `|μ̂_T(ω)| ≤ (D_F(ι) / (T + 1 - a))^{A_*(ι)}`. -/
theorem norm_refLawDft_le_of_not_dvd (ι : FIndex) {T a : ℕ} (haT : a ≤ T) (ω : ResidueGroup T)
    (hω : ¬ 3 ^ a ∣ ω.val) :
    ‖refLawDft T ω‖ ≤ ((DF ι : ℝ) / ((T + 1 - a : ℕ) : ℝ)) ^ (Aexp ι : ℝ) := by
  have hω0 : ω.val ≠ 0 := fun h => hω (h ▸ dvd_zero _)
  obtain ⟨j, hj1, hj2⟩ : ∃ j, 3 ^ j ∣ ω.val ∧ ¬ 3 ^ (j + 1) ∣ ω.val :=
    ⟨padicValNat 3 ω.val, pow_padicValNat_dvd, pow_succ_padicValNat_not_dvd hω0⟩
  have hja : j < a := not_le.1 fun h => hω ((pow_dvd_pow 3 h).trans hj1)
  obtain ⟨η₀, hη₀⟩ := hj1
  have h3η : ¬ 3 ∣ η₀ := by
    rintro ⟨t, rfl⟩
    exact hj2 ⟨t, by rw [hη₀, pow_succ]; ring⟩
  obtain ⟨r, rfl⟩ : ∃ r, T = r + j := ⟨T - j, by omega⟩
  have hωη : ω = 3 ^ j * (η₀ : ResidueGroup (r + j)) := by
    rw [← ZMod.natCast_zmod_val ω, hη₀]
    push_cast
    rfl
  have hunit : IsResidueUnit (η₀ : ResidueGroup r) := by
    rw [IsResidueUnit, ZMod.val_natCast]
    exact fun h => h3η ((Nat.dvd_mod_iff (dvd_pow_self 3 (by omega))).1 h)
  rw [hωη, refLawDft_three_pow_mul, residueReduction_natCast]
  refine (norm_refLawDft_le_Cstar_div_rpow ι (by omega) hunit).trans ?_
  have hpos : (0 : ℝ) < ((r + j + 1 - a : ℕ) : ℝ) := mod_cast (show 0 < r + j + 1 - a by omega)
  have hDF : (0 : ℝ) ≤ (DF ι : ℝ) := by exact_mod_cast (DF_pos ι).le
  exact Real.rpow_le_rpow (div_nonneg hDF (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_left hDF hpos (mod_cast (show r + j + 1 - a ≤ r by omega)))
    (by exact_mod_cast (Aexp_pos ι).le)

/-- In `G_n`, if the reduction of `ξ` modulo `3^{n-m}` vanishes then `3^m ξ = 0`. -/
private theorem mxTailDecay_three_pow_mul_eq_zero {n m : ℕ} (hmn : m ≤ n) (ξ : ResidueGroup n)
    (hξ : residueReduction (Nat.sub_le n m) ξ = 0) : (3 : ResidueGroup n) ^ m * ξ = 0 := by
  obtain ⟨t, ht⟩ := (residueReduction_eq_zero_iff _ ξ).1 hξ
  rw [← ZMod.natCast_zmod_val ξ, ht]
  have h : (3 : ResidueGroup n) ^ m * ((3 ^ (n - m) * t : ℕ) : ResidueGroup n) =
      ((3 ^ n : ℕ) : ResidueGroup n) * t := by
    push_cast
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
  rw [h, ZMod.natCast_self, zero_mul]

/-- **Fourier decay of the tail law.** Let `ι` be a Fourier index, `n ≥ 1`, `k < m ≤ n` and
`15 (m - k) ≥ 2 n`. For every `ξ ∈ G_n` with `3^m ξ ≠ 0`,
`|Tl̂_{n,k,l}(ξ)| ≤ (15 D_F(ι) / 2)^{A_*(ι)} n^{-A_*(ι)}`. -/
@[collatz_pos_dens "lem_mx_tail_decay"]
theorem norm_fxDft_tailLaw_le (ι : FIndex) {n k l m : ℕ} (hn : 1 ≤ n) (hmn : m ≤ n) (hkm : k < m)
    (h15 : 2 * n ≤ 15 * (m - k)) {ξ : ResidueGroup n}
    (hξ : (3 : ResidueGroup n) ^ m * ξ ≠ 0) :
    ‖fxDft n (fun x => ((tailLaw n k l x).toReal : ℂ)) ξ‖ ≤
      (15 / 2 * (DF ι : ℝ)) ^ (Aexp ι : ℝ) * (n : ℝ) ^ (-(Aexp ι : ℝ)) := by
  obtain ⟨T, rfl⟩ : ∃ T, n = T + (k + 1) := ⟨n - (k + 1), by omega⟩
  rw [fxDft_tailLaw_eq_refLawDft]
  have ha : T + (k + 1) - m ≤ T := by omega
  have hnd : ¬ 3 ^ (T + (k + 1) - m) ∣
      (residueReduction (Nat.le_add_right T (k + 1)) (2⁻¹ ^ l * ξ)).val := by
    intro hd
    apply hξ
    apply mxTailDecay_three_pow_mul_eq_zero hmn
    have h0 : residueReduction ha
        (residueReduction (Nat.le_add_right T (k + 1)) (2⁻¹ ^ l * ξ)) = 0 :=
      (residueReduction_eq_zero_iff ha _).2 hd
    rw [residueReduction_residueReduction, map_mul] at h0
    have h2 := congrArg (residueReduction (Nat.sub_le (T + (k + 1)) m))
      (two_pow_mul_inv_two_pow (T + (k + 1)) l)
    rw [map_mul, map_one] at h2
    linear_combination (residueReduction (Nat.sub_le (T + (k + 1)) m) (2 ^ l)) * h0 -
      (residueReduction (Nat.sub_le (T + (k + 1)) m) ξ) * h2
  refine (norm_refLawDft_le_of_not_dvd ι ha _ hnd).trans ?_
  rw [show T + 1 - (T + (k + 1) - m) = m - k by omega]
  set N : ℕ := T + (k + 1)
  have hNpos : (0 : ℝ) < (N : ℝ) := mod_cast (show 0 < N by omega)
  have hDF : (0 : ℝ) < (DF ι : ℝ) := by exact_mod_cast DF_pos ι
  have hmk : (0 : ℝ) < ((m - k : ℕ) : ℝ) := mod_cast (show 0 < m - k by omega)
  have hle : 2 * (N : ℝ) ≤ 15 * ((m - k : ℕ) : ℝ) := by exact_mod_cast h15
  have hA : (0 : ℝ) ≤ (Aexp ι : ℝ) := by exact_mod_cast (Aexp_pos ι).le
  calc ((DF ι : ℝ) / ((m - k : ℕ) : ℝ)) ^ (Aexp ι : ℝ)
      ≤ (15 / 2 * (DF ι : ℝ) / (N : ℝ)) ^ (Aexp ι : ℝ) := by
        refine Real.rpow_le_rpow (div_nonneg hDF.le hmk.le) ?_ hA
        rw [div_le_div_iff₀ hmk hNpos]
        nlinarith
    _ = (15 / 2 * (DF ι : ℝ)) ^ (Aexp ι : ℝ) * (N : ℝ) ^ (-(Aexp ι : ℝ)) := by
        rw [Real.div_rpow (by positivity) hNpos.le, Real.rpow_neg hNpos.le, div_eq_mul_inv]

end CollatzPosDens
