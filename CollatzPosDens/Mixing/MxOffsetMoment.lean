/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Mixing.MxMomentDenominator
public import CollatzPosDens.Transfer.GeometricTotal

/-!
# A fractional moment of the offset

Let `σ = 65535/65536`. For every length `n`, the fractional moment of the offset under the
geometric weights `2^{-A(w)}` is bounded uniformly in `n`:
$$\sum_{w \in \mathbb{Z}_{\ge 1}^n} 2^{-A(w)} \operatorname{off}(w)^{\sigma} < 2^{20}.$$

More generally, for `0 < σ ≤ 1` with `D = 2^{1+σ} - 1 > 3^σ`, the moment is at most
`1 / (D - 3^σ)`; for `σ = 65535/65536` the lower bound `D - 3^σ > 2^{-20}` gives the claim.

## Main results

* `CollatzPosDens.offsetMoment_le`: the general bound
  `∑_{|w| = n} 2^{-A(w)} off(w)^σ ≤ 1 / (2^{1+σ} - 1 - 3^σ)`.
* `CollatzPosDens.offsetMoment_lt`: the case `σ = 65535/65536`, with bound `2^{20}`.

## Implementation notes

Words of length `n` are the set `{w : Word | w.length = n}`, and the sum is an
unconditional `tsum` in `ℝ≥0∞`, with the summand `2⁻¹ ^ A(w) · ofReal(off w) ^ σ`; all terms
are nonnegative, so this is the sum above computed in `[0, ∞]`.

The source expands `off(w)^σ ≤ ∑_j 3^{σ(j-1)} 2^{-σ S_j}` and sums each term separately.
Here the same subadditivity `(x + y)^σ ≤ x^σ + y^σ` is applied once to the Horner recursion
`off(a w) = 2^{-a} (1 + 3 off(w))`, splitting a word of length `n + 1` into its first letter and
its tail. Writing `M_n` for the moment, this gives `M_{n+1} ≤ D^{-1} (1 + 3^σ M_n)` with
`M_0 = 0`, since `∑_{a ≥ 1} 2^{-(1+σ) a} = D^{-1}` and `∑_{|w| = n} 2^{-A(w)} = 1`; the bound
`M_n ≤ 1 / (D - 3^σ)` is the fixed point of this recursion and follows by induction on `n`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

private lemma tsum_length_zero (f : Word → ℝ≥0∞) :
    ∑' w : {w : Word | w.length = 0}, f w = f [] := by
  refine tsum_eq_single (⟨[], rfl⟩ : {w : Word | w.length = 0}) fun w hw => ?_
  exact absurd (Subtype.ext (List.eq_nil_of_length_eq_zero w.2)) hw

/-- `∑_{a ≥ 1} 2^{-a} 2^{-σ a} = 1 / (2^{1+σ} - 1)`. -/
private lemma tsum_pnat_coeff {σ : ℝ} (hσ : 0 ≤ σ) :
    ∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ((2⁻¹ : ℝ≥0∞) ^ (a : ℕ)) ^ σ =
      ENNReal.ofReal (1 / ((2 : ℝ) ^ (1 + σ) - 1)) := by
  set P : ℝ := (2 : ℝ) ^ (1 + σ) with hP
  have hP1 : 1 < P := Real.one_lt_rpow (by norm_num) (by linarith)
  have hP0 : 0 < P := by linarith
  set q : ℝ := P⁻¹ with hq
  have hq0 : 0 < q := inv_pos.mpr hP0
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hP1
  have h2 : (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]
  have hterm : ∀ a : ℕ, (2⁻¹ : ℝ≥0∞) ^ a * ((2⁻¹ : ℝ≥0∞) ^ a) ^ σ = ENNReal.ofReal (q ^ a) := by
    intro a
    rw [h2, ← ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_rpow_of_nonneg (by positivity) hσ,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [← Real.rpow_pow_comm (by norm_num), ← mul_pow, hq, hP, Real.rpow_add two_pos,
      Real.rpow_one, mul_inv, Real.inv_rpow (by norm_num)]
  simp only [hterm]
  have hs : Summable fun a : ℕ+ => q ^ (a : ℕ) :=
    (summable_geometric_of_lt_one hq0.le hq1).comp_injective PNat.coe_injective
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun a => by positivity) hs]
  congr 1
  rw [← Equiv.pnatEquivNat.symm.tsum_eq]
  simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, pow_succ, tsum_mul_right,
    tsum_geometric_of_lt_one hq0.le hq1]
  rw [hq]
  field_simp

/-- Subadditivity applied to the Horner recursion:
`off(a w)^σ ≤ 2^{-σ a} (1 + 3^σ off(w)^σ)`. -/
private lemma off_cons_rpow_le {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (a : ℕ+) (w : Word) :
    ENNReal.ofReal (off (a :: w) : ℝ) ^ σ ≤
      ((2⁻¹ : ℝ≥0∞) ^ (a : ℕ)) ^ σ * (1 + 3 ^ σ * ENNReal.ofReal (off w : ℝ) ^ σ) := by
  have h0 : (0 : ℝ) ≤ off w := by exact_mod_cast off_nonneg w
  have h : ENNReal.ofReal (off (a :: w) : ℝ) =
      (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * (1 + 3 * ENNReal.ofReal (off w : ℝ)) := by
    rw [off_cons]
    push_cast
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add zero_le_one (by positivity),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_one, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_ofNat, ENNReal.inv_pow]
  rw [h, ENNReal.mul_rpow_of_nonneg _ _ hσ0]
  gcongr
  calc (1 + 3 * ENNReal.ofReal (off w : ℝ)) ^ σ
      ≤ 1 ^ σ + (3 * ENNReal.ofReal (off w : ℝ)) ^ σ := ENNReal.rpow_add_le_add_rpow _ _ hσ0 hσ1
    _ = _ := by rw [ENNReal.one_rpow, ENNReal.mul_rpow_of_nonneg _ _ hσ0]

/-- **Fractional moment of the offset, general exponent.** For `0 < σ ≤ 1` with
`3^σ < 2^{1+σ} - 1`, and every `n`,
`∑_{w ∈ ℤ_{≥1}^n} 2^{-A(w)} off(w)^σ ≤ 1 / (2^{1+σ} - 1 - 3^σ)`. -/
theorem offsetMoment_le {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hD : (3 : ℝ) ^ σ < (2 : ℝ) ^ (1 + σ) - 1) (n : ℕ) :
    ∑' w : {w : Word | w.length = n},
        (2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum * ENNReal.ofReal (off (w : Word) : ℝ) ^ σ ≤
      ENNReal.ofReal (1 / ((2 : ℝ) ^ (1 + σ) - 1 - 3 ^ σ)) := by
  set D : ℝ := (2 : ℝ) ^ (1 + σ) - 1 with hDdef
  have h3 : (3 : ℝ≥0∞) ^ σ = ENNReal.ofReal ((3 : ℝ) ^ σ) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by norm_num) hσ0.le, ENNReal.ofReal_ofNat]
  have h3pos : (0 : ℝ) < 3 ^ σ := by positivity
  have hDpos : 0 < D := by linarith
  have hB : (0 : ℝ) < D - 3 ^ σ := by linarith
  have hmass (n : ℕ) :
      ∑' w : {w : Word | w.length = n}, (2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum = 1 := by
    simpa [geomMass_def, Word.massWeight] using geomMass_setOf_length_eq n
  induction n with
  | zero =>
    rw [tsum_length_zero (fun w : Word => (2⁻¹ : ℝ≥0∞) ^ w.valSum *
      ENNReal.ofReal (off w : ℝ) ^ σ)]
    simp [ENNReal.zero_rpow_of_pos hσ0]
  | succ n ih =>
    rw [Word.tsum_setOf_length_succ n (fun w : Word => (2⁻¹ : ℝ≥0∞) ^ w.valSum *
      ENNReal.ofReal (off w : ℝ) ^ σ)]
    calc _ ≤ ∑' a : ℕ+, ∑' w : {w : Word | w.length = n},
          ((2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ((2⁻¹ : ℝ≥0∞) ^ (a : ℕ)) ^ σ) *
            ((2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum + 3 ^ σ *
              ((2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum * ENNReal.ofReal (off (w : Word) : ℝ) ^ σ)) := by
          refine ENNReal.tsum_le_tsum fun a => ENNReal.tsum_le_tsum fun w => ?_
          rw [Word.valSum_cons, pow_add]
          calc _ ≤ (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * (2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum *
                (((2⁻¹ : ℝ≥0∞) ^ (a : ℕ)) ^ σ *
                  (1 + 3 ^ σ * ENNReal.ofReal (off (w : Word) : ℝ) ^ σ)) := by
                gcongr
                exact off_cons_rpow_le hσ0.le hσ1 a w
            _ = _ := by ring
      _ = (∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ((2⁻¹ : ℝ≥0∞) ^ (a : ℕ)) ^ σ) *
            (1 + 3 ^ σ * ∑' w : {w : Word | w.length = n},
              (2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum * ENNReal.ofReal (off (w : Word) : ℝ) ^ σ) := by
          simp only [ENNReal.tsum_mul_left, ENNReal.tsum_add, hmass,
            ENNReal.tsum_mul_right]
      _ ≤ ENNReal.ofReal (1 / D) *
            (1 + ENNReal.ofReal ((3 : ℝ) ^ σ) * ENNReal.ofReal (1 / (D - 3 ^ σ))) := by
          rw [tsum_pnat_coeff hσ0.le, ← h3]
          gcongr
      _ = ENNReal.ofReal (1 / (D - 3 ^ σ)) := by
          rw [← ENNReal.ofReal_mul h3pos.le, ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
          ring

/-- **Fractional moment of the offset.** With `σ = 65535/65536`, for every `n`,
`∑_{w ∈ ℤ_{≥1}^n} 2^{-A(w)} off(w)^σ < 2^{20}`. -/
@[collatz_pos_dens "lem_mx_offset_moment"]
theorem offsetMoment_lt (n : ℕ) :
    ∑' w : {w : Word | w.length = n},
        (2⁻¹ : ℝ≥0∞) ^ (w : Word).valSum *
          ENNReal.ofReal (off (w : Word) : ℝ) ^ (65535 / 65536 : ℝ) < 2 ^ 20 := by
  have h := two_pow_neg_twenty_lt_momentDenominator
  have h20 : (2 : ℝ) ^ (-20 : ℤ) = 1 / 2 ^ 20 := by norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-20 : ℤ) := by positivity
  refine (offsetMoment_le (by norm_num) (by norm_num) (by linarith) n).trans_lt ?_
  rw [show (2 : ℝ≥0∞) ^ 20 = ENNReal.ofReal (2 ^ 20) by
    rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat],
    ENNReal.ofReal_lt_ofReal_iff (by norm_num), one_div_lt (by linarith) (by norm_num)]
  rwa [← h20]

end CollatzPosDens
