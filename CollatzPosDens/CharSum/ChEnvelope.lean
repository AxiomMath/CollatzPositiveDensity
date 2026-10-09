/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChEnvelopeAbs
public import CollatzPosDens.CharSum.ChPairPoint
public import CollatzPosDens.CharSum.ChPairProduct
public import CollatzPosDens.CharSum.ChPascalMass
public import CollatzPosDens.Characters.FxCharacter
public import CollatzPosDens.Characters.FxCharacterAbs
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.CharSum.ChPairFactor
public import CollatzPosDens.CharSum.ChPairFactorRange
public import CollatzPosDens.CharSum.ChEnvelopeRhs
public import CollatzPosDens.CharSum.ChEnvelopeRhsRange
public import CollatzPosDens.CharSum.ChFiberMass

/-!
# The envelope bound for the paired character series

Fix `n : ℕ` and a frequency `ξ ∈ G_n`. For all `k j : ℕ` and `s ∈ ℤ`, writing
`k' = ⌊k / 2⌋`,
`|∑_{w ∈ ℤ_{≥1}^k} 2^{-A(w)} Ep(j, s; w)|
  ≤ ∑_{b ∈ ℤ^{k'}} ∏_{i=1}^{k'} ϖ(b_i) ∏_{i=1}^{k'} Fp(j + i - 1, s + b_1 + ⋯ + b_{i-1}, b_i)`.

For `k ≤ 1` the right side is `1` and the left side is at most the geometric mass
`𝐩(ℤ_{≥1}^k) = 1`, since `|Ep| = 1`. For `k ≥ 2` one writes `w = (a₁, a₂) w'`, groups the
absolutely convergent series by `b = a₁ + a₂`, bounds each fiber by `ϖ(b) Fp(j, s, b)` and the
remaining series by induction, and recombines `b` with the shorter tuple into a tuple of
length `k'`.

## Main results

* `CollatzPosDens.norm_tsum_chPairProduct_le`: the envelope bound.

## Implementation notes

`ℤ_{≥1}^k` is the subtype of words of length `k`, and `ℤ^{k'}` is `Fin k' → ℤ` with indices
`i = 0, …, k' - 1`, so that the factor of index `i` is `Fp(j + i, s + ∑_{l < i} b_l, b_i)`, as in
`CollatzPosDens.summable_chEnvelopeRhs`. No hypothesis `j ≥ 1` is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.1.
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- The paired character series has modulus at most `𝐩(ℤ_{≥1}^k) = 1`. -/
private theorem norm_tsum_chPairProduct_le_one (n : ℕ) (ξ : ResidueGroup n) (k j : ℕ) (s : ℤ) :
    ‖∑' w : {w : Word | w.length = k}, (2⁻¹ : ℂ) ^ (w : Word).valSum *
      chPairProduct n ξ j s w‖ ≤ 1 := by
  refine (norm_tsum_le_tsum_norm (summable_norm_chPairProduct_series n ξ k j s)).trans
    (le_of_eq ?_)
  have h := congrArg ENNReal.toReal (geomMass_setOf_length_eq k)
  rw [geomMass_def, ENNReal.tsum_toReal_eq (fun w => by simp [Word.massWeight])] at h
  rw [ENNReal.toReal_one] at h
  rw [← h]
  refine tsum_congr fun w => ?_
  simp [norm_chPairProduct, Word.massWeight, ENNReal.toReal_pow, ENNReal.toReal_inv]

/-- The partial sums of a tuple `Fin.cons x p` below `i.succ` are `x` plus those of `p`. -/
private theorem sum_Iio_succ_cons {m : ℕ} (x : ℤ) (p : Fin m → ℤ) (i : Fin m) :
    ∑ l ∈ Iio i.succ, (Fin.cons x p : Fin (m + 1) → ℤ) l = x + ∑ l ∈ Iio i, p l := by
  have h : Iio i.succ = insert 0 ((Iio i).image Fin.succ) := by
    rw [Fin.finsetImage_succ_Iio]
    ext l
    simp only [mem_Iio, mem_insert, mem_Ioo]
    rcases Fin.eq_zero_or_eq_succ l with rfl | ⟨l, rfl⟩
    · simp
    · simp [Fin.succ_pos]
  rw [h, sum_insert (by simp), sum_image (Fin.succ_injective _).injOn]
  simp

/-- The envelope series of length `m + 1` is the sum over `b` of `ϖ(b) Fp(j, s, b)` times the
envelope series of length `m` at `(j + 1, s + b)`. -/
private theorem hasSum_tsum_chEnvelopeRhs_succ (n : ℕ) (ξ : ResidueGroup n) (m j : ℕ) (s : ℤ) :
    HasSum (fun b : ℕ => varpi b * chPairFactor n ξ j s b *
      ∑' b' : Fin m → ℤ, (∏ i, varpi (b' i)) *
        ∏ i : Fin m, chPairFactor n ξ (j + 1 + i) (s + b + ∑ l ∈ Iio i, b' l) (b' i))
      (∑' b : Fin (m + 1) → ℤ, (∏ i, varpi (b i)) *
        ∏ i : Fin (m + 1), chPairFactor n ξ (j + i) (s + ∑ l ∈ Iio i, b l) (b i)) := by
  set R : ℤ → ℝ := fun t => ∑' b' : Fin m → ℤ, (∏ i, varpi (b' i)) *
    ∏ i : Fin m, chPairFactor n ξ (j + 1 + i) (t + ∑ l ∈ Iio i, b' l) (b' i)
  have hR01 (t : ℤ) : R t ∈ Set.Icc (0 : ℝ) 1 := tsum_chEnvelopeRhs_mem_Icc n ξ m (j + 1) t
  set u : ℤ → ℝ := fun b => varpi b * chPairFactor n ξ j s b * R (s + b) with hu
  have hu0 (b : ℤ) : 0 ≤ u b :=
    mul_nonneg (mul_nonneg (varpi_nonneg b) (chPairFactor_nonneg _ _ _ _ _)) (hR01 _).1
  have hu1 (b : ℤ) : u b ≤ varpi b := by
    refine (mul_le_of_le_one_right (mul_nonneg (varpi_nonneg b)
      (chPairFactor_nonneg _ _ _ _ _)) (hR01 _).2).trans ?_
    exact mul_le_of_le_one_right (varpi_nonneg b) (chPairFactor_le_one _ _ _ _ _)
  have hsum : Summable fun b : ℕ => u b :=
    (hasSum_varpi.summable.comp_injective Nat.cast_injective).of_nonneg_of_le
      (fun b => hu0 b) (fun b => hu1 b)
  refine hsum.hasSum_iff.mpr ?_
  -- Split `β ∈ ℤ^{m+1}` as `Fin.cons b b'`.
  have hsplit (b : ℤ) (b' : Fin m → ℤ) :
      (∏ i, varpi ((Fin.cons b b' : Fin (m + 1) → ℤ) i)) *
        ∏ i : Fin (m + 1), chPairFactor n ξ (j + i)
          (s + ∑ l ∈ Iio i, (Fin.cons b b' : Fin (m + 1) → ℤ) l)
          ((Fin.cons b b' : Fin (m + 1) → ℤ) i) =
      varpi b * chPairFactor n ξ j s b * ((∏ i, varpi (b' i)) *
        ∏ i : Fin m, chPairFactor n ξ (j + 1 + i) (s + b + ∑ l ∈ Iio i, b' l) (b' i)) := by
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, sum_Iio_succ_cons, Fin.val_succ,
      Fin.val_zero, add_zero]
    have h0 : (Iio (0 : Fin (m + 1))) = ∅ := by ext l; simp
    rw [h0, sum_empty, add_zero]
    have h1 : ∀ i : Fin m, j + (i + 1 : ℕ) = j + 1 + i := fun i => by omega
    simp only [h1, add_assoc]
    ring
  have hsumm := (Fin.consEquiv fun _ : Fin (m + 1) => ℤ).summable_iff.mpr
    (summable_chEnvelopeRhs n ξ (m + 1) j s)
  rw [← (Fin.consEquiv fun _ : Fin (m + 1) => ℤ).tsum_eq]
  refine Eq.trans ?_ hsumm.tsum_prod.symm
  simp only [Function.comp_apply, Fin.consEquiv_apply, hsplit, tsum_mul_left]
  change ∑' b : ℕ, u b = ∑' b : ℤ, u b
  refine Function.Injective.tsum_eq Nat.cast_injective (f := u) ?_
  intro b hb
  have : 2 ≤ b := by
    by_contra h
    exact hb (by simp [hu, varpi_of_le_one (show b ≤ 1 by omega)])
  exact ⟨b.toNat, by simp; omega⟩

/-- Peeling off the first two letters of the paired character series and grouping by their
sum `b = a₁ + a₂`. -/
private theorem tsum_chPairProduct_length_add_two (n : ℕ) (ξ : ResidueGroup n) (k j : ℕ) (s : ℤ) :
    ∑' w : {w : Word | w.length = k + 2}, (2⁻¹ : ℂ) ^ (w : Word).valSum *
      chPairProduct n ξ j s w =
    ∑' b : ℕ, (∑ p ∈ (antidiagonal b).filter (fun p => 1 ≤ p.1 ∧ 1 ≤ p.2),
        (2 : ℂ) ^ (-(b : ℤ)) *
          fxChar n (-((2 : ResidueGroup n) ^ p.2 + 3) * chPairPoint n j (s + b) * ξ)) *
      ∑' w : {w : Word | w.length = k}, (2⁻¹ : ℂ) ^ (w : Word).valSum *
        chPairProduct n ξ (j + 1) (s + b) w := by
  set L : ℤ → ℂ := fun t => ∑' w : {w : Word | w.length = k}, (2⁻¹ : ℂ) ^ (w : Word).valSum *
    chPairProduct n ξ (j + 1) t w with hL
  set c : ℕ → ℕ → ℂ := fun b a₂ =>
    (2 : ℂ) ^ (-(b : ℤ)) *
      fxChar n (-((2 : ResidueGroup n) ^ a₂ + 3) * chPairPoint n j (s + b) * ξ) with hc
  let e : (ℕ+ × ℕ+) × {w : Word | w.length = k} ≃ {w : Word | w.length = k + 2} :=
    (Equiv.prodAssoc _ _ _).trans
      ((Equiv.prodCongr (Equiv.refl ℕ+) (Word.consLengthEquiv k)).trans
        (Word.consLengthEquiv (k + 1)))
  have he (a₁ a₂ : ℕ+) (w : {w : Word | w.length = k}) :
      (e ((a₁, a₂), w) : Word) = a₁ :: a₂ :: (w : Word) := rfl
  have hterm (a₁ a₂ : ℕ+) (w : {w : Word | w.length = k}) :
      (2⁻¹ : ℂ) ^ (e ((a₁, a₂), w) : Word).valSum * chPairProduct n ξ j s (e ((a₁, a₂), w)) =
        c ((a₁ : ℕ) + a₂) a₂ * ((2⁻¹ : ℂ) ^ (w : Word).valSum *
          chPairProduct n ξ (j + 1) (s + (((a₁ : ℕ) + a₂ : ℕ) : ℤ)) w) := by
    rw [he, chPairProduct_cons_cons, Word.valSum_cons, Word.valSum_cons]
    have hs : s + ((a₁ : ℕ) : ℤ) + ((a₂ : ℕ) : ℤ) = s + (((a₁ : ℕ) + a₂ : ℕ) : ℤ) := by
      push_cast; ring
    simp only [hc, hs, neg_mul, zpow_neg, zpow_natCast, inv_pow, pow_add]
    ring
  have hT := (summable_norm_chPairProduct_series n ξ (k + 2) j s).of_norm
  rw [← e.summable_iff] at hT
  rw [← e.tsum_eq]
  refine (hT.tsum_prod).trans ?_
  have hF (p : ℕ+ × ℕ+) :
      ∑' w : {w : Word | w.length = k}, (2⁻¹ : ℂ) ^ (e (p, w) : Word).valSum *
        chPairProduct n ξ j s (e (p, w)) =
      c ((p.1 : ℕ) + p.2) p.2 * L (s + (((p.1 : ℕ) + p.2 : ℕ) : ℤ)) := by
    simp only [hterm, tsum_mul_left]
    rfl
  have hFs := hT.prod
  simp only [Function.comp_apply, hF] at hFs ⊢
  -- Extend from `ℕ+ × ℕ+` to `ℕ × ℕ` by zero.
  set G : ℕ × ℕ → ℂ := fun q =>
    if 1 ≤ q.1 ∧ 1 ≤ q.2 then c (q.1 + q.2) q.2 * L (s + (q.1 + q.2 : ℕ)) else 0 with hG
  have hGφ (p : ℕ+ × ℕ+) : G (Prod.map PNat.val PNat.val p) =
      c ((p.1 : ℕ) + p.2) p.2 * L (s + (((p.1 : ℕ) + p.2 : ℕ) : ℤ)) := by
    simp [hG, Nat.one_le_iff_ne_zero, PNat.ne_zero]
  have hφ : Function.Injective (Prod.map PNat.val PNat.val) :=
    Function.Injective.prodMap PNat.coe_injective PNat.coe_injective
  have hsupp : ∀ q ∉ Set.range (Prod.map PNat.val PNat.val), G q = 0 := by
    intro q hq
    simp only [hG]
    split_ifs with h
    · exact absurd ⟨(⟨q.1, h.1⟩, ⟨q.2, h.2⟩), rfl⟩ hq
    · rfl
  simp only [← hGφ] at hFs ⊢
  have hGs : Summable G := (hφ.summable_iff hsupp).mp hFs
  rw [hφ.tsum_eq (fun q hq => by_contra fun h => hq (hsupp q h)),
    ← HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq]
  refine (Summable.tsum_sigma (f := fun c => G (HasAntidiagonal.sigmaAntidiagonalEquivProd c))
    (hGs.comp_injective (Equiv.injective _))).trans ?_
  refine tsum_congr fun b => ?_
  simp only [HasAntidiagonal.sigmaAntidiagonalEquivProd, Equiv.coe_fn_mk]
  rw [Finset.tsum_subtype (antidiagonal b) G, sum_mul, sum_filter]
  refine sum_congr rfl fun q hq => ?_
  rw [mem_antidiagonal] at hq
  simp only [hG, hq]
  split_ifs <;> simp [hc, hL]

/-- **The envelope bound.** For all `k`, `j` and `s`, writing `k' = ⌊k / 2⌋`,
`|∑_{w ∈ ℤ_{≥1}^k} 2^{-A(w)} Ep(j, s; w)|
  ≤ ∑_{b ∈ ℤ^{k'}} ∏_i ϖ(b_i) ∏_i Fp(j + i - 1, s + b_1 + ⋯ + b_{i-1}, b_i)`. -/
@[collatz_pos_dens "lem_ch_envelope"]
theorem norm_tsum_chPairProduct_le (n : ℕ) (ξ : ResidueGroup n) :
    ∀ (k j : ℕ) (s : ℤ),
      ‖∑' w : {w : Word | w.length = k}, (2⁻¹ : ℂ) ^ (w : Word).valSum *
          chPairProduct n ξ j s w‖ ≤
        ∑' b : Fin (k / 2) → ℤ, (∏ i, varpi (b i)) *
          ∏ i : Fin (k / 2), chPairFactor n ξ (j + i) (s + ∑ l ∈ Iio i, b l) (b i)
  | 0, j, s => (norm_tsum_chPairProduct_le_one n ξ 0 j s).trans_eq (by simp)
  | 1, j, s => (norm_tsum_chPairProduct_le_one n ξ 1 j s).trans_eq (by simp)
  | k + 2, j, s => by
    rw [tsum_chPairProduct_length_add_two, show (k + 2) / 2 = k / 2 + 1 by omega]
    refine tsum_of_norm_bounded (hasSum_tsum_chEnvelopeRhs_succ n ξ (k / 2) j s) fun b => ?_
    rw [norm_mul]
    exact mul_le_mul (norm_sum_chFiber_eq n ξ j s b).le
      (norm_tsum_chPairProduct_le n ξ k (j + 1) _)
      (norm_nonneg _) (mul_nonneg (varpi_nonneg _) (chPairFactor_nonneg _ _ _ _ _))

end CollatzPosDens
