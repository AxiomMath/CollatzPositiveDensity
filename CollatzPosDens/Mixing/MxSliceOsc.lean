/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FourierDecay.ChPrimCoeff
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Mixing.MxOsc
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Mixing.MxTailLaw
public import CollatzPosDens.Mixing.MxCollisionOsc
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxHeadMass
public import CollatzPosDens.Mixing.MxSliceGate
public import CollatzPosDens.Mixing.MxHeadCollision
public import CollatzPosDens.Mixing.MxHeadIndex
public import CollatzPosDens.Mixing.MxSliceConvolution
public import CollatzPosDens.Mixing.MxTailDecay

/-!
# Oscillation of one slice

Let `n ≥ 2 ^ 131072` and `k, l, m ∈ ℕ` with `k < n`, `m ≤ n` and `9 n ≤ 10 m`. Then the submass
of the slice gate `Sl(n, k, l)` has oscillation at scale `m` at most
`C_* 20^{A_*} / n^{A_*} · (3^n 2^{-l} 𝐩(Hd(n, k, l)))^{1/2}`, where `A_* = 10241/4096`.

The submass is the convolution `x ↦ ∑_y Hm_{n,k,l}(y) Tl_{n,k,l}(x - y)` of the head mass with
the tail law. If the head gate `Hd(n, k, l)` is empty, the head mass vanishes and so does the
oscillation. Otherwise `20 k ≤ 17 n`, hence `k + 1 ≤ m`, and with
`δ = C_* 20^{A_*} / n^{A_*}` the Fourier decay of the tail law, the collision bound for
oscillations and the head collision bound give
`Osc_{m,n}(Sub)^2 ≤ δ^2 3^n ∑_y Hm(y)^2 ≤ δ^2 3^n 2^{-l} 𝐩(Hd(n, k, l))`.

## Main results

* `CollatzPosDens.oscillation_subMass_mxSliceGate_le_sqrt`: the oscillation bound.

## Implementation notes

The submass takes values in `[0, ∞]` while the oscillation is defined for real functions; the
submass enters through `ENNReal.toReal`, and so does the geometric mass `𝐩(Hd(n, k, l))`, which
is finite since the head gate is finite. The square root is `Real.sqrt` and `2^{-l}` is written
`2⁻¹ ^ l`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §13.9.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

open Finset

/-- **Oscillation of one slice.** Let `n ≥ 2 ^ 131072` and `k, l, m ∈ ℕ` with `k < n`, `m ≤ n`
and `9 n ≤ 10 m`. Then
`Osc_{m,n}(Sub^n_{Sl(n,k,l)}) ≤ C_* 20^{A_*} / n^{A_*} · (3^n 2^{-l} 𝐩(Hd(n, k, l)))^{1/2}`. -/
@[collatz_pos_dens "lem_mx_slice_osc"]
theorem oscillation_subMass_mxSliceGate_le_sqrt {n k l m : ℕ} (hn : 2 ^ 131072 ≤ n)
    (hk : k < n) (hmn : m ≤ n) (h9 : 9 * n ≤ 10 * m) :
    oscillation hmn (fun y => (subMass n (mxSliceGate n k l) y).toReal) ≤
      Cstar * 20 ^ (10241 / 4096 : ℝ) / (n : ℝ) ^ (10241 / 4096 : ℝ) *
        Real.sqrt ((3 : ℝ) ^ n * (2⁻¹ : ℝ) ^ l * (geomMass (mxHeadGate n k l)).toReal) := by
  set H : ResidueGroup n → ℝ := mxHeadMass n k l
  set T : ResidueGroup n → ℝ := fun x => (tailLaw n k l x).toReal
  set δ : ℝ := Cstar * 20 ^ (10241 / 4096 : ℝ) / (n : ℝ) ^ (10241 / 4096 : ℝ) with hδ
  have hconv : ∀ x, (subMass n (mxSliceGate n k l) x).toReal = ∑ y, H y * T (x - y) := by
    intro x
    rw [subMass_mxSliceGate_eq_sum hk x, ENNReal.toReal_sum]
    · refine sum_congr rfl fun y _ => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mxHeadMass_nonneg n k l y)]
    · exact fun y _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (tailLaw_ne_top _ _ _ _)
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  have hδ0 : 0 ≤ δ := by have := Cstar_pos; positivity
  have hrhs : 0 ≤ δ * Real.sqrt ((3 : ℝ) ^ n * (2⁻¹ : ℝ) ^ l *
      (geomMass (mxHeadGate n k l)).toReal) := mul_nonneg hδ0 (Real.sqrt_nonneg _)
  by_cases hHd : mxHeadGate n k l = ∅
  · have hH : ∀ y, H y = 0 := mxHeadMass_eq_zero_of_mxHeadGate_eq_empty hHd
    have hzero : (fun y => (subMass n (mxSliceGate n k l) y).toReal) = fun _ => (0 : ℝ) := by
      funext x
      simp [hconv, hH]
    rw [hzero, oscillation_const]
    exact hrhs
  · have h20 : 20 * k ≤ 17 * n := mxHeadGate_index_le hn hHd
    have hkm : k + 1 ≤ m := by omega
    have hosc := oscillation_sq_le_of_convolution hmn H T _ hconv δ
      (fun ξ hξ => norm_fxDft_tailLaw_le hn1 hkm hmn h9 h20 hξ)
    have hcoll := sum_mxHeadMass_sq_le_geomMass n k l
    have hsq : oscillation hmn (fun y => (subMass n (mxSliceGate n k l) y).toReal) ^ 2 ≤
        (δ * Real.sqrt ((3 : ℝ) ^ n * (2⁻¹ : ℝ) ^ l *
          (geomMass (mxHeadGate n k l)).toReal)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      calc _ ≤ δ ^ 2 * 3 ^ n * ∑ y, H y ^ 2 := hosc
        _ ≤ δ ^ 2 * 3 ^ n * ((2⁻¹ : ℝ) ^ l * (geomMass (mxHeadGate n k l)).toReal) := by
          gcongr
        _ = _ := by ring
    exact (pow_le_pow_iff_left₀ (oscillation_nonneg _ _) hrhs two_ne_zero).1 hsq

end CollatzPosDens
