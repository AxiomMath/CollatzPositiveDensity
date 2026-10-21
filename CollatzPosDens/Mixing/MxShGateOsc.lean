/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Transfer.S02Aexp
public import CollatzPosDens.Transfer.S02Bstar
public import CollatzPosDens.Transfer.S02DF
public import CollatzPosDens.Mixing.MxOsc
public import CollatzPosDens.Mixing.MxSubmass
public import CollatzPosDens.Mixing.MxTailLaw
public import CollatzPosDens.Mixing.MxCollisionOsc
public import CollatzPosDens.Mixing.MxTailDecay
public import CollatzPosDens.Mixing.MxShHeight
public import CollatzPosDens.Mixing.MxShGate
public import CollatzPosDens.Mixing.MxShHeadMeasure
public import CollatzPosDens.Mixing.MxShKhi
public import CollatzPosDens.Mixing.MxShShellWidth
public import CollatzPosDens.Mixing.MxShSlice
public import CollatzPosDens.Mixing.MxShGateSquare
public import CollatzPosDens.Mixing.MxShSliceConvolution
public import CollatzPosDens.Mixing.MxShWindowHigh

/-!
# Oscillation of one retained slice of the shell cut

Let `ι` be a Fourier index, let `n ≥ n₀ = 2^80` and `m ≤ n` with `25 n ≤ 27 m`, let `d` be an
integer with `k^{sh,-}_n ≤ d ≤ k^{sh,+}_n - 1`, and let `j ∈ ℕ`. Then the submass of the slice
`Sl^{sh}_n(d, j)` satisfies
$$\mathrm{Osc}_{m,n}\bigl(\mathrm{Sub}^n_{\mathrm{Sl}^{\mathrm{sh}}_n(d,j)}\bigr)
  \le B_{\mathrm F}(ι)\, n^{-A_*(ι)}
  \sqrt{(W_j + 2)\, 2^{-(H^{\mathrm{sh}}_n - 1)}\, \#\mathrm{Hd}^{\mathrm{sh}}_n(d, j)}.$$

Since `21600 k^{sh,+}_n < 17119 n + 32400` and `27 m ≥ 25 n`, we get `d < n`, `d - 1 < m` and
`15 (m - (d - 1)) ≥ 2 n`. With `N = H^{sh}_n - 1`, the submass of the slice is the convolution
`x ↦ ∑_y Γ^{sh}_{n,d,j}(y) Tl_{n,d-1,N}(x - y)`. The tail law has Fourier coefficients at most
`B_F(ι) n^{-A_*(ι)}` off the subgroup `3^m ξ = 0`, so the collision bound for oscillations
together with `3^n ∑_y Γ^{sh}_{n,d,j}(y)^2 ≤ (W_j + 2) 2^{-N} #Hd^{sh}_n(d, j)` gives the square
of the claim.

## Main results

* `CollatzPosDens.oscillation_subMass_mxShSlice_shRetainedHeads_le`: the oscillation bound.

## Implementation notes

The submass takes values in `[0, ∞]`; it enters the real-valued oscillation through
`ENNReal.toReal`, and it is finite since the slice consists of words of length `n`. The integer
`d` is a natural number with `1 ≤ d`: the lower window end satisfies `k^{sh,-}_n ≥ 1` for
`n ≥ n₀`, and the bound holds for every `1 ≤ d ≤ k^{sh,+}_n - 1`, so the hypothesis
`k^{sh,-}_n ≤ d` is replaced by the weaker `1 ≤ d`. The square root is `Real.sqrt`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

open Finset

/-- **Oscillation of one retained slice.** Let `ι` be a Fourier index, `n ≥ n₀`, `m ≤ n` with
`25 n ≤ 27 m`, `1 ≤ d ≤ k^{sh,+}_n - 1` and `j ∈ ℕ`. Then `Osc_{m,n}(Sub^n_{Sl^sh_n(d,j)}) ≤`
`B_F(ι) n^{-A_*(ι)} √((W_j + 2) 2^{-(H^sh_n - 1)} #Hd^sh_n(d,j))`.
-/
@[collatz_pos_dens "lem_mx_sh_gate_osc"]
theorem oscillation_subMass_mxShSlice_shRetainedHeads_le (ι : FIndex) {n m d : ℕ}
    (hn : mxGateLevel ≤ n) (hmn : m ≤ n) (h25 : 25 * n ≤ 27 * m) (hd1 : 1 ≤ d)
    (hdhi : (d : ℤ) ≤ shKHi n - 1) (j : ℕ) :
    oscillation hmn (fun y => (subMass n (mxShSlice n d j) y).toReal) ≤
      fourierPrefactor ι * (n : ℝ) ^ (-(Aexp ι : ℝ)) *
        Real.sqrt (((shShellWidth j : ℝ) + 2) * ((2 : ℝ) ^ (shHeight n - 1))⁻¹ *
          #(shRetainedHeads n d j)) := by
  set N := shHeight n - 1
  have hwin := mul_shKHi_lt hn
  have hn80 : 2 ^ 80 ≤ n := by rwa [mxGateLevel_def] at hn
  have hdZ : 21600 * (d : ℤ) < 17119 * (n : ℤ) + 10800 := by linarith
  have hdm : d - 1 < m := by omega
  have hdn : d < n := by omega
  have h15 : 2 * n ≤ 15 * (m - (d - 1)) := by omega
  have hn1 : 1 ≤ n := by omega
  set H : ResidueGroup n → ℝ := fun y => (shHeadMeasure n d j y : ℝ)
  set T : ResidueGroup n → ℝ := fun x => (tailLaw n (d - 1) N x).toReal
  set δ : ℝ := fourierPrefactor ι * (n : ℝ) ^ (-(Aexp ι : ℝ))
  have hconv : ∀ x, (subMass n (mxShSlice n d j) x).toReal = ∑ y, H y * T (x - y) := by
    intro x
    rw [subMass_mxShSlice_eq_sum hd1 hdn j x, ENNReal.toReal_sum]
    · refine sum_congr rfl fun y _ => ?_
      rw [ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (by exact_mod_cast shHeadMeasure_nonneg n d j y)]
    · exact fun y _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (tailLaw_ne_top _ _ _ _)
  have hδ0 : 0 ≤ δ := mul_nonneg (fourierPrefactor_nonneg ι) (by positivity)
  have hosc := oscillation_sq_le_of_convolution hmn H T _ hconv δ
    (fun ξ hξ => by
      simpa [δ, fourierPrefactor_def] using norm_fxDft_tailLaw_le ι (l := N) hn1 hmn hdm h15 hξ)
  have hsqR : (3 : ℝ) ^ n * ∑ y, H y ^ 2 ≤
      ((shShellWidth j : ℝ) + 2) * ((2 : ℝ) ^ N)⁻¹ * #(shRetainedHeads n d j) := by
    have := pow_three_mul_sum_shHeadMeasure_sq_le hn1 d j
    have h' := (Rat.cast_le (K := ℝ)).2 this
    push_cast at h'
    simpa [H] using h'
  have hrhs : 0 ≤ δ * Real.sqrt (((shShellWidth j : ℝ) + 2) * ((2 : ℝ) ^ N)⁻¹ *
      #(shRetainedHeads n d j)) :=
    mul_nonneg hδ0 (Real.sqrt_nonneg _)
  have hsq : oscillation hmn (fun y => (subMass n (mxShSlice n d j) y).toReal) ^ 2 ≤
      (δ * Real.sqrt (((shShellWidth j : ℝ) + 2) * ((2 : ℝ) ^ N)⁻¹ *
        #(shRetainedHeads n d j))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc _ ≤ δ ^ 2 * 3 ^ n * ∑ y, H y ^ 2 := hosc
      _ = δ ^ 2 * ((3 : ℝ) ^ n * ∑ y, H y ^ 2) := by ring
      _ ≤ _ := by gcongr
  exact (pow_le_pow_iff_left₀ (oscillation_nonneg _ _) hrhs two_ne_zero).1 hsq

end CollatzPosDens
