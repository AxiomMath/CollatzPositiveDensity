/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.B
public import CollatzPosDens.Transfer.Dsc
public import CollatzPosDens.Transfer.H
public import CollatzPosDens.Transfer.K
public import CollatzPosDens.Transfer.Qpack
public import CollatzPosDens.Transfer.S
public import CollatzPosDens.Transfer.Beta
public import CollatzPosDens.Transfer.PBits
public import CollatzPosDens.Transfer.SLower
public import CollatzPosDens.Transfer.BlockGap
public import CollatzPosDens.Transfer.BlockSumX
public import CollatzPosDens.Transfer.BlockSumOne
public import CollatzPosDens.Transfer.FarB
public import CollatzPosDens.Transfer.FarS
public import CollatzPosDens.StoppingTrace.TrEstar
public import CollatzPosDens.Case3.C3Big
public import CollatzPosDens.Case3.C3ExcSum
public import CollatzPosDens.Case3.C3BigMass
public import CollatzPosDens.Case3.C3Margin
public import CollatzPosDens.Case3.C3ScaleRoom

/-!
# Mass of the large-triangle event `E^{*,e}`

Let `J = ⌊n/2⌋`, let `ξ` be a unit, `e = (j₀, l₀) ∈ Δ₀ ∈ 𝔗 = 𝔗_{n,ξ,ε_*}` and `G ∈ ℕ` with
`l₀ + G = l_{Δ₀}`. Let `m` be a real number with `m ≥ D_sc`, `P_* ≤ J` and `m / (log m)^2 < G`.
Then
$$\mu_{e,G}(\mathrm E^{*,e}) < \frac{2 + 272 (H_* + 1) Q_{\mathrm{pack}}}{K_*} + \frac1{3360}.$$

The offsets `u ∈ {0, …, P_* - 1}` are grouped into dyadic blocks `2^k ≤ u + 1 < 2^{k+1}`,
`0 ≤ k ≤ k̄` where `2^{k̄} ≤ P_* < 2^{k̄+1}`. On the `k`-th block put
`v_k = min(P_* - 1, 2^{k+1} - 2)`, `X_k = 136 (v_k + 1)` and `s_k = β_*(2^k - 1)`. Then
`E^{*,e} ⊆ ⋃_k Big_{e,G,v_k,s_k}`, and the mass of each `Big_{e,G,v_k,s_k}` is at most
`Q_pack X_k / s_k + 1 / s_k + Exc(v_k)` by `CollatzPosDens.tsum_trFreshLaw_c3Big_le`, whose
hypotheses follow from the far-scale bounds `S_* < m/(log m)^2` and `B_*^2 < 2 m/(log m)^2`, the
block gap and the triangle margin. The two block sums are partial sums of convergent series
bounded by `272 (H_* + 1)/K_*` and `2/K_*`, and the offsets `v_k`, `k ≥ 1`, are pairwise distinct
and at least `2`, so the exceptional allowances sum to less than `1/3360`.

## Main results

* `CollatzPosDens.trEStar_subset_iUnion_c3Big`: the dyadic block cover of `E^{*,e}`.
* `CollatzPosDens.tsum_trFreshLaw_trEStar_lt`: the mass bound for `E^{*,e}` displayed above.

## Implementation notes

As in `CollatzPosDens.tsum_trFreshLaw_c3Big_le`, the mass `μ_{e,G}(E)` of an event `E` is the
`ℝ≥0∞`-valued sum `∑' a : E, ENNReal.ofReal (μ_{e,G}(a))`, which needs no summability side
condition; the bound is stated for its image under `ENNReal.ofReal`. The standing assumptions of
the section (`ξ` a unit, `ε = ε_*`) are explicit hypotheses, and `P_* ≤ J` is `pStar ≤ n / 2`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.3.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- The dyadic block cover of the large-triangle event: if `P_* < 2^{k̄+1}`, then
`E^{*,e} ⊆ ⋃_{k ≤ k̄} Big_{e,G,v_k,s_k}` with `v_k = min(P_* - 1, 2^{k+1} - 2)` and
`s_k = β_*(2^k - 1)`. -/
theorem trEStar_subset_iUnion_c3Big (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) (G : ℕ)
    {kb : ℕ} (hkb : pStar < 2 ^ (kb + 1)) :
    trEStar n ξ e ⊆ ⋃ k ∈ Finset.range (kb + 1),
      c3Big n ξ epsStar e G (min (pStar - 1) (2 ^ (k + 1) - 2)) (betaStar (2 ^ k - 1)) := by
  rintro a ⟨ha, q, hq, Δ, hΔ, hmem, hs⟩
  set k := Nat.log 2 (q + 1)
  have h1 : 2 ^ k ≤ q + 1 := Nat.pow_log_le_self 2 (by omega)
  have h2 : q + 1 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hk : k < kb + 1 := by
    by_contra h
    have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (not_lt.1 h)
    omega
  refine Set.mem_biUnion (Finset.mem_range.2 hk) ?_
  refine mem_c3Big_of_mem ha (u := q) (by omega) hΔ hmem (le_trans ?_ hs)
  exact_mod_cast betaStar_monotone (by omega)

/-- The exceptional allowances of the dyadic blocks sum to less than `1/3360`. -/
theorem sum_c3Exc_block_lt {P kb : ℕ} (hkb : 2 ^ kb ≤ P) :
    ∑ k ∈ Finset.range (kb + 1), c3Exc (min (P - 1) (2 ^ (k + 1) - 2)) < 1 / 3360 := by
  have hvlt {i j : ℕ} (hij : i < j) (hj : j < kb) :
      min (P - 1) (2 ^ (i + 1 + 1) - 2) < min (P - 1) (2 ^ (j + 1 + 1) - 2) := by
    have h₁ : 2 ^ (i + 1 + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h₂ : 2 ^ (j + 1) ≤ 2 ^ kb := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h₃ : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
    have h₄ := Nat.one_le_two_pow (n := j + 1)
    omega
  have hinj : Set.InjOn (fun i ↦ min (P - 1) (2 ^ (i + 1 + 1) - 2)) (Finset.range kb : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (hvlt h hj).ne
    · exact h
    · exact absurd hij.symm (hvlt h hi).ne
  rw [Finset.sum_range_succ', show min (P - 1) (2 ^ (0 + 1) - 2) = 0 by simp,
    ← Finset.sum_image (f := c3Exc) hinj, add_comm]
  refine c3Exc_zero_add_sum_lt _ fun x hx ↦ ?_
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
  have h₁ : 2 ^ (i + 1) ≤ 2 ^ kb := Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.1 hi)
  have h₂ : 2 ^ (i + 1 + 1) = 2 * 2 ^ (i + 1) := by ring
  have h₃ := Nat.one_le_two_pow (n := i + 1)
  omega

/-- The mass of the `k`-th dyadic block: if `2^k ≤ P_*`, then `Big_{e,G,v_k,s_k}` has mass at
most `Q_pack X_k / s_k + 1 / s_k + Exc(v_k)`, under the hypotheses of
`CollatzPosDens.tsum_trFreshLaw_trEStar_lt`. -/
theorem tsum_trFreshLaw_c3Big_block_le {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ} (he : e ∈ Δ₀) {G : ℕ}
    (hG : bkL e + G = Δ₀.l) {m : ℝ} (hm : (Dsc : ℝ) ≤ m) (hP : pStar ≤ n / 2)
    (hmG : m / Real.log m ^ 2 < G) {k : ℕ} (hk : 2 ^ k ≤ pStar) :
    ∑' a : c3Big n ξ epsStar e G (min (pStar - 1) (2 ^ (k + 1) - 2)) (betaStar (2 ^ k - 1)),
        ENNReal.ofReal (trFreshLaw n e G a) ≤
      ENNReal.ofReal (Qpack * (136 * (((min (pStar - 1) (2 ^ (k + 1) - 2) : ℕ) : ℝ) + 1) /
        betaStar (2 ^ k - 1)) + 1 / (betaStar (2 ^ k - 1) : ℝ) +
        c3Exc (min (pStar - 1) (2 ^ (k + 1) - 2))) := by
  have hSG : (sStar : ℝ) < G := (sStar_lt_div_log_sq hm).trans hmG
  have hBG : (Bstar : ℝ) ^ 2 < 2 * G := by linarith [sq_Bstar_div_two_lt_div_log_sq hm]
  have hG160 : 2 ^ 160 ≤ G := by
    have h365 : 2 ^ 160 < sStar :=
      lt_trans (Nat.pow_lt_pow_right (by norm_num) (by norm_num)) two_pow_365_lt_sStar
    have : ((2 ^ 160 : ℕ) : ℝ) < G := lt_trans (by exact_mod_cast h365) hSG
    exact_mod_cast this.le
  have hSG' : 2 ^ 36 * (pStar : ℝ) ≤ G := by
    rw [← sStar_cast]
    exact hSG.le
  have hP1 : 1 ≤ pStar := Nat.one_le_two_pow.trans two_pow_le_pStar
  have hvP : min (pStar - 1) (2 ^ (k + 1) - 2) + 1 ≤ pStar := by omega
  have hs : 4096 * (136 * (((min (pStar - 1) (2 ^ (k + 1) - 2) : ℕ) : ℝ) + 1)) ≤
      betaStar (2 ^ k - 1) := by
    have hgap := betaStar_block_gap k (pStar - 1)
    generalize min (pStar - 1) (2 ^ (k + 1) - 2) = v at hgap ⊢
    have : ((4096 * 136 * (v + 1) : ℕ) : ℝ) < betaStar (2 ^ k - 1) := by exact_mod_cast hgap
    push_cast at this
    linarith
  have hBdef : betaStar (pStar - 1) = Bstar := by
    rw [Bstar_def, pStar_def, Nat.add_sub_cancel]
  have hsB : (betaStar (2 ^ k - 1) : ℝ) ≤ Bstar := by
    rw [← hBdef]
    exact_mod_cast betaStar_monotone (by omega)
  exact tsum_trFreshLaw_c3Big_le hξ hΔ₀ he hG hG160 (by omega) hs
    ((pow_le_pow_left₀ (Nat.cast_nonneg _) hsB 2).trans_lt hBG)
    (by linarith [two_mul_rpow_add_alpha_mul_add_one_le_mul_drift hvP hSG'])

/-- The block masses sum to less than `(2 + 272 (H_* + 1) Q_pack) / K_* + 1/3360`. -/
theorem sum_block_mass_lt {P kb : ℕ} (hkb : 2 ^ kb ≤ P) :
    ∑ k ∈ Finset.range (kb + 1), (Qpack * (136 * (((min (P - 1) (2 ^ (k + 1) - 2) : ℕ) : ℝ) + 1) /
        betaStar (2 ^ k - 1)) + 1 / (betaStar (2 ^ k - 1) : ℝ) +
        c3Exc (min (P - 1) (2 ^ (k + 1) - 2))) <
      (2 + 272 * ((Hstar : ℝ) + 1) * Qpack) / Kstar + 1 / 3360 := by
  obtain ⟨v, hv⟩ : ∃ v : ℕ → ℕ, v = fun k ↦ min (P - 1) (2 ^ (k + 1) - 2) := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : ℕ → ℝ, s = fun k ↦ (betaStar (2 ^ k - 1) : ℝ) := ⟨_, rfl⟩
  have hvk (k : ℕ) : v k = min (P - 1) (2 ^ (k + 1) - 2) := by rw [hv]
  have hsk (k : ℕ) : s k = (betaStar (2 ^ k - 1) : ℝ) := by rw [hsdef]
  simp only [← hvk, ← hsk]
  obtain ⟨hXs, hXlt⟩ := betaStar_two_pow_sub_one_summable_window (P - 1)
  have hXeq (k : ℕ) : ((136 * (min (P - 1) (2 ^ (k + 1) - 2) + 1) : ℕ) : ℝ) /
      betaStar (2 ^ k - 1) = 136 * ((v k : ℝ) + 1) / s k := by
    rw [hvk, hsk]
    push_cast
    rfl
  have hA : ∑ k ∈ Finset.range (kb + 1), 136 * ((v k : ℝ) + 1) / s k <
      272 * (Hstar + 1) / Kstar := by
    refine lt_of_le_of_lt ?_ hXlt
    simp_rw [← hXeq]
    exact hXs.sum_le_tsum _ fun k _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  obtain ⟨hOs, hOle⟩ := betaStar_two_pow_sub_one_summable_inv
  have hO : ∑ k ∈ Finset.range (kb + 1), 1 / s k ≤ 2 / Kstar := by
    refine le_trans ?_ hOle
    simp_rw [hsk]
    exact hOs.sum_le_tsum _ fun k _ ↦ div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hC : ∑ k ∈ Finset.range (kb + 1), c3Exc (v k) < 1 / 3360 := by
    simpa only [hvk] using sum_c3Exc_block_lt hkb
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    show (2 + 272 * ((Hstar : ℝ) + 1) * Qpack) / Kstar =
      Qpack * (272 * (Hstar + 1) / Kstar) + 2 / Kstar by field_simp; ring]
  linarith [mul_lt_mul_of_pos_left hA (show (0 : ℝ) < Qpack by exact_mod_cast Qpack_pos)]

/-- The `ℝ≥0∞`-valued form of `CollatzPosDens.sum_block_mass_lt`. -/
theorem sum_ofReal_block_mass_lt {P kb : ℕ} (hkb : 2 ^ kb ≤ P) :
    ∑ k ∈ Finset.range (kb + 1),
        ENNReal.ofReal (Qpack * (136 * (((min (P - 1) (2 ^ (k + 1) - 2) : ℕ) : ℝ) + 1) /
          betaStar (2 ^ k - 1)) + 1 / (betaStar (2 ^ k - 1) : ℝ) +
          c3Exc (min (P - 1) (2 ^ (k + 1) - 2))) <
      ENNReal.ofReal ((2 + 272 * ((Hstar : ℝ) + 1) * Qpack) / Kstar + 1 / 3360) := by
  have h₀ (k : ℕ) : 0 ≤ Qpack * (136 * (((min (P - 1) (2 ^ (k + 1) - 2) : ℕ) : ℝ) + 1) /
      betaStar (2 ^ k - 1)) + 1 / (betaStar (2 ^ k - 1) : ℝ) +
      c3Exc (min (P - 1) (2 ^ (k + 1) - 2)) :=
    add_nonneg (add_nonneg (mul_nonneg (by exact_mod_cast Qpack_pos.le)
      (div_nonneg (by positivity) (Nat.cast_nonneg _)))
      (div_nonneg zero_le_one (Nat.cast_nonneg _))) (c3Exc_pos _).le
  have hsum := sum_block_mass_lt hkb
  rw [← ENNReal.ofReal_sum_of_nonneg fun k _ ↦ h₀ k,
    ENNReal.ofReal_lt_ofReal_iff ((Finset.sum_nonneg fun k _ ↦ h₀ k).trans_lt hsum)]
  exact hsum

/-- **Mass of the large-triangle event.** Let `ξ` be a unit, `e ∈ Δ₀ ∈ 𝔗_{n,ξ,ε_*}`, `G ∈ ℕ`
with `l(e) + G = l_{Δ₀}`, and `m` a real number with `m ≥ D_sc`, `P_* ≤ ⌊n/2⌋` and
`m / (log m)^2 < G`. Then
`μ_{e,G}(E^{*,e}) < (2 + 272 (H_* + 1) Q_pack) / K_* + 1/3360`. -/
@[collatz_pos_dens "lem_c3_estar_mass"]
theorem tsum_trFreshLaw_trEStar_lt {n : ℕ} {ξ : ResidueGroup n} (hξ : IsResidueUnit ξ)
    {Δ₀ : BkTriangle} (hΔ₀ : Δ₀ ∈ bkFamily n ξ epsStar) {e : ℤ × ℤ} (he : e ∈ Δ₀) {G : ℕ}
    (hG : bkL e + G = Δ₀.l) {m : ℝ} (hm : (Dsc : ℝ) ≤ m) (hP : pStar ≤ n / 2)
    (hmG : m / Real.log m ^ 2 < G) :
    ∑' a : trEStar n ξ e, ENNReal.ofReal (trFreshLaw n e G a) <
      ENNReal.ofReal ((2 + 272 * ((Hstar : ℝ) + 1) * Qpack) / Kstar + 1 / 3360) := by
  obtain ⟨kb, hkb1, hkb2⟩ : ∃ kb, 2 ^ kb ≤ pStar ∧ pStar < 2 ^ (kb + 1) :=
    ⟨Nat.log 2 pStar,
      Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.1 (Nat.one_le_two_pow.trans two_pow_le_pStar)),
      Nat.lt_pow_succ_log_self (by norm_num) _⟩
  calc ∑' a : trEStar n ξ e, ENNReal.ofReal (trFreshLaw n e G a)
      ≤ ∑' a : ↥(⋃ k ∈ Finset.range (kb + 1),
          c3Big n ξ epsStar e G (min (pStar - 1) (2 ^ (k + 1) - 2)) (betaStar (2 ^ k - 1))),
          ENNReal.ofReal (trFreshLaw n e G a) :=
        ENNReal.tsum_mono_subtype (fun a ↦ ENNReal.ofReal (trFreshLaw n e G a))
          (trEStar_subset_iUnion_c3Big n ξ e G hkb2)
    _ ≤ ∑ k ∈ Finset.range (kb + 1), ∑' a : c3Big n ξ epsStar e G
          (min (pStar - 1) (2 ^ (k + 1) - 2)) (betaStar (2 ^ k - 1)),
          ENNReal.ofReal (trFreshLaw n e G a) :=
        ENNReal.tsum_biUnion_le (fun a ↦ ENNReal.ofReal (trFreshLaw n e G a)) _ _
    _ ≤ _ := Finset.sum_le_sum fun k hk ↦ tsum_trFreshLaw_c3Big_block_le hξ hΔ₀ he hG hm hP hmG
          ((Nat.pow_le_pow_right two_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))).trans hkb1)
    _ < _ := sum_ofReal_block_mass_lt hkb1

end CollatzPosDens
