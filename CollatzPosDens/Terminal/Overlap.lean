/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.RbLower
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.EndpointRatio
public import CollatzPosDens.Seed.EndpointUpperGrowth
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.HistoryPrefix
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.UpperScale

/-!
# Overlap of the scale windows of consecutive generations

Let `M ≥ 16^{b₀}` be an odd integer and `j ≥ 20 · 10^9`. For every central history
`h ∈ 𝓗_j(M)` and every `h' ∈ 𝓗_{j+1}(M)`, the lower scale of the next generation lies strictly
below the upper scale of the current one:
$$L_{b_{j+1}}(R_{h'}) < U_{b_j}(R_h).$$

Write `b = b_j`, `b' = b_{j+1}` and `σ_j = ∑_{i<j} (K_i + 3)`. Let `h''` be the prefix of `h'` of
generation `j`. Then `R_{h'} = src(w_j, R_{h''}) ≤ 2^{K_j+1} (4/3)^b R_{h''}` and
`R_{h''} ≤ 2^{σ_j} R_h`, so the claim reduces to `(4/3)^{b'} 2^{K_j+1+σ_j} < 2^{r_b + r_{b'}}`.
Since `(4/3)^{12} ≤ 2^5`, `100 b' ≤ 101 b + 99` and `r_b ≥ (229/1000) b - 4` for `b ≥ 256`,
this follows from `σ_j + K_j ≤ 20 (j+1)^2` and the fact that `b_j ≥ 9 (101/100)^j` is much
larger than `j^2` once `j ≥ 20 · 10^9`.

## Main results

* `CollatzPosDens.lowerScale_lt_upperScale_of_mem_centralHistories`: for `h ∈ 𝓗_j(M)` and
  `h' ∈ 𝓗_{j+1}(M)`, `L_{b_{j+1}}(R_{h'}) < U_{b_j}(R_h)`.
* `CollatzPosDens.ten_pow_ten_mul_sq_le_scale`: for `j ≥ 20 · 10^9`, `b_j ≥ 10^{10} (j+1)^2`.

## Implementation notes

The power `(101/100)^j` is bounded below as follows: with `m = ⌊j/4⌋`, Bernoulli's inequality
gives `(101/100)^j ≥ ((101/100)^m)^4 ≥ (1 + m/100)^4 ≥ (m/100)^4`. The comparison of
`(4/3)^{b'}` with a power of `2` is made after raising both sides to the twelfth power, so that
only integer exponents occur. The starting point `M` is an integer, cast to `ℚ` where the
histories are taken, and the endpoints are cast to `ℝ` where the scales are evaluated.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

/-- The cap sum `σ_j + K_j = ∑_{i<j} (K_i + 3) + K_j` is at most `20 (j+1)^2`. -/
private theorem overlap_capSum_add_cap_le (j : ℕ) :
    (∑ i ∈ Finset.range j, (cap i + 3)) + cap j ≤ 20 * (j + 1) ^ 2 := by
  have h1 : (∑ i ∈ Finset.range j, (cap i + 3)) + cap j ≤
      ∑ i ∈ Finset.range (j + 1), (cap i + 3) := by
    rw [Finset.sum_range_succ]
    omega
  have h2 : ∑ i ∈ Finset.range (j + 1), (cap i + 3) ≤
      ∑ _i ∈ Finset.range (j + 1), (cap j + 3) :=
    Finset.sum_le_sum fun i hi => by
      have := cap_mono (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
      omega
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
  calc _ ≤ _ := h1.trans h2
    _ ≤ (j + 1) * (20 * (j + 1)) := Nat.mul_le_mul_left _ (by unfold cap; omega)
    _ = _ := by ring

/-- For `j ≥ 20 · 10^9` the scale `b_j` dominates `10^{10} (j+1)^2`. -/
theorem ten_pow_ten_mul_sq_le_scale {j : ℕ}
    (hj : 20 * 10 ^ 9 ≤ j) : (10 : ℝ) ^ 10 * (j + 1) ^ 2 ≤ scale j := by
  set m := j / 4
  have hjm : (j : ℝ) ≤ 4 * m + 3 := by exact_mod_cast (show j ≤ 4 * m + 3 by omega)
  have hm5 : (5 * 10 ^ 9 : ℝ) ≤ m := by exact_mod_cast (show 5 * 10 ^ 9 ≤ m by omega)
  have hb := scale_add_ge_growthRatio_pow_mul 0 j
  rw [zero_add, scale_zero, growthRatio_cast] at hb
  have h1 : (101 / 100 : ℝ) ^ (4 * m) ≤ (101 / 100) ^ j :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_mul'] at h1
  have h2 : 1 + (m : ℝ) * (1 / 100) ≤ (1 + 1 / 100) ^ m := one_add_mul_le_pow (by norm_num) m
  have h2' : (m : ℝ) / 100 ≤ (101 / 100) ^ m := by
    norm_num at h2
    linarith
  have h3 : ((m : ℝ) / 100) ^ 4 ≤ ((101 / 100 : ℝ) ^ m) ^ 4 := by
    gcongr
  have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
  have h4 : (10 : ℝ) ^ 10 * (j + 1) ^ 2 ≤ 10 ^ 10 * 25 * m ^ 2 := by nlinarith
  have hmsq : (25 * 10 ^ 18 : ℝ) ≤ m ^ 2 := by nlinarith
  have h5 : (10 : ℝ) ^ 10 * 25 * m ^ 2 ≤ 9 * ((m : ℝ) / 100) ^ 4 := by
    rw [show 9 * ((m : ℝ) / 100) ^ 4 = 9 / 10 ^ 8 * m ^ 2 * m ^ 2 by ring]
    nlinarith
  nlinarith

/-- The exponent comparison: `(4/3)^{b_{j+1}} 2^{K_j + 1 + σ_j} < 2^{r_{b_j}} 2^{r_{b_{j+1}}}`. -/
private theorem overlap_key {j : ℕ} (hj : 20 * 10 ^ 9 ≤ j) :
    (4 / 3 : ℝ) ^ scale (j + 1) * 2 ^ (cap j + 1 + ∑ i ∈ Finset.range j, (cap i + 3)) <
      (2 : ℝ) ^ rb (scale j) * 2 ^ rb (scale (j + 1)) := by
  have hsq := ten_pow_ten_mul_sq_le_scale hj
  set b := scale j
  set b' := scale (j + 1)
  set N := cap j + 1 + ∑ i ∈ Finset.range j, (cap i + 3)
  have hjR : (20 * 10 ^ 9 : ℝ) ≤ j := by exact_mod_cast hj
  have hb256R : (256 : ℝ) ≤ b := by nlinarith
  have hb256 : 256 ≤ b := by exact_mod_cast hb256R
  have hbb' : 100 * b' ≤ 101 * b + 99 := by
    simp only [b, b', scale_succ, eb_of_le hb256]
    omega
  have hbb'' : b ≤ b' := scale_monotone (Nat.le_succ j)
  have hN : N ≤ 20 * (j + 1) ^ 2 + 1 := by
    have := overlap_capSum_add_cap_le j
    simp only [N]
    omega
  have hNR : (N : ℝ) ≤ 20 * (j + 1) ^ 2 + 1 := by exact_mod_cast hN
  have hbbR : (100 : ℝ) * b' ≤ 101 * b + 99 := by exact_mod_cast hbb'
  have hbbR' : (b : ℝ) ≤ b' := by exact_mod_cast hbb''
  have hr := rb_lower hb256
  have hr' := rb_lower (hb256.trans hbb'')
  have hexp : ((5 * b' + 12 * N : ℕ) : ℤ) < 12 * (rb b + rb b') := by
    have : ((5 * b' + 12 * N : ℕ) : ℝ) < ((12 * (rb b + rb b') : ℤ) : ℝ) := by
      push_cast
      nlinarith
    exact_mod_cast this
  have hX : (0 : ℝ) ≤ (4 / 3 : ℝ) ^ b' * 2 ^ N := by positivity
  have hY : (0 : ℝ) ≤ (2 : ℝ) ^ rb b * 2 ^ rb b' := by positivity
  refine (pow_lt_pow_iff_left₀ hX hY (by norm_num : (12 : ℕ) ≠ 0)).mp ?_
  have h43 : ((4 / 3 : ℝ) ^ 12) ≤ 2 ^ 5 := by norm_num
  calc ((4 / 3 : ℝ) ^ b' * 2 ^ N) ^ 12 = ((4 / 3 : ℝ) ^ 12) ^ b' * 2 ^ (12 * N) := by
        rw [mul_pow, ← pow_mul, ← pow_mul, pow_mul', mul_comm N 12]
    _ ≤ ((2 : ℝ) ^ 5) ^ b' * 2 ^ (12 * N) := by gcongr
    _ = (2 : ℝ) ^ ((5 * b' + 12 * N : ℕ) : ℤ) := by
        rw [zpow_natCast, ← pow_mul, ← pow_add]
    _ < (2 : ℝ) ^ (12 * (rb b + rb b')) := zpow_lt_zpow_right₀ (by norm_num) hexp
    _ = ((2 : ℝ) ^ rb b * 2 ^ rb b') ^ 12 := by
        rw [← zpow_add₀ two_ne_zero, ← zpow_natCast, ← zpow_mul, mul_comm]
        norm_num

/-- **Overlap of consecutive generations.** Let `M ≥ 16^{b₀}` be odd and `j ≥ 20 · 10^9`. For
every `h ∈ 𝓗_j(M)` and `h' ∈ 𝓗_{j+1}(M)`, `L_{b_{j+1}}(R_{h'}) < U_{b_j}(R_h)`. -/
@[collatz_pos_dens "lem_overlap"]
theorem lowerScale_lt_upperScale_of_mem_centralHistories {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) {j : ℕ} (hj : 20 * 10 ^ 9 ≤ j) {h : Fin j → Word}
    {h' : Fin (j + 1) → Word} (hh : h ∈ centralHistories M j)
    (hh' : h' ∈ centralHistories M (j + 1)) :
    lowerScale (scale (j + 1)) (historyEndpoint M h') <
      upperScale (scale j) (historyEndpoint M h) := by
  set h'' : Fin j → Word := fun i => h' (Fin.castLE (Nat.le_succ j) i)
  have hh'' : h'' ∈ centralHistories M j := centralHistories_prefix hh' (Nat.le_succ j)
  have hR' : historyEndpoint M h' = src (h' ⟨j, Nat.lt_succ_self j⟩) (historyEndpoint M h'') := by
    rw [historyEndpoint, historyEndpointAt_succ M h' (Nat.lt_succ_self j),
      historyEndpointAt_eq_src_concatWord M h' (Nat.le_succ j), historyEndpoint_eq_src]
  obtain ⟨m'', hm'', -, hm''ge⟩ := historyEndpointAt_large hodd hM hh'' le_rfl
  have hRpos : (0 : ℚ) < historyEndpoint M h := historyEndpointAt_large_endpoint_pos hodd hM hh
  have hR''nn : (0 : ℚ) ≤ historyEndpoint M h'' := by
    rw [historyEndpoint, hm'']
    exact_mod_cast le_trans (by positivity) hm''ge
  have hw : h' ⟨j, Nat.lt_succ_self j⟩ ∈ firstCrossing (scale j) (rb (scale j)) (cap j) :=
    centralFamily_subset_firstCrossing _ _
      (selectedTuples_mem_centralFamily hh'.1 ⟨j, Nat.lt_succ_self j⟩)
  have hup := src_le_of_mem_firstCrossing_rb hw hR''nn
  have hratio := historyEndpoint_le_two_pow_mul hodd hM hh hh''
  set σ := ∑ i ∈ Finset.range j, (cap i + 3)
  have hQ : historyEndpoint M h' ≤
      2 ^ (cap j + 1) * (4 / 3) ^ scale j * (2 ^ σ * historyEndpoint M h) := by
    rw [hR']
    exact hup.trans (mul_le_mul_of_nonneg_left hratio (by positivity))
  have hRR : (0 : ℝ) < (historyEndpoint M h : ℝ) := by exact_mod_cast hRpos
  have hQR : (historyEndpoint M h' : ℝ) ≤
      2 ^ (cap j + 1) * (4 / 3) ^ scale j * (2 ^ σ * (historyEndpoint M h : ℝ)) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hQ
  set R : ℝ := (historyEndpoint M h : ℝ)
  have hkey := overlap_key hj
  set b := scale j
  set b' := scale (j + 1)
  have hr' : (0 : ℝ) < 2 ^ rb b' := by positivity
  calc lowerScale b' (historyEndpoint M h')
      ≤ lowerScale b' (2 ^ (cap j + 1) * (4 / 3) ^ b * (2 ^ σ * R)) := lowerScale_mono b' hQR
    _ = ((4 / 3 : ℝ) ^ b' * 2 ^ (cap j + 1 + σ)) * ((4 / 3) ^ b * R / 4) / 2 ^ rb b' := by
        rw [lowerScale_def, div_pow, div_pow, pow_add (2 : ℝ) (cap j + 1) σ]
        field_simp
    _ < (2 ^ rb b * 2 ^ rb b') * ((4 / 3) ^ b * R / 4) / 2 ^ rb b' := by
        gcongr
    _ = upperScale b R := by
        rw [upperScale_eq, div_pow]
        field_simp

end CollatzPosDens
