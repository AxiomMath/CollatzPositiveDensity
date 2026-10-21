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
public import CollatzPosDens.FirstCrossing.FcCapSumProp
public import CollatzPosDens.FirstCrossing.RbLower
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.OrdinaryTime.CkScaleDoubling
public import CollatzPosDens.Recipe.CovGen
public import CollatzPosDens.Recipe.NstarRange
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.EndpointRatio
public import CollatzPosDens.Seed.EndpointUpperGrowth
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.S05HistoryPrefix
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.UpperScale

/-!
# Overlap of the scale windows of consecutive generations

Let `t ≥ t_min` be an odd integer and `j ≥ J_c = 23000`. For every central history
`h ∈ 𝓗_j(t)` and every `h' ∈ 𝓗_{j+1}(t)`, the lower scale of the next generation lies strictly
below the upper scale of the current one:
$$L_{b_{j+1}}(R_{h'}) < U_{b_j}(R_h).$$

Write `b = b_j`, `b' = b_{j+1}` and `σ_j = ∑_{i<j} (K_i + 3)`. With `k = ⌊j/70⌋ ≥ 328`,
`b ≥ 16544 · 2^k ≥ 148896 k^2` (as `2^k ≥ 9 k^2` for `k ≥ 57`) and `j < 71 k`, so
`j^2 < (37/1000) b`. Let `h''` be the prefix of `h'` of generation `j`. Then
`R_{h'} = src(w_j, R_{h''}) ≤ 2^{K_j+1} (4/3)^b R_{h''}` and `R_{h''} ≤ 2^{σ_j} R_h`, so the
claim reduces to `(4/3)^{b'} 2^{K_j+1+σ_j} < 2^{r_b + r_{b'}}`. Since `(4/3)^{12} ≤ 2^5`,
`100 b' ≤ 101 b + 99` and `r_b ≥ (229/1000) b - 4` for `b ≥ 256`, this follows from
`K_j + σ_j + 10 < j^2`, which holds as `K_j = 29 + ⌊j/56⌋ ≤ 29 + j/56` and `1 + σ_j < j^2/82`
for `j ≥ J_c ≥ N_*`: then `K_j + σ_j + 10 < 38 + j/56 + j^2/82 ≤ 39 j + j^2/82 ≤ j^2`, the last
step because `39 · 82 ≤ 81 · 40` and `j ≥ 40`.

## Main results

* `CollatzPosDens.lowerScale_lt_upperScale_of_mem_centralHistories`: the overlap
  `L_{b_{j+1}}(R_{h'}) < U_{b_j}(R_h)`.
* `CollatzPosDens.thousand_mul_sq_lt_thirtySeven_mul_scale`: for `j ≥ J_c`,
  `1000 j^2 < 37 b_j`.

## Implementation notes

The comparison of `(4/3)^{b'}` with a power of `2` is made after raising both sides to the
twelfth power, so that only integer exponents occur; the lower bound for `r_{b'}` is used at
`b'` itself rather than through `b' ≥ b`. The starting point `t` is an integer, cast to `ℚ`
where the histories are taken, and the endpoints are cast to `ℝ` where the scales are
evaluated.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `9 k^2 ≤ 2^k` for `k ≥ 57` (the binomial bound `2^k ≥ binom(k, 3) ≥ 9 k^2`). -/
private theorem overlap_nine_mul_sq_le_two_pow {k : ℕ} (hk : 57 ≤ k) : 9 * k ^ 2 ≤ 2 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ 2 k]
    nlinarith

/-- For `j ≥ J_c = 23000`, the scale dominates the square of the generation:
`j^2 < (37/1000) b_j`, written `1000 j^2 < 37 b_j`. -/
theorem thousand_mul_sq_lt_thirtySeven_mul_scale {j : ℕ} (hj : covGen ≤ j) :
    1000 * j ^ 2 < 37 * scale j := by
  rw [covGen_def] at hj
  set k := j / 70 with hkdef
  have hk : 328 ≤ k := by omega
  have hjk : j < 71 * k := by omega
  have h2k := overlap_nine_mul_sq_le_two_pow (k := k) (by omega)
  have hb := sixteen544_mul_two_pow_div_seventy_le_scale j
  rw [← hkdef] at hb
  calc 1000 * j ^ 2 < 1000 * (71 * k) ^ 2 := by
        have := Nat.pow_lt_pow_left hjk (two_ne_zero)
        omega
    _ ≤ 37 * (16544 * (9 * k ^ 2)) := by ring_nf; omega
    _ ≤ 37 * (16544 * 2 ^ k) := by gcongr
    _ ≤ 37 * scale j := by gcongr

/-- `K_j + σ_j + 10 < j^2` for `j ≥ J_c`, where `σ_j = ∑_{i<j} (K_i + 3)`. -/
private theorem overlap_cap_add_sum_lt_sq {j : ℕ} (hj : covGen ≤ j) :
    cap j + (∑ i ∈ Finset.range j, (cap i + 3)) + 10 < j ^ 2 := by
  have hr := one_add_sum_cap_add_three_lt_sq_div_82
    (selEnd_le_generationThreshold_range.2.trans hj)
  have hnat : 82 * (1 + ∑ i ∈ Finset.range j, (cap i + 3)) < j ^ 2 := by
    have h' : (82 : ℝ) * (1 + ∑ i ∈ Finset.range j, ((cap i : ℝ) + 3)) < (j : ℝ) ^ 2 := by
      linarith
    exact_mod_cast h'
  rw [covGen_def] at hj
  have hcap : cap j = 29 + j / 56 := rfl
  have hj56 : j / 56 ≤ j := Nat.div_le_self _ _
  have hsq : 23000 * j ≤ j ^ 2 := by rw [sq]; exact Nat.mul_le_mul_right _ hj
  omega

/-- The exponent comparison: `(4/3)^{b_{j+1}} 2^{K_j + 1 + σ_j} < 2^{r_{b_j}} 2^{r_{b_{j+1}}}`
for `j ≥ J_c`. -/
private theorem overlap_key {j : ℕ} (hj : covGen ≤ j) :
    (4 / 3 : ℝ) ^ scale (j + 1) * 2 ^ (cap j + 1 + ∑ i ∈ Finset.range j, (cap i + 3)) <
      (2 : ℝ) ^ rb (scale j) * 2 ^ rb (scale (j + 1)) := by
  have hsq := thousand_mul_sq_lt_thirtySeven_mul_scale hj
  have hN := overlap_cap_add_sum_lt_sq hj
  have hbb' : 100 * scale (j + 1) ≤ 101 * scale j + 99 := by
    rw [scale_succ, eb_eq]
    omega
  set b := scale j
  set b' := scale (j + 1)
  set N := cap j + 1 + ∑ i ∈ Finset.range j, (cap i + 3)
  have hb256 : 256 ≤ b := le_trans (by norm_num) (sixteen544_le_scale j)
  have hbb'' : b ≤ b' := by rw [show b' = b + eb b from scale_succ j]; omega
  have hN' : N + 9 < j ^ 2 := by simp only [N]; omega
  have hNR : ((N : ℕ) : ℝ) + 9 < (j : ℝ) ^ 2 := by exact_mod_cast hN'
  have hsqR : (1000 : ℝ) * (j : ℝ) ^ 2 < 37 * b := by exact_mod_cast hsq
  have hbbR : (100 : ℝ) * b' ≤ 101 * b + 99 := by exact_mod_cast hbb'
  have hr := rb_lower hb256
  have hr' := rb_lower (hb256.trans hbb'')
  have hexp : ((5 * b' + 12 * N : ℕ) : ℤ) < 12 * (rb b + rb b') := by
    have : ((5 * b' + 12 * N : ℕ) : ℝ) < ((12 * (rb b + rb b') : ℤ) : ℝ) := by
      push_cast
      linarith
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

/-- **Overlap of consecutive generations.** Let `t ≥ t_min` (`targetFloor`) be an odd integer and
`j ≥ J_c` (`covGen`). For every `h ∈ 𝓗_j(t)` and `h' ∈ 𝓗_{j+1}(t)`,
`L_{b_{j+1}}(R_{h'}) < U_{b_j}(R_h)`. -/
@[collatz_pos_dens "lem_overlap"]
theorem lowerScale_lt_upperScale_of_mem_centralHistories {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) {j : ℕ} (hj : covGen ≤ j) {h : Fin j → Word}
    {h' : Fin (j + 1) → Word} (hh : h ∈ centralHistories t j)
    (hh' : h' ∈ centralHistories t (j + 1)) :
    lowerScale (scale (j + 1)) (historyEndpoint t h') <
      upperScale (scale j) (historyEndpoint t h) := by
  set h'' : Fin j → Word := fun k => h' (Fin.castLE (Nat.le_succ j) k)
  have hh'' : h'' ∈ centralHistories t j := centralHistories_prefix hh' (Nat.le_succ j)
  have hR' : historyEndpoint t h' =
      src (h' ⟨j, Nat.lt_succ_self j⟩) (historyEndpoint t h'') := by
    rw [historyEndpoint, historyEndpointAt_succ t h' (Nat.lt_succ_self j),
      historyEndpointAt_eq_src_concatWord t h' (Nat.le_succ j), historyEndpoint_eq_src]
  obtain ⟨m'', hm'', -, hm''ge⟩ := historyEndpointAt_large hodd ht hh'' le_rfl
  have hRpos : (0 : ℚ) < historyEndpoint t h :=
    historyEndpointAt_large_endpoint_pos hodd (targetFloor_le_iff.1 ht) hh
  have hR''nn : (0 : ℚ) ≤ historyEndpoint t h'' := by
    rw [historyEndpoint, hm'']
    exact_mod_cast le_trans (by positivity) hm''ge
  have hw₀ := selectedTuples_mem_centralFamily hh'.1 ⟨j, Nat.lt_succ_self j⟩
  have hw : h' ⟨j, Nat.lt_succ_self j⟩ ∈ firstCrossing (scale j) (rb (scale j)) (cap j) :=
    centralFamily_subset_firstCrossing _ _ hw₀
  have hup := src_le_of_mem_firstCrossing_rb hw hR''nn
  have hratio := historyEndpoint_le_two_pow_mul hodd ht hh hh''
  set σ := ∑ i ∈ Finset.range j, (cap i + 3)
  have hQ : historyEndpoint t h' ≤
      2 ^ (cap j + 1) * (4 / 3) ^ scale j * (2 ^ σ * historyEndpoint t h) := by
    rw [hR']
    exact hup.trans (mul_le_mul_of_nonneg_left hratio (by positivity))
  have hRR : (0 : ℝ) < (historyEndpoint t h : ℝ) := by exact_mod_cast hRpos
  have hQR : (historyEndpoint t h' : ℝ) ≤
      2 ^ (cap j + 1) * (4 / 3) ^ scale j * (2 ^ σ * (historyEndpoint t h : ℝ)) := by
    simpa using (Rat.cast_le (K := ℝ)).mpr hQ
  set R : ℝ := (historyEndpoint t h : ℝ)
  have hkey := overlap_key hj
  set b := scale j
  set b' := scale (j + 1)
  have hr' : (0 : ℝ) < 2 ^ rb b' := by positivity
  calc lowerScale b' (historyEndpoint t h')
      ≤ lowerScale b' (2 ^ (cap j + 1) * (4 / 3) ^ b * (2 ^ σ * R)) := lowerScale_mono b' hQR
    _ = ((4 / 3 : ℝ) ^ b' * 2 ^ (cap j + 1 + σ)) * ((4 / 3) ^ b * R / 4) / 2 ^ rb b' := by
        rw [lowerScale_def, div_pow, div_pow, pow_add (2 : ℝ) (cap j + 1) σ]
        field_simp
    _ < (2 ^ rb b * 2 ^ rb b') * ((4 / 3) ^ b * R / 4) / 2 ^ rb b' :=
        div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hkey
          (div_pos (mul_pos (pow_pos (by norm_num) _) hRR) (by norm_num))) hr'
    _ = upperScale b R := by
        rw [upperScale_eq, div_pow]
        field_simp

end CollatzPosDens
