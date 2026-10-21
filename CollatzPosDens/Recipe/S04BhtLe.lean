/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Texp
public import CollatzPosDens.Recipe.Bht
public import CollatzPosDens.Recipe.Erec
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.Recipe.CovExp
public import CollatzPosDens.FirstCrossing.ScalesUpper
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Upper bound for the height exponent

The height exponent `B_ht = 𝓔(J_c) + ⌊2 b_{J_c}/3⌋`, with `J_c = 23000` the coverage
generation, lies below the coverage exponent: `B_ht < Λ_cov = 2^352`.

Since `gr(u) < 5u/12 + 1` and `K_j + 1 = 30 + ⌊j/56⌋ ≤ 30 + j/56`, unfolding the exponent
recurrence gives `𝓔(J) ≤ 31 J + J^2/112 + (5/12) ∑_{j<J} b_j`. The upper growth of the scales,
`b_j < 16644 𝗀^j` with `𝗀 = 101/100`, turns the sum into a geometric one:
`∑_{j<J} b_j ≤ 1664400 (𝗀^J - 1)`, and `⌊2 b_J/3⌋ < 11096 𝗀^J`, so
`B_ht < 31 J + J^2/112 + 704596 𝗀^J < 2^30 + 2^20 𝗀^J` at `J = J_c`. Since `𝗀^348 < 2^5`,
`𝗀^32 < 2` and `J_c = 348 · 66 + 32`, one has `𝗀^{J_c} < 2^331`, whence
`B_ht < 2^30 + 2^351 ≤ 2^352`.

## Main results

* `CollatzPosDens.mul_erec_le_sum_scale`: `1344 𝓔(j) ≤ 41664 j + 12 j^2 + 560 ∑_{i<j} b_i`.
* `CollatzPosDens.sum_range_scale_le`: `∑_{i<J} b_i ≤ 1664400 (𝗀^J - 1)`.
* `CollatzPosDens.heightExponentOf_lt_growthRatio_pow`:
  `𝓔(J) + ⌊2 b_J/3⌋ < 31 J + J^2/112 + 704596 𝗀^J`.
* `CollatzPosDens.growthRatio_pow_covGen_lt`: `𝗀^{J_c} < 2^331`.
* `CollatzPosDens.heightExponent_lt_covExp`: `B_ht < Λ_cov`.

## Implementation notes

The bound `𝗀^{32} < 2` is checked directly by an exact rational comparison, where the original
argument passes through `𝗀^{32} ≤ 𝗀^{69} = 2^{69δ} < 2`. The comparison `𝗀^348 < 2^5` is the
exact integer comparison `101^348 < 2^5 · 100^348 = 32 · 100^348`, evaluated with the
exponentiation threshold raised to `348` for the declaration that states it. The powers
`2^331` and `2^352` are treated as opaque numbers in the final linear arithmetic.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset Real

/-- Unfolding the exponent recurrence: `1344 𝓔(j) ≤ 41664 j + 12 j^2 + 560 ∑_{i<j} b_i`, i.e.
`𝓔(j) ≤ 31 j + j^2/112 + (5/12) ∑_{i<j} b_i`. -/
theorem mul_erec_le_sum_scale (j : ℕ) :
    1344 * erec j ≤ 41664 * j + 12 * (j * j) + 560 * ∑ i ∈ range j, scale i := by
  induction j with
  | zero => simp [erec_zero]
  | succ j ih =>
    rw [erec_succ, sum_range_succ]
    have hc : cap j = 29 + j / 56 := rfl
    have ht : 12 * texp (scale j) ≤ 5 * scale j + 11 := by
      rw [texp_eq_ceil]; exact Nat.mul_div_le _ _
    have hd : 56 * (j / 56) ≤ j := Nat.mul_div_le _ _
    rw [hc]
    nlinarith

/-- The geometric sum of the scales: `∑_{i<J} b_i ≤ 1664400 (𝗀^J - 1)`. -/
theorem sum_range_scale_le (J : ℕ) :
    (∑ i ∈ range J, (scale i : ℝ)) ≤ 1664400 * ((growthRatio : ℝ) ^ J - 1) := by
  calc (∑ i ∈ range J, (scale i : ℝ)) ≤ ∑ i ∈ range J, 16644 * (growthRatio : ℝ) ^ i :=
        sum_le_sum fun i _ => (scale_lt_mul_growthRatio_pow i).le
    _ = 16644 * (((growthRatio : ℝ) ^ J - 1) / ((growthRatio : ℝ) - 1)) := by
        rw [← mul_sum, geom_sum_eq (by rw [growthRatio_cast]; norm_num)]
    _ = 1664400 * ((growthRatio : ℝ) ^ J - 1) := by
        rw [growthRatio_cast]; field_simp; ring

/-- For every `J`, `𝓔(J) + ⌊2 b_J/3⌋ < 31 J + J^2/112 + 704596 𝗀^J`. -/
theorem heightExponentOf_lt_growthRatio_pow (J : ℕ) :
    (heightExponentOf J : ℝ) < 31 * J + (J : ℝ) ^ 2 / 112 + 704596 * (growthRatio : ℝ) ^ J := by
  rw [heightExponentOf_def]
  have he : (1344 * erec J : ℝ) ≤
      41664 * J + 12 * (J * J) + 560 * ∑ i ∈ range J, (scale i : ℝ) := by
    exact_mod_cast mul_erec_le_sum_scale J
  have hsum := sum_range_scale_le J
  have hb := scale_lt_mul_growthRatio_pow J
  have hd : ((2 * scale J / 3 : ℕ) : ℝ) * 3 ≤ 2 * scale J := by
    have : 2 * scale J / 3 * 3 ≤ 2 * scale J := Nat.div_mul_le_self _ _
    exact_mod_cast this
  have hg : 0 < (growthRatio : ℝ) ^ J := pow_pos (by rw [growthRatio_cast]; norm_num) J
  push_cast
  nlinarith

set_option exponentiation.threshold 348 in
/-- The exact integer comparison `101^348 < 2^5 · 100^348`, with `2^5 = 32`. -/
private theorem s04_pow_348_lt : 101 ^ 348 < 32 * 100 ^ 348 :=
  Nat.le_of_ble_eq_true rfl

/-- `𝗀^348 < 2^5`. -/
private theorem s04_growthRatio_pow_348_lt : (growthRatio : ℝ) ^ 348 < 2 ^ 5 := by
  have h := (Nat.cast_lt (α := ℝ)).mpr s04_pow_348_lt
  have h100 : (0 : ℝ) < (100 : ℝ) ^ 348 := by positivity
  have h32 : (2 : ℝ) ^ 5 = 32 := by norm_num
  rw [growthRatio_cast, div_pow, div_lt_iff₀ h100, h32]
  simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

/-- `𝗀^32 < 2`. -/
private theorem s04_growthRatio_pow_32_lt : (growthRatio : ℝ) ^ 32 < 2 := by
  rw [growthRatio_cast]; norm_num

/-- The geometric term at the coverage generation: `𝗀^{J_c} < 2^331`. -/
theorem growthRatio_pow_covGen_lt : (growthRatio : ℝ) ^ covGen < 2 ^ 331 := by
  have h0 : (0 : ℝ) ≤ (growthRatio : ℝ) := by rw [growthRatio_cast]; norm_num
  have e : (growthRatio : ℝ) ^ covGen =
      ((growthRatio : ℝ) ^ 348) ^ 66 * (growthRatio : ℝ) ^ 32 := by
    rw [covGen_def, ← pow_mul, ← pow_add]
  have h66 : ((growthRatio : ℝ) ^ 348) ^ 66 < (2 ^ 5) ^ 66 :=
    pow_lt_pow_left₀ s04_growthRatio_pow_348_lt (pow_nonneg h0 _) (by norm_num)
  have h2 : (2 : ℝ) ^ 331 = (2 ^ 5) ^ 66 * 2 := by rw [← pow_mul, ← pow_succ]
  rw [e, h2]
  exact mul_lt_mul'' h66 s04_growthRatio_pow_32_lt (pow_nonneg (pow_nonneg h0 _) _)
    (pow_nonneg h0 _)

/-- The height exponent lies below the coverage exponent: `B_ht < Λ_cov`. -/
@[collatz_pos_dens "lem_s04_Bht_le"]
theorem heightExponent_lt_covExp : heightExponent < covExp := by
  have hB := heightExponentOf_lt_growthRatio_pow covGen
  rw [← heightExponent_eq_heightExponentOf] at hB
  have hgJ := growthRatio_pow_covGen_lt
  have hQ : ((covExp : ℕ) : ℝ) = 2 * (2 : ℝ) ^ 351 := by
    rw [covExp_def, Nat.cast_pow, Nat.cast_ofNat, ← pow_succ']
  have hP : (2 : ℝ) ^ 351 = 2 ^ 20 * 2 ^ 331 := by rw [← pow_add]
  have hP10 : (2 : ℝ) ^ 10 ≤ 2 ^ 331 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hJ : 31 * (covGen : ℝ) + (covGen : ℝ) ^ 2 / 112 < 2 ^ 30 := by
    rw [covGen_def]; norm_num
  have hlt : (heightExponent : ℝ) < covExp := by
    rw [hQ, hP]
    generalize (2 : ℝ) ^ 331 = P at hgJ hP10 ⊢
    generalize (growthRatio : ℝ) ^ covGen = G at hB hgJ
    generalize 31 * (covGen : ℝ) + (covGen : ℝ) ^ 2 / 112 = A at hB hJ
    norm_num at hP10 hJ ⊢
    nlinarith
  exact_mod_cast hlt

end CollatzPosDens
