/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FcStartupProductCertA
public import CollatzPosDens.FirstCrossing.FcStartupProductCertB
public import CollatzPosDens.FirstCrossing.FcStartupProductCertC
public import CollatzPosDens.FirstCrossing.FcStartupProductCertD
public import CollatzPosDens.FirstCrossing.FcStartupProductCertE
public import CollatzPosDens.FirstCrossing.FcStartupProductCertF
public import CollatzPosDens.FirstCrossing.FcStartupProductCertG
public import CollatzPosDens.FirstCrossing.FcStartupProductCertH
public import CollatzPosDens.FirstCrossing.FcStartupProductCertI
public import CollatzPosDens.FirstCrossing.FcStartupProductCertJ

/-!
# Startup product of central masses

Let `b_j` be the scales and `K_j = 16 + ⌊j/32⌋` the overshoot caps. The first `444` central
families have geometric masses whose product exceeds `(72/5) 2^{-25}`:
$$\prod_{j=0}^{443}\mathbf{p}(\mathcal{C}(b_j,K_j)) > \tfrac{72}{5}\,2^{-25}.$$

This is a finite numerical certificate. Each factor is bounded below by `N_j 2^{-64}` for an
explicit natural number `N_j`, and the exact integer inequality
`72 · 2^{28391} < 5 ∏_j N_j` is checked by kernel evaluation.

* For `j ≤ 41` we have `9 ≤ b_j ≤ 233 < 256`, so `𝒞(b_j, K_j)` is the first-crossing family
  `𝒲(b_j, r_{b_j}, K_j)` (cut by the minimal early overshoot `μ_b` when `b ∈ {9, 10, 11}`).
  Its mass is given exactly by the dynamic-programming formula
  `∑_d (∑_s c_{b,d-1}(s)) (2^{K+1-μ(d)} - 1) / 2^{H(d)+K}`, the surviving counts
  `c_{b,i}(s)` being computed from their initial values and their prefix-sum recursion; `N_j`
  is the truncation of `2^64` times this mass.
* For `42 ≤ j ≤ 443` we have `b_j ≥ 256`, and `N_j` comes from the binomial lower bound
  `1 - 2·2^{-n₊}∑_{t<h₊}C(n₊,t) - 2^{-n₋}∑_{t≤h₋-v₋}C(n₋,t) - 2^{-(K+1)}`, each tail being
  rounded up to a multiple of `2^{-64}`.

## Main results

* `CollatzPosDens.geomMass_centralFamily_startup_prod_gt`: the startup product exceeds
  `(72/5) 2^{-25}`.

## Implementation notes

The non-computable ingredients are replaced by computable mirrors proved equal to them:
`B(j) = ⌈j log₂ 3⌉` is `⌊log₂ 3^j⌋ + 1` for `j ≥ 1`, the centred barrier
`H_{b,r_b}(s) = 2b + B((s-b)₊) - B((b-s)₊)` is free of the shift `r_b`, and the width
`wd(b) = min(⌈√(32 b lg b)⌉, ⌊3b/5⌋ - 1)` uses the integer ceiling square root. For
`b ∈ {9, 10, 11}`, `μ_b(d)` is bounded above by the least `k < 16` passing an integer form of
its defining inequality; a smaller lower-bound family is used if no such `k` exists, so no
case analysis on the values of `μ_b` is needed.

The proof departs from [mazur2026] in the large-scale factors only in how the binomial tails
are bounded: they are summed exactly for `j < 140`, while for `140 ≤ j ≤ 443` the lower tail
`∑_{t≤k}C(n,t)` is bounded by the Chernoff estimate `(p+q)^n / (p^k q^{n-k})` at
`p = k`, `q = n - k`. This loses a factor of about `0.995` in the product, which stays above
`14.63 · 2^{-25}`. Each factor is truncated to `64` binary digits, and the kernel checks the
product in nineteen blocks of consecutive factors; the six factors `36 ≤ j ≤ 41`, whose
dynamic programmes are the largest, form blocks of their own.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

open fcStartupProduct

private theorem prodGo_certificate :
    72 * 2 ^ 28391 < prodGo 444 0 (scale 0) * 5 := by
  have c368 := prodGo_block_368
  have c292 := prodGo_mul_le prodGo_block_292 c368
  have c216 := prodGo_mul_le prodGo_block_216 c292
  have c140 := prodGo_mul_le prodGo_block_140 c216
  have c91 := prodGo_mul_le prodGo_block_91 c140
  have c42 := prodGo_mul_le prodGo_block_42 c91
  have c41 := prodGo_mul_le prodGo_block_41 c42
  have c40 := prodGo_mul_le prodGo_block_40 c41
  have c39 := prodGo_mul_le prodGo_block_39 c40
  have c38 := prodGo_mul_le prodGo_block_38 c39
  have c37 := prodGo_mul_le prodGo_block_37 c38
  have c36 := prodGo_mul_le prodGo_block_36 c37
  have c33 := prodGo_mul_le prodGo_block_33 c36
  have c30 := prodGo_mul_le prodGo_block_30 c33
  have c24 := prodGo_mul_le prodGo_block_24 c30
  have c18 := prodGo_mul_le prodGo_block_18 c24
  have c12 := prodGo_mul_le prodGo_block_12 c18
  have c6 := prodGo_mul_le prodGo_block_6 c12
  have c0 := prodGo_mul_le prodGo_block_0 c6
  refine lt_of_lt_of_le ?_ (Nat.mul_le_mul_right 5 c0)
  decide +kernel

/-- The product of the geometric masses of the first `444` central families exceeds
`(72/5) 2^{-25}`: `∏_{j=0}^{443} 𝐩(𝒞(b_j, K_j)) > (72/5) 2^{-25}`. -/
@[collatz_pos_dens "lem_fc_startup_product"]
theorem geomMass_centralFamily_startup_prod_gt :
    (72 / 5 : ℝ≥0∞) * 2⁻¹ ^ 25 <
      ∏ j ∈ Finset.range 444, geomMass (centralFamily (scale j) (cap j)) := by
  have hcert := prodGo_certificate
  rw [prodGo_eq] at hcert
  simp only [zero_add] at hcert
  set P := ∏ i ∈ Finset.range 444, startupNum i (scale i)
  have hlow : (P : ℝ≥0∞) * 2⁻¹ ^ 28416 ≤
      ∏ j ∈ Finset.range 444, geomMass (centralFamily (scale j) (cap j)) := by
    calc (P : ℝ≥0∞) * 2⁻¹ ^ 28416
        = ∏ j ∈ Finset.range 444, ((startupNum j (scale j) : ℝ≥0∞) * 2⁻¹ ^ 64) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
            Nat.cast_prod]
      _ ≤ _ := Finset.prod_le_prod fun j hj => startupNum_le (Finset.mem_range.1 hj)
  refine lt_of_lt_of_le ?_ hlow
  have hu0 : (2⁻¹ : ℝ≥0∞) ^ 28416 ≠ 0 := pow_ne_zero _ (by simp)
  have hut : (2⁻¹ : ℝ≥0∞) ^ 28416 ≠ ⊤ := ENNReal.pow_ne_top (by simp)
  have h25 : (2⁻¹ : ℝ≥0∞) ^ 25 = 2 ^ 28391 * 2⁻¹ ^ 28416 := by
    rw [show 28416 = 28391 + 25 by norm_num, pow_add, ← mul_assoc, two_pow_mul_inv_pow, one_mul]
  rw [h25, ← mul_assoc, ENNReal.mul_lt_mul_iff_left hu0 hut, mul_comm, ← mul_div_assoc,
    ENNReal.div_lt_iff (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  have h := (Nat.cast_lt (α := ℝ≥0∞)).2 hcert
  rwa [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat, Nat.cast_ofNat,
    mul_comm (72 : ℝ≥0∞)] at h

end CollatzPosDens
