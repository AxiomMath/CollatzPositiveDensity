/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.RbBounds
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.WeightUpper
public import CollatzPosDens.Maps.AffineIdentity
public import CollatzPosDens.Mixing.MxLog2Bounds
public import CollatzPosDens.Recipe.SeedShift
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.OrdinaryTime.CkCountSmall
public import CollatzPosDens.OrdinaryTime.CkScaleLast
public import CollatzPosDens.OrdinaryTime.CkSourceGuard
public import CollatzPosDens.OrdinaryTime.S07Bstar
public import CollatzPosDens.OrdinaryTime.S07LogFourThirds
public import CollatzPosDens.OrdinaryTime.S07SelectedPair
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.S05OffsetSmall
public import CollatzPosDens.Seed.S05Tuples
public import CollatzPosDens.Terminal.Sources

/-!
# A lower bound for the logarithm of a source

Let `t ≥ 1`, let `t₁` be a `t`-good seed and `n ≥ J_c = 23000`. Every source
`x ∈ 𝒮_{n,X}(t₁)` satisfies
$$\log (x/t) \ge \frac{28559}{100000} B_*(n).$$

The proof follows a selected pair `(h, w)` with source `x`, where
`h = (w_0, …, w_{n-1})` is a central history from `t₁` and `w ∈ 𝒲(b_n, u_h, 1)`. One block
of the inverse orbit along a word `v ∈ 𝒲(b, u, K)` from `R ≥ 2^{b+1}` multiplies `R` by at least
`2^{u - r_b - 2} (4/3)^b`, by the affine identity `R = ω(v) src(v, R) + off(v)`, the offset
bound `off(v) < 2^b` and the weight bound `ω(v) ≤ 2^{1 + r_b - u} (3/4)^b`. The endpoints
`R_j(h)` are odd integers with `R_j(h) ≥ 16^{b_j}` since `t₁ ≥ t_min`, so the block estimate
applies to each central word `w_j` (with `u = r_{b_j}`) and to the terminal word. Summing gives
`log x ≥ log t₁ + B_*(n) log(4/3) - r_{b_n} log 2 - 2(n + 1) log 2`. The losses are
absorbed using `r_{b_n} ≤ 3 b_n / 10`, `b_n ≤ 16544 + B_*(n)/100 + n`, `2^{22}(n+1) ≤ B_*(n)`,
`log t₁ - log t ≥ σ_sd log 2 ≥ (24816/5) log 2` (from `t₁ > 2^{σ_sd} t`, with `σ_sd = 66176`),
`log(4/3) > 0.287682` and `log 2 < 0.694`; finally `log(x/t) = log x - log t`.

## Main results

* `CollatzPosDens.le_log_of_mem_sources`: `(28559/100000) B_*(n) ≤ log (x/t)` for
  `x ∈ 𝒮_{n,X}(t₁)` and `n ≥ J_c`.

## Implementation notes

The paper assumes `3 ∤ t` and `X > 0`. Neither is used: the bound holds for every positive
integer `t` and every real `X`, since the terminal shift is a natural number in any case, so
both hypotheses are omitted. The seed `t₁` is a natural number, as in `CollatzPosDens.GoodSeed`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/
@[expose] public section

namespace CollatzPosDens

open Real

/-- One block of the inverse orbit: for `v ∈ 𝒲(b, u, K)` with `R ≥ 2^{b+1}`,
the source `src(v, R)` is positive and
`log src(v, R) ≥ log R + b log(4/3) - (r_b - u + 2) log 2`. -/
private theorem logSourceLower_block {b : ℕ} {u : ℤ} {K : ℕ} {w : Word}
    (hw : w ∈ firstCrossing b u K) {R : ℚ} (hR : 2 * 2 ^ b ≤ R) :
    0 < src w R ∧
      Real.log (R : ℝ) + b * Real.log (4 / 3) - (rb b - u + 2) * Real.log 2 ≤
        Real.log (src w R : ℝ) := by
  have hA := eq_weight_mul_src_add_off w R
  have hoff := off_lt_two_pow_of_mem_firstCrossing hw
  have hω := Word.weight_pos w
  have hωle := weight_le_of_mem_firstCrossing hw
  have h2b : (0 : ℚ) < 2 ^ b := by positivity
  have h1 : R / 2 < w.weight * src w R := by linarith
  have hs : 0 < src w R := by
    by_contra hneg
    push Not at hneg
    nlinarith
  refine ⟨hs, ?_⟩
  have h2 : R / 2 < (2 : ℚ) ^ (1 + rb b - u) * (3 / 4) ^ b * src w R :=
    lt_of_lt_of_le h1 (mul_le_mul_of_nonneg_right hωle.le hs.le)
  have h3 : (R : ℝ) / 2 < (2 : ℝ) ^ (1 + rb b - u) * (3 / 4) ^ b * (src w R : ℝ) := by
    simpa using (Rat.cast_lt (K := ℝ)).2 h2
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (by linarith : (0 : ℚ) < R)
  have hspos : (0 : ℝ) < src w R := by exact_mod_cast hs
  have h4 := Real.log_lt_log (by positivity) h3
  rw [Real.log_div hRpos.ne' two_ne_zero, Real.log_mul (by positivity) hspos.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_zpow, Real.log_pow,
    show (3 / 4 : ℝ) = (4 / 3)⁻¹ by norm_num, Real.log_inv] at h4
  push_cast at h4
  linarith

/-- An endpoint `R_j(h)` of a central history from an odd `t₁ ≥ t_min` satisfies
`R_j(h) ≥ 2 · 2^{b_j}`, the hypothesis of the block estimate. -/
private theorem logSourceLower_endpoint {t₁ : ℕ} (hodd : Odd t₁) (ht₁ : targetFloor ≤ t₁)
    {n : ℕ} {h : Fin n → Word} (hh : h ∈ centralHistories (t₁ : ℚ) n) {j : ℕ}
    (hj : j ≤ n) : 2 * 2 ^ scale j ≤ historyEndpointAt (t₁ : ℚ) h j := by
  have hh' : h ∈ centralHistories ((t₁ : ℤ) : ℚ) n := by rwa [Int.cast_natCast]
  obtain ⟨m, hm, -, hmge⟩ :=
    historyEndpointAt_large (by exact_mod_cast hodd) (by exact_mod_cast ht₁) hh' hj
  rw [Int.cast_natCast] at hm
  rw [hm]
  exact (two_mul_two_pow_le_sixteen_pow (le_trans (by norm_num) (sixteen544_le_scale j))).trans
    (by exact_mod_cast hmge)

/-- Generation-by-generation lower bound along a central history from an odd `t₁ ≥ t_min`:
`log R_j(h) ≥ log t₁ + (∑_{i < j} b_i) log(4/3) - 2 j log 2` for `j ≤ n`. -/
private theorem logSourceLower_history {t₁ : ℕ} (hodd : Odd t₁) (ht₁ : targetFloor ≤ t₁)
    {n : ℕ} {h : Fin n → Word} (hh : h ∈ centralHistories (t₁ : ℚ) n) {j : ℕ}
    (hj : j ≤ n) :
    Real.log t₁ + (∑ i ∈ Finset.range j, (scale i : ℝ)) * Real.log (4 / 3) -
        2 * (j : ℝ) * Real.log 2 ≤
      Real.log (historyEndpointAt (t₁ : ℚ) h j : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j < n := hj
    have hR := logSourceLower_endpoint hodd ht₁ hh hjn.le
    have hw : h ⟨j, hjn⟩ ∈ firstCrossing (scale j) (rb (scale j)) (cap j) :=
      centralFamily_subset_firstCrossing _ _ (selectedTuples_mem_centralFamily hh.1 ⟨j, hjn⟩)
    have hblk := (logSourceLower_block hw hR).2
    rw [← historyEndpointAt_succ (t₁ : ℚ) h hjn] at hblk
    have := ih hjn.le
    rw [Finset.sum_range_succ]
    push_cast
    simp only [sub_self, zero_add] at hblk
    linarith

/-- The losses in the two-stage estimate of `log x` are absorbed. -/
private theorem logSourceLower_absorb {n B bₙ r u S lM lR lx : ℝ}
    (hhist : lM + S * Real.log (4 / 3) - 2 * n * Real.log 2 ≤ lR)
    (hblk : lR + bₙ * Real.log (4 / 3) - (r - u + 2) * Real.log 2 ≤ lx)
    (hS : S + bₙ = B) (hu : 0 ≤ u) (hr : r ≤ 3 / 10 * bₙ) (hbn : bₙ ≤ 16544 + B / 100 + n)
    (hn : 0 ≤ n) (hN : 2 ^ 22 * (n + 1) ≤ B) (hlM : 24816 / 5 * Real.log 2 ≤ lM) :
    28559 / 100000 * B ≤ lx := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL7 : Real.log 2 < 0.694 := log_two_bounds.2
  have hF : (287682 / 10 ^ 6 : ℝ) < Real.log (4 / 3) := log_four_thirds_gt
  have hB : 0 ≤ B := le_trans (by positivity) hN
  have hSF : S * Real.log (4 / 3) + bₙ * Real.log (4 / 3) = B * Real.log (4 / 3) := by
    rw [← add_mul, hS]
  nlinarith [mul_le_mul_of_nonneg_right hr hL.le, mul_le_mul_of_nonneg_right hbn hL.le,
    mul_le_mul_of_nonneg_right hN hL.le, mul_le_mul_of_nonneg_left hF.le hB,
    mul_le_mul_of_nonneg_left hL7.le hB, mul_nonneg hu hL.le, mul_nonneg hn hL.le]

/-- **Lower bound for the logarithm of a source.** Let `t ≥ 1`, let `t₁` be a `t`-good seed,
`n ≥ J_c`, `X` real and `x ∈ 𝒮_{n,X}(t₁)`. Then `log(x/t) ≥ (28559/100000) B_*(n)`. -/
@[collatz_pos_dens "lem_log_source_lower"]
theorem le_log_of_mem_sources {t t₁ : ℕ} (ht : 0 < t) (ht₁ : GoodSeed t t₁) {n : ℕ}
    (hn : covGen ≤ n) (X : ℝ) {x : ℤ} (hx : x ∈ sources n X (t₁ : ℚ)) :
    (28559 / 100000 : ℝ) * scaleSum n ≤ Real.log ((x : ℝ) / t) := by
  obtain ⟨⟨h, w⟩, hp, hsrc⟩ := mem_sources.1 hx
  have hp' : IsSelectedPair n X (t₁ : ℚ) h w := hp
  -- `t₁ > 2^{σ_sd} t ≥ 2^{σ_sd} = t_min`
  have hσ : (2 : ℕ) ^ seedShift = targetFloor := by
    rw [seedShift_def, targetFloor_def, pow_mul, show (2 : ℕ) ^ 4 = 16 from rfl]
  have ht₁floor : targetFloor ≤ t₁ := by
    rw [← hσ]
    exact (Nat.le_mul_of_pos_right _ ht).trans ht₁.lower.le
  have hR := logSourceLower_endpoint ht₁.odd ht₁floor hp'.mem_centralHistories le_rfl
  rw [historyEndpointAt_of_le _ _ le_rfl] at hR
  obtain ⟨hxpos, hblk⟩ := logSourceLower_block hp'.mem_firstCrossing hR
  simp only at hsrc
  rw [hsrc] at hxpos
  rw [hsrc, Rat.cast_intCast, historyEndpoint] at hblk
  have hxpos' : (0 : ℝ) < x := by exact_mod_cast hxpos
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  rw [Real.log_div hxpos'.ne' htpos.ne']
  have hlM : 24816 / 5 * Real.log 2 ≤ Real.log t₁ - Real.log t := by
    have h2 : (2 : ℝ) ^ seedShift * t ≤ t₁ := by exact_mod_cast ht₁.lower.le
    have := Real.log_le_log (by positivity) h2
    rw [Real.log_mul (by positivity) htpos.ne', Real.log_pow, seedShift_eq] at this
    have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
    push_cast at this
    linarith
  have hhist := logSourceLower_history ht₁.odd ht₁floor hp'.mem_centralHistories le_rfl
  set lR := Real.log (historyEndpointAt (t₁ : ℚ) h n : ℝ)
  set S := ∑ i ∈ Finset.range n, (scale i : ℝ)
  set u : ℝ := (historyShift n X (t₁ : ℚ) h : ℝ)
  have hhist' : (Real.log t₁ - Real.log t) + S * Real.log (4 / 3) -
      2 * (n : ℝ) * Real.log 2 ≤ lR - Real.log t := by linarith
  have hblk' : (lR - Real.log t) + scale n * Real.log (4 / 3) -
      (rb (scale n) - u + 2) * Real.log 2 ≤ Real.log x - Real.log t := by
    push_cast at hblk
    linarith
  refine logSourceLower_absorb hhist' hblk' ?_ (by positivity)
    (by linarith [(rb_bounds ((by norm_num : 256 ≤ 16544).trans (sixteen544_le_scale n))).2,
      (Nat.cast_nonneg _ : (0 : ℝ) ≤ scale n)])
    (scale_le_scaleSum_div_hundred n) (Nat.cast_nonneg n)
    (by exact_mod_cast two_pow_twentyTwo_mul_succ_le_scaleSum n hn) hlM
  rw [scaleSum, Finset.sum_range_succ]
  push_cast
  rfl

end CollatzPosDens
