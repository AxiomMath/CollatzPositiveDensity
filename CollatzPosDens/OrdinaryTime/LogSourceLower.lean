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
public import CollatzPosDens.OrdinaryTime.CkCountSmall
public import CollatzPosDens.OrdinaryTime.CkLateGrowth
public import CollatzPosDens.OrdinaryTime.CkScaleLast
public import CollatzPosDens.OrdinaryTime.CkSourceGuard
public import CollatzPosDens.OrdinaryTime.Bstar
public import CollatzPosDens.OrdinaryTime.LogFourThirds
public import CollatzPosDens.OrdinaryTime.SelectedPair
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.GoodSeed
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.OffsetSmall
public import CollatzPosDens.Seed.Tuples
public import CollatzPosDens.Terminal.Sources

/-!
# A lower bound for the logarithm of a source

Let `M` be a good seed and `n ≥ 2 · 10^{10}`. Every source `x ∈ 𝒮_{n,X}(M)` satisfies
$$\log x \ge \frac{28559}{100000} B_*(n).$$

The proof follows a selected pair `(h, w)` with source `x`. One block of the inverse orbit
along a word `v ∈ 𝒲(b, u, K)` from `R ≥ 2^{b+1}` multiplies `R` by at least
`2^{u - r_b - 2} (4/3)^b`, by the affine identity `R = ω(v) src(v, R) + off(v)`, the offset
bound `off(v) < 2^b` and the weight bound `ω(v) ≤ 2^{1 + r_b - u} (3/4)^b`. Summing the
logarithmic form of this over the central words of `h` and the terminal word `w` gives
`log x ≥ log M + B_*(n) log(4/3) - r_{b_n} log 2 - 2(n+1) log 2`. The losses are absorbed
using `r_{b_n} ≤ 3 b_n / 10`, `b_n ≤ 9 + B_*(n)/100 + 2n`, `2^{22}(n+1) ≤ B_*(n)`,
`log M ≥ 4 b_0 log 2`, `log(4/3) > 0.287682` and `log 2 < 0.694`.

## Main results

* `CollatzPosDens.le_log_of_mem_sources`: `(28559/100000) B_*(n) ≤ log x` for
  `x ∈ 𝒮_{n,X}(M)` and `n ≥ 2 · 10^{10}`.

## Implementation notes

The hypothesis `X > 0` is not needed: the bound holds for every real `X`, since the terminal
shift is a natural number in any case.

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
  have h2b : (0 : ℚ) < 2 ^ b := by positivity
  have h1 : R / 2 < w.weight * src w R := by
    linarith [eq_weight_mul_src_add_off w R, off_lt_two_pow_of_mem_firstCrossing hw]
  have hs : 0 < src w R := by
    by_contra hneg
    push Not at hneg
    nlinarith [Word.weight_pos w]
  refine ⟨hs, ?_⟩
  have h2 : R / 2 < (2 : ℚ) ^ (1 + rb b - u) * (3 / 4) ^ b * src w R :=
    h1.trans_le (mul_le_mul_of_nonneg_right (weight_le_of_mem_firstCrossing hw) hs.le)
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

/-- Generation-by-generation lower bound along a central history from an odd `M ≥ 16^{b_0}`:
`log R_j(h) ≥ log M + (∑_{i<j} b_i) log(4/3) - 2 j log 2` for `j ≤ n`. -/
private theorem logSourceLower_history {M : ℕ} (hodd : Odd M) (hM : 16 ^ scale 0 ≤ M)
    {n : ℕ} {h : Fin n → Word} (hh : h ∈ centralHistories (M : ℚ) n) {j : ℕ}
    (hj : j ≤ n) :
    Real.log M + (∑ i ∈ Finset.range j, (scale i : ℝ)) * Real.log (4 / 3) -
        2 * j * Real.log 2 ≤ Real.log (historyEndpointAt (M : ℚ) h j : ℝ) := by
  have hoddZ : Odd (M : ℤ) := by exact_mod_cast hodd
  have hMZ : (16 : ℤ) ^ scale 0 ≤ (M : ℤ) := by exact_mod_cast hM
  have hh' : h ∈ centralHistories ((M : ℤ) : ℚ) n := by rwa [Int.cast_natCast]
  induction j with
  | zero => simp
  | succ j ih =>
    have hjn : j < n := hj
    obtain ⟨m, hm, -, hmge⟩ := historyEndpointAt_large hoddZ hMZ hh' hjn.le
    rw [Int.cast_natCast] at hm
    have hR : 2 * 2 ^ scale j ≤ historyEndpointAt (M : ℚ) h j := by
      rw [hm]
      exact (two_mul_two_pow_le_sixteen_pow (le_trans (by norm_num) (nine_le_scale j))).trans
        (by exact_mod_cast hmge)
    have hw : h ⟨j, hjn⟩ ∈ firstCrossing (scale j) (rb (scale j)) (cap j) :=
      centralFamily_subset_firstCrossing _ _ (mem_selectedTuples.1 hh.1 |>.1 ⟨j, hjn⟩)
    have hblk := (logSourceLower_block hw hR).2
    rw [← historyEndpointAt_succ (M : ℚ) h hjn] at hblk
    rw [Finset.sum_range_succ]
    push_cast
    simp only [sub_self, zero_add] at hblk
    linarith [ih hjn.le]

/-- The losses in the two-stage estimate of `log x` are absorbed. -/
private theorem logSourceLower_absorb {n B b₀ bₙ r u S lM lR lx : ℝ}
    (hhist : lM + S * Real.log (4 / 3) - 2 * n * Real.log 2 ≤ lR)
    (hblk : lR + bₙ * Real.log (4 / 3) - (r - u + 2) * Real.log 2 ≤ lx)
    (hS : S + bₙ = B) (hu : 0 ≤ u) (hr : r ≤ 3 / 10 * bₙ) (hbn : bₙ ≤ 9 + B / 100 + 2 * n)
    (hn : 0 ≤ n) (hN : 2 ^ 22 * (n + 1) ≤ B) (hb₀ : 9 ≤ b₀) (hlM : 4 * b₀ * Real.log 2 ≤ lM) :
    28559 / 100000 * B ≤ lx := by
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL7 : Real.log 2 < 0.694 := log_two_bounds.2
  have hF : (287682 / 10 ^ 6 : ℝ) < Real.log (4 / 3) := log_four_thirds_gt
  have hB : 0 ≤ B := by linarith
  nlinarith [mul_le_mul_of_nonneg_right hr hL.le, mul_le_mul_of_nonneg_right hbn hL.le,
    mul_le_mul_of_nonneg_right hN hL.le, mul_le_mul_of_nonneg_left hF.le hB,
    mul_le_mul_of_nonneg_left hL7.le hB, mul_le_mul_of_nonneg_right hb₀ hL.le,
    mul_nonneg hu hL.le]

/-- **Lower bound for the logarithm of a source.** Let `M` be a good seed, `n ≥ 2 · 10^{10}`,
`X` real and `x ∈ 𝒮_{n,X}(M)`. Then `log x ≥ (28559/100000) B_*(n)`. -/
@[collatz_pos_dens "lem_log_source_lower"]
theorem le_log_of_mem_sources {M : ℕ} (hM : GoodSeed M) {n : ℕ} (hn : 2 * 10 ^ 10 ≤ n)
    (X : ℝ) {x : ℤ} (hx : x ∈ sources n X (M : ℚ)) :
    (28559 / 100000 : ℝ) * scaleSum n ≤ Real.log x := by
  obtain ⟨⟨h, w⟩, hp, hsrc⟩ := mem_sources.1 hx
  have hp' : IsSelectedPair n X (M : ℚ) h w := hp
  have hM16 : 16 ^ scale 0 ≤ M := hM.lower.le
  have hh' : h ∈ centralHistories ((M : ℤ) : ℚ) n := by
    rw [Int.cast_natCast]
    exact hp'.mem_centralHistories
  obtain ⟨m, hm, -, hmge⟩ :=
    historyEndpointAt_large (by exact_mod_cast hM.odd) (by exact_mod_cast hM16) hh' le_rfl
  rw [Int.cast_natCast, historyEndpointAt_of_le _ _ le_rfl] at hm
  have hR : 2 * 2 ^ scale n ≤ historyEndpoint (M : ℚ) h := by
    rw [hm]
    exact (two_mul_two_pow_le_sixteen_pow (le_trans (by norm_num) (nine_le_scale n))).trans
      (by exact_mod_cast hmge)
  have hblk := (logSourceLower_block hp'.mem_firstCrossing hR).2
  simp only at hsrc
  rw [hsrc, historyEndpoint, Rat.cast_intCast] at hblk
  push_cast at hblk
  have hlM : 4 * (scale 0 : ℝ) * Real.log 2 ≤ Real.log M := by
    have := Real.log_le_log (by positivity) (show (16 : ℝ) ^ scale 0 ≤ M by exact_mod_cast hM16)
    rw [Real.log_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at this
    push_cast at this
    linarith
  have hhist := logSourceLower_history hM.odd hM16 hp'.mem_centralHistories le_rfl
  refine logSourceLower_absorb (n := (n : ℝ)) hhist hblk ?_ (by positivity)
    (rb_bounds (nine_le_scale n)).2 (scale_le_scaleSum_div_hundred (by omega))
    (Nat.cast_nonneg n) (by exact_mod_cast two_pow_twentyTwo_mul_succ_le_scaleSum n hn)
    (by exact_mod_cast nine_le_scale 0) hlM
  rw [scaleSum_def, Finset.sum_range_succ]
  push_cast
  rfl

end CollatzPosDens
