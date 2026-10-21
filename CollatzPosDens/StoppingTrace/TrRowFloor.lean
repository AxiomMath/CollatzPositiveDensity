/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkExitWidth
public import CollatzPosDens.Renewal.RnRawOddSum
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Tactic.FieldSimp

/-!
# Rows of raw-prefix masses at large gaps

For integers `s ≥ 512` and `2 ≤ l ≤ s`, the first `f_s = ⌊(5s + 16)/16⌋` terms of the row
`r ↦ 𝖱(r - 1, l)` already carry mass at least `231/1024`:
`∑_{r=1}^{f_s} 𝖱(r - 1, l) ≥ 231/1024`.

The whole row `∑_{k ≥ 1} 𝖱(k, l)` equals `1/4`, and by the closed form
`𝖱(k, l) = binom(l - 1, 2k - 1) 2^{-l}` the omitted tail is at most half the mass of the
binomial law of row `n = l - 1` beyond index `2 f_s - 1`. That index exceeds the mean `n/2` by at
least `(s - 3)/8`, so Chebyshev's inequality, with the binomial variance
`∑_i binom(n, i) (2i - n)^2 = n 2^n`, bounds the tail by `25/(2s) ≤ 25/1024`.

## Main results

* `CollatzPosDens.sum_choose_mul_two_mul_sub_sq`: the binomial variance identity
  `∑_{i ≤ n} binom(n, i) (2i - n)^2 = n 2^n`.
* `CollatzPosDens.rawMass_row_floor`: `∑_{r=1}^{f_s} 𝖱(r - 1, l) ≥ 231/1024` for `s ≥ 512` and
  `2 ≤ l ≤ s`.

## Implementation notes

The variance identity is obtained by evaluating the Bernstein variance identity
`bernsteinPolynomial.variance` at `1/2`. The Chebyshev step is carried out directly on the
binomial coefficients: the tail indices `2k + 1 ≥ 2 f_s - 1` are injected into the row, where each
weight `(2i - n)^2` is at least `((s - 3)/4)^2`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset Polynomial

/-- The variance of the binomial law: `∑_{i ≤ n} binom(n, i) (2i - n)^2 = n 2^n`. -/
theorem sum_choose_mul_two_mul_sub_sq (n : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (2 * i - n) ^ 2 = (n * 2 ^ n : ℝ) := by
  have h := congrArg (Polynomial.eval (1 / 2 : ℝ)) (bernsteinPolynomial.variance ℝ n)
  simp only [eval_finsetSum, eval_mul, eval_pow, eval_sub, eval_X, eval_natCast,
    bernsteinPolynomial, eval_one, nsmul_eq_mul] at h
  have h2 : ∀ i ∈ range (n + 1), (n.choose i : ℝ) * (2 * i - n) ^ 2 = 4 * 2 ^ n *
      (((n : ℝ) * (1 / 2) - i) ^ 2 * ((n.choose i : ℝ) * (1 / 2) ^ i * (1 - 1 / 2) ^ (n - i))) := by
    intro i hi
    have hi' : i ≤ n := by simpa [Nat.lt_succ_iff] using hi
    rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, mul_assoc (n.choose i : ℝ), ← pow_add,
      Nat.add_sub_cancel' hi', one_div_pow]
    field_simp
    ring
  rw [sum_congr rfl h2, ← mul_sum, h]
  ring

/-- **Rows of raw-prefix masses at large gaps.** For `s ≥ 512` and `2 ≤ l ≤ s`,
`∑_{r=1}^{f_s} 𝖱(r - 1, l) ≥ 231/1024`, where `f_s = ⌊(5s + 16)/16⌋` is the exit width. -/
@[collatz_pos_dens "lem_tr_row_floor"]
theorem rawMass_row_floor {s : ℕ} (hs : 512 ≤ s) {l : ℤ} (hl : 2 ≤ l) (hls : l ≤ s) :
    (231 / 1024 : ℝ) ≤ ∑ r ∈ Icc 1 (bkExitWidth s), rawMass (r - 1) l := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, l = n + 1 := ⟨(l - 1).toNat, by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hns : n + 1 ≤ s := by omega
  have hf := five_mul_lt_sixteen_mul_bkExitWidth s
  obtain ⟨g, hg⟩ : ∃ g, bkExitWidth s = g + 1 := ⟨bkExitWidth s - 1, by omega⟩
  have hform : ∀ k : ℕ, rawMass (k + 1) ((n : ℤ) + 1) =
      (n.choose (2 * k + 1) : ℝ) * (2 : ℝ) ^ (-((n : ℤ) + 1)) := by
    intro k
    rw [rawMass_eq_choose (by omega), show ((n : ℤ) + 1 - 1).toNat = n by omega,
      show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  have hsum : ∑ r ∈ Icc 1 (bkExitWidth s), rawMass (r - 1) ((n : ℤ) + 1) =
      (∑ k ∈ range g, (n.choose (2 * k + 1) : ℝ)) * (2 : ℝ) ^ (-((n : ℤ) + 1)) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, hg,
      show g + 1 + 1 - 1 = g + 1 by omega, sum_range_succ', sum_mul]
    simp only [show ∀ k, 1 + (k + 1) - 1 = k + 1 from fun k ↦ by omega, hform,
      show 1 + 0 - 1 = 0 from rfl, rawMass_zero]
    have : ((n : ℤ) + 1) ≠ 0 := by omega
    simp [this]
  rw [hsum]
  set A : ℝ := 2 ^ (n - 1) with hA
  have hApos : 0 < A := by positivity
  have h2n : (2 : ℝ) ^ n = 2 * A := by
    rw [hA, ← pow_succ', Nat.sub_add_cancel hn1]
  have hpow : (2 : ℝ) ^ (-((n : ℤ) + 1)) = 1 / (4 * A) := by
    rw [zpow_neg, show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
      pow_succ, h2n]
    ring
  have htotal : ∑ k ∈ range (g + (n + 1)), (n.choose (2 * k + 1) : ℝ) = A := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [← Nat.cast_sum, sum_range_choose_succ_odd,
      ← sum_subset (range_mono (by omega : m + 1 ≤ 2 * (g + (m + 1 + 1))))
        (fun i _ hi ↦ Nat.choose_eq_zero_of_lt (by simpa using hi)), Nat.sum_range_choose, hA]
    simp
  rw [sum_range_add] at htotal
  set T := ∑ k ∈ range (n + 1), (n.choose (2 * (g + k) + 1) : ℝ) with hT
  have hT0 : 0 ≤ T := sum_nonneg fun _ _ ↦ by positivity
  set D : ℝ := 4 * g + 2 - n with hD
  have hD4 : (s : ℝ) - 3 ≤ 4 * D := by
    have : (5 * s + 1 : ℝ) ≤ 16 * (g + 1) := by exact_mod_cast (hg ▸ hf : 5 * s < 16 * (g + 1))
    have : (n : ℝ) + 1 ≤ s := by exact_mod_cast hns
    rw [hD]; linarith
  have hs' : (512 : ℝ) ≤ s := by exact_mod_cast hs
  have hDpos : 0 < D := by linarith
  have hcheb : T * D ^ 2 ≤ n * 2 ^ n := by
    rw [hT, sum_mul, ← sum_choose_mul_two_mul_sub_sq]
    calc ∑ k ∈ range (n + 1), (n.choose (2 * (g + k) + 1) : ℝ) * D ^ 2
        ≤ ∑ k ∈ range (n + 1), (n.choose (2 * (g + k) + 1) : ℝ) *
            (2 * ((2 * (g + k) + 1 : ℕ) : ℝ) - n) ^ 2 := by
          refine sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : D ≤ 2 * ((2 * (g + k) + 1 : ℕ) : ℝ) - n := by
            push_cast; rw [hD]; nlinarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]
          nlinarith
      _ = ∑ i ∈ (range (n + 1)).image (fun k ↦ 2 * (g + k) + 1),
            (n.choose i : ℝ) * (2 * (i : ℝ) - n) ^ 2 := by
          rw [sum_image fun a _ b _ h ↦ by omega]
      _ ≤ ∑ i ∈ range (2 * (g + n) + 2), (n.choose i : ℝ) * (2 * (i : ℝ) - n) ^ 2 := by
          refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ by positivity
          intro i hi
          simp only [mem_image, mem_range] at hi ⊢
          omega
      _ = ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (2 * (i : ℝ) - n) ^ 2 := by
          refine (sum_subset (range_mono (by omega)) fun i _ hi ↦ ?_).symm
          rw [Nat.choose_eq_zero_of_lt (by simpa using hi)]
          simp
  have hD2 : ((s : ℝ) - 3) ^ 2 ≤ 16 * D ^ 2 := by nlinarith
  have hn' : (n : ℝ) + 1 ≤ s := by exact_mod_cast hns
  have hTA : T * ((s : ℝ) - 3) ^ 2 ≤ 32 * n * A := by
    rw [h2n] at hcheb; nlinarith
  have hnum : 8192 * (n : ℝ) ≤ 25 * ((s : ℝ) - 3) ^ 2 := by nlinarith
  have hTle : T ≤ 25 * A / 256 := by
    have hpos : 0 < ((s : ℝ) - 3) ^ 2 := by nlinarith
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  rw [hpow, show (∑ k ∈ range g, (n.choose (2 * k + 1) : ℝ)) = A - T by linarith, mul_one_div,
    le_div_iff₀ (by linarith)]
  linarith

end CollatzPosDens
