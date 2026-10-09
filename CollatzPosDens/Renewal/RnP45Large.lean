/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.Renewal.RnRawMassFormula
public import CollatzPosDens.Renewal.RnRawOddSum

/-!
# A lower bound for the closing exit mass at large gaps

For every integer `s ≥ 256`, the closing exit mass `p₄₅ = CollatzPosDens.p45` satisfies
`p₄₅(s) ≥ 5/16 - 125/(8s)`. Here `ϖ = CollatzPosDens.varpi` is the Pascal holding-time law and
`𝖱 = CollatzPosDens.rawMass` the raw-prefix mass.

Write `f = ⌊(5s+16)/16⌋`, so `16f ≥ 5s + 1`. For each of the eight pairs `(c, O)` with
`c ∈ {4, 5}`, `O ∈ {1, …, 4}`, put `t = s + O - c ∈ [s - 4, s]` and `n = t - 1`. Dropping the
`r = 1` term and using `∑_{k ≥ 1} 𝖱(k, t) = 1/4`,
`∑_{r=1}^{f} 𝖱(r - 1, t) ≥ 1/4 - ∑_{k ≥ f} 𝖱(k, t)`, and by the closed form
`𝖱(k, t) = binom(n, 2k - 1) 2^{-t}` the tail is at most `2^{-t} ∑_{i ≥ 2f - 1} binom(n, i)`.
For `i ≥ 2f - 1` one has `2i - n ≥ s/5`, so Chebyshev's inequality with the variance identity
`∑_i binom(n, i) (2i - n)² = n 2^n` bounds the tail by `25 n / (2 s²) ≤ 25/(2s)`. Summing over the
pairs with `ϖ(4) + ϖ(5) = 5/16` gives the claim.

## Main results

* `CollatzPosDens.p45_ge_of_le`: for `s ≥ 256`, `5/16 - 125/(8s) ≤ p₄₅(s)`.

## Implementation notes

The variance identity is written as `∑_{i ≤ n} binom(n, i) (2i - n)² = n 2^n` (four times the
centred form `∑ binom(n, i) 2^{-n} (i - n/2)² = n/4`), and proved by induction on `n` through
Pascal's rule rather than through the first two factorial moments. The tail `∑_{k ≥ f} 𝖱(k, t)`
is a `tsum`, bounded through its partial sums; each partial sum of odd-index coefficients
`∑_{i < N} binom(n, 2i + m)` is bounded by the full block `∑_{j < 2N} binom(n, m + j)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Pascal's rule summed against a weight:
`∑_{i ≤ n+1} binom(n+1, i) g(i) = ∑_{i ≤ n} binom(n, i) (g(i) + g(i+1))`. -/
private lemma sum_range_choose_succ_mul (n : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ range (n + 2), ((n + 1).choose i : ℝ) * g i =
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (g i + g (i + 1)) := by
  rw [sum_range_succ']
  simp_rw [Nat.choose_succ_succ', Nat.cast_add, add_mul, sum_add_distrib, mul_add,
    sum_add_distrib]
  have h : ∑ i ∈ range (n + 1), (n.choose i : ℝ) * g i =
      ∑ i ∈ range (n + 1), (n.choose (i + 1) : ℝ) * g (i + 1) + (n.choose 0 : ℝ) * g 0 := by
    rw [sum_range_succ', sum_range_succ (fun i ↦ (n.choose (i + 1) : ℝ) * g (i + 1)),
      Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  rw [h]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

/-- The binomial variance identity `∑_{i ≤ n} binom(n, i) (2i - n)² = n 2^n`. -/
private lemma sum_choose_mul_sq (n : ℕ) :
    ∑ i ∈ range (n + 1), (n.choose i : ℝ) * (2 * (i : ℝ) - n) ^ 2 = (n : ℝ) * 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n + 1 + 1 = n + 2 by rfl, sum_range_choose_succ_mul]
    have h : ∀ i ∈ range (n + 1), (n.choose i : ℝ) * ((2 * (i : ℝ) - ((n + 1 : ℕ) : ℝ)) ^ 2 +
        (2 * ((i + 1 : ℕ) : ℝ) - ((n + 1 : ℕ) : ℝ)) ^ 2) =
        2 * ((n.choose i : ℝ) * (2 * (i : ℝ) - n) ^ 2) + 2 * (n.choose i : ℝ) := by
      intro i _
      push_cast
      ring
    rw [sum_congr rfl h, sum_add_distrib, ← mul_sum, ← mul_sum, ih, ← Nat.cast_sum,
      Nat.sum_range_choose]
    push_cast
    ring

/-- Every partial sum of the variance sum is at most `n 2^n`. -/
private lemma sum_range_choose_mul_sq_le (n M : ℕ) :
    ∑ i ∈ range M, (n.choose i : ℝ) * (2 * (i : ℝ) - n) ^ 2 ≤ (n : ℝ) * 2 ^ n := by
  calc ∑ i ∈ range M, (n.choose i : ℝ) * (2 * (i : ℝ) - n) ^ 2
      ≤ ∑ i ∈ range ((n + 1) + M), (n.choose i : ℝ) * (2 * (i : ℝ) - n) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) fun _ _ _ ↦ by positivity
    _ = (n : ℝ) * 2 ^ n := by
        rw [sum_range_add, sum_choose_mul_sq]
        rw [sum_eq_zero fun x _ ↦ by rw [Nat.choose_eq_zero_of_lt (by omega)]; simp, add_zero]

/-- The odd-step partial sums are bounded by full blocks:
`∑_{i < N} binom(n, 2i + m) ≤ ∑_{j < 2N} binom(n, m + j)`. -/
private lemma sum_range_choose_two_mul_add_le (n m N : ℕ) :
    ∑ i ∈ range N, (n.choose (2 * i + m) : ℝ) ≤ ∑ j ∈ range (2 * N), (n.choose (m + j) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ,
      sum_range_succ]
    have h1 : (0 : ℝ) ≤ (n.choose (m + (2 * N + 1)) : ℝ) := by positivity
    rw [show 2 * N + m = m + 2 * N by ring]
    linarith

/-- The binomial tail beyond `m` with `2m - n ≥ s/5`: for every `N`,
`2^{-(n+1)} ∑_{i < N} binom(n, 2i + m) ≤ 25 n / (2 s²)`. -/
private lemma tail_bound {n m : ℕ} {s : ℝ} (hs : 0 < s) (hm : s / 5 ≤ 2 * (m : ℝ) - n) (N : ℕ) :
    (∑ i ∈ range N, (n.choose (2 * i + m) : ℝ)) * (2 : ℝ) ^ (-((n : ℤ) + 1)) ≤
      25 * n / (2 * s ^ 2) := by
  have hz : (2 : ℝ) ^ (-((n : ℤ) + 1)) = 1 / (2 * 2 ^ n) := by
    rw [show -((n : ℤ) + 1) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
      pow_succ]
    field_simp
  have hterm : ∀ j ∈ range (2 * N), (n.choose (m + j) : ℝ) ≤
      25 / s ^ 2 * ((n.choose (m + j) : ℝ) * (2 * ((m + j : ℕ) : ℝ) - n) ^ 2) := by
    intro j _
    have hj : s / 5 ≤ 2 * ((m + j : ℕ) : ℝ) - n := by
      push_cast
      linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)]
    have hsq : s ^ 2 / 25 ≤ (2 * ((m + j : ℕ) : ℝ) - n) ^ 2 := by
      have := pow_le_pow_left₀ (by positivity) hj 2
      linarith [show (s / 5) ^ 2 = s ^ 2 / 25 by ring]
    rw [← mul_assoc, mul_comm (25 / s ^ 2), mul_assoc]
    refine le_mul_of_one_le_right (by positivity) ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith
  have hsum : ∑ j ∈ range (2 * N), (n.choose (m + j) : ℝ) ≤ 25 / s ^ 2 * (n * 2 ^ n) := by
    calc ∑ j ∈ range (2 * N), (n.choose (m + j) : ℝ)
        ≤ ∑ j ∈ range (2 * N),
            25 / s ^ 2 * ((n.choose (m + j) : ℝ) * (2 * ((m + j : ℕ) : ℝ) - n) ^ 2) :=
          sum_le_sum hterm
      _ = 25 / s ^ 2 * ∑ j ∈ range (2 * N),
            (n.choose (m + j) : ℝ) * (2 * ((m + j : ℕ) : ℝ) - n) ^ 2 := by rw [mul_sum]
      _ ≤ 25 / s ^ 2 * (n * 2 ^ n) := by
          gcongr
          have h0 : 0 ≤ ∑ i ∈ range m, (n.choose i : ℝ) * (2 * (i : ℝ) - n) ^ 2 :=
            sum_nonneg fun _ _ ↦ by positivity
          have := sum_range_choose_mul_sq_le n (m + 2 * N)
          rw [sum_range_add] at this
          linarith
  rw [hz, mul_one_div, div_le_iff₀ (by positivity)]
  calc (∑ i ∈ range N, (n.choose (2 * i + m) : ℝ)) ≤ 25 / s ^ 2 * (n * 2 ^ n) :=
      (sum_range_choose_two_mul_add_le n m N).trans hsum
    _ = 25 * n / (2 * s ^ 2) * (2 * 2 ^ n) := by field_simp

/-- For each of the eight pairs `(c, O)`, with `t = s + O - c ∈ [s - 4, s]`,
`∑_{r=1}^{f} 𝖱(r - 1, t) ≥ 1/4 - 25/(2s)`. -/
private lemma inner_ge {s : ℕ} (hs : 256 ≤ s) {t : ℤ} (ht1 : (s : ℤ) - 4 ≤ t)
    (ht2 : t ≤ s) :
    1 / 4 - 25 / (2 * (s : ℝ)) ≤ ∑ r ∈ Icc 1 ((5 * s + 16) / 16), rawMass (r - 1) t := by
  set f := (5 * s + 16) / 16 with hf
  have hf16 : 5 * s + 1 ≤ 16 * f := by omega
  have hf1 : 1 ≤ f := by omega
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = n + 1 := ⟨(t - 1).toNat, by omega⟩
  have hns : n + 1 ≤ s := by omega
  -- drop the `r = 1` term
  have hdrop : ∑ k ∈ range (f - 1), rawMass (k + 1) ((n : ℤ) + 1) ≤
      ∑ r ∈ Icc 1 f, rawMass (r - 1) ((n : ℤ) + 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range,
      show f + 1 - 1 = (f - 1) + 1 by omega, sum_range_succ']
    simp only [show ∀ k, 1 + (k + 1) - 1 = k + 1 from fun k ↦ by omega]
    linarith [rawMass_nonneg (1 + 0 - 1) ((n : ℤ) + 1)]
  have hsum := hasSum_rawMass_succ (t := (n : ℤ) + 1) (by omega)
  have hsplit := hsum.summable.sum_add_tsum_nat_add (f - 1)
  rw [hsum.tsum_eq] at hsplit
  -- the tail
  have hs0 : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hn : (n : ℝ) + 1 ≤ s := by exact_mod_cast hns
  have hm : (s : ℝ) / 5 ≤ 2 * ((2 * f - 1 : ℕ) : ℝ) - n := by
    have h1 : ((5 * s + 1 : ℕ) : ℝ) ≤ ((16 * f : ℕ) : ℝ) := by exact_mod_cast hf16
    have h3 : (256 : ℝ) ≤ s := by exact_mod_cast hs
    rw [Nat.cast_sub (by omega)]
    push_cast at h1 ⊢
    linarith
  have htail : ∑' i : ℕ, rawMass (i + (f - 1) + 1) ((n : ℤ) + 1) ≤ 25 / (2 * (s : ℝ)) := by
    refine Real.tsum_le_of_sum_range_le (fun _ ↦ rawMass_nonneg _ _) fun N ↦ ?_
    have hform : ∀ i : ℕ, rawMass (i + (f - 1) + 1) ((n : ℤ) + 1) =
        (n.choose (2 * i + (2 * f - 1)) : ℝ) * (2 : ℝ) ^ (-((n : ℤ) + 1)) := by
      intro i
      rw [rawMass_eq_choose (by omega), show ((n : ℤ) + 1 - 1).toNat = n by omega,
        show 2 * (i + (f - 1) + 1) - 1 = 2 * i + (2 * f - 1) by omega]
    simp_rw [hform, ← sum_mul]
    refine (tail_bound hs0 hm N).trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **The closing exit mass at large gaps.** For every integer `s ≥ 256`,
`p₄₅(s) ≥ 5/16 - 125/(8s)`. -/
@[collatz_pos_dens "lem_rn_p45_large"]
theorem p45_ge_of_le {s : ℕ} (hs : 256 ≤ s) : 5 / 16 - 125 / (8 * (s : ℝ)) ≤ p45 s := by
  set L := 1 / 4 - 25 / (2 * (s : ℝ)) with hL
  have hinner : ∀ c ∈ Icc (4 : ℤ) 5, 4 * L ≤
      ∑ O ∈ Icc (1 : ℤ) 4, ∑ r ∈ Icc 1 ((5 * s + 16) / 16), rawMass (r - 1) ((s : ℤ) + O - c) := by
    intro c hc
    rw [mem_Icc] at hc
    calc 4 * L = ∑ _O ∈ Icc (1 : ℤ) 4, L := by simp
      _ ≤ _ := sum_le_sum fun O hO ↦ by
          rw [mem_Icc] at hO
          exact inner_ge hs (by omega) (by omega)
  calc 5 / 16 - 125 / (8 * (s : ℝ)) = ∑ c ∈ Icc (4 : ℤ) 5, varpi c * (4 * L) := by
        rw [← sum_mul, show Icc (4 : ℤ) 5 = {4, 5} by rfl, sum_pair (by norm_num), varpi_four,
          varpi_five, hL]
        ring
    _ ≤ p45 s := sum_le_sum fun c hc ↦ mul_le_mul_of_nonneg_left (hinner c hc) (varpi_nonneg c)

end CollatzPosDens
