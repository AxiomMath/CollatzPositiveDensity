/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnRawMass
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Closed form of the raw-prefix mass

For integers `k ≥ 1` and `t`, the raw-prefix mass `𝖱(k, t)`, the `k`-fold convolution power of
the Pascal law `ϖ` at `t`, is `𝖱(k, t) = binom(t - 1, 2k - 1) 2^{-t}`.

Indeed `2^b ϖ(b)` counts the pairs `(x, y)` of positive integers with `x + y = b`, so
`2^t 𝖱(k, t)` counts the compositions of `t` into `2k` positive parts, of which there are
`binom(t - 1, 2k - 1)`.

## Main results

* `CollatzPosDens.rawMass_eq_choose`: for `k ≥ 1` and `t ∈ ℤ`,
  `𝖱(k, t) = binom((t - 1)₊, 2k - 1) 2^{-t}`.
* `CollatzPosDens.rawMass_succ_natCast`: for `k, t ∈ ℕ`,
  `𝖱(k + 1, t) = binom(t - 1, 2k + 1) (1/2)^t` (truncated subtraction).
* `CollatzPosDens.rawMass_natCast_succ_eq_sum_antidiagonal`: the convolution recursion of
  `𝖱` indexed by the antidiagonal of `t ∈ ℕ`.

## Implementation notes

Instead of counting compositions directly, we induct on `k` through the convolution recursion
`𝖱(k + 1, t) = ∑_{a + b = t} ϖ(a) 𝖱(k, b)`, using the identity
`∑_{i + j = n} binom(i, p) binom(j, q) = binom(n + 1, p + q + 1)` (the composition count
grouped by the position of the `(p + 1)`-st cut). [mazur2026] states the formula for `t ≥ 1`;
it holds for every integer `t` (both sides vanish for `t ≤ 0`, reading `t - 1` as its positive
part), and we state it so.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- `∑_{i + j = n} binom(i, p) binom(j, q) = binom(n + 1, p + q + 1)`. -/
private lemma sum_antidiagonal_choose_mul_choose (n p q : ℕ) :
    ∑ ij ∈ antidiagonal n, ij.1.choose p * ij.2.choose q = (n + 1).choose (p + q + 1) := by
  induction n generalizing q with
  | zero =>
    rcases p with _ | p <;> rcases q with _ | q <;> simp [Nat.choose_eq_zero_of_lt]
  | succ n ih =>
    rw [Nat.sum_antidiagonal_succ']
    rcases q with _ | q
    · simp only [Nat.choose_zero_right, mul_one, add_zero]
      have h := ih 0
      simp only [Nat.choose_zero_right, mul_one, add_zero] at h
      rw [h, Nat.choose_succ_succ' (n + 1) p]
    · simp only [Nat.choose_succ_succ', mul_add, sum_add_distrib, ih, Nat.choose_zero_succ,
        mul_zero, zero_add]
      rw [show p + (q + 1) = p + q + 1 by omega, Nat.choose_succ_succ' n (p + q)]

/-- The shifted composition count: for `p, q ≥ 1`,
`∑_{a + b = t} binom(a - 1, p) binom(b - 1, q) = binom(t - 1, p + q + 1)`
(truncated subtraction). -/
private lemma sum_antidiagonal_choose_pred_mul_choose_pred (t : ℕ) {p q : ℕ} (hp : 1 ≤ p)
    (hq : 1 ≤ q) :
    ∑ ab ∈ antidiagonal t, (ab.1 - 1).choose p * (ab.2 - 1).choose q =
      (t - 1).choose (p + q + 1) := by
  have hp0 : Nat.choose 0 p = 0 := Nat.choose_eq_zero_of_lt (by omega)
  have hq0 : Nat.choose 0 q = 0 := Nat.choose_eq_zero_of_lt (by omega)
  rcases t with _ | _ | n
  · simp [hp0]
  · rw [Nat.sum_antidiagonal_succ]
    simp [hp0]
  · rw [Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ']
    simp only [hp0, hq0, Nat.zero_sub, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
    exact sum_antidiagonal_choose_mul_choose n p q

/-- `ϖ(a) = binom(a - 1, 1) (1/2)^a` for every `a ∈ ℕ` (truncated subtraction). -/
private lemma varpi_natCast_eq_choose (a : ℕ) :
    varpi a = ((a - 1).choose 1 : ℝ) * (1 / 2) ^ a := by
  rcases a with _ | _ | n
  · simp [varpi_of_le_one]
  · simp [varpi_of_le_one]
  · rw [show ((n + 1 + 1 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring, varpi_natCast_add_two]
    simp

/-- The convolution recursion of `𝖱` over the antidiagonal:
`𝖱(k + 1, t) = ∑_{a + b = t} ϖ(a) 𝖱(k, b)` for `t ∈ ℕ`. -/
theorem rawMass_natCast_succ_eq_sum_antidiagonal (k t : ℕ) :
    rawMass (k + 1) t = ∑ ab ∈ antidiagonal t, varpi ab.1 * rawMass k ab.2 := by
  rw [rawMass_succ, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have hsub : Icc (2 : ℤ) t ⊆ Icc 0 t := Icc_subset_Icc_left (by norm_num)
  rw [sum_subset hsub (fun a ha hna ↦ by
    simp only [mem_Icc, not_and, not_le] at ha hna
    rw [varpi_of_le_one (by omega), zero_mul])]
  refine sum_nbij' (fun a ↦ a.toNat) (fun a ↦ (a : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [mem_Icc] at ha
    simp only [mem_range]
    omega
  · intro a ha
    simp only [mem_range] at ha
    simp only [mem_Icc]
    omega
  · intro a ha
    simp only [mem_Icc] at ha
    simp only [Int.toNat_of_nonneg ha.1]
  · intro a _
    simp
  · intro a ha
    simp only [mem_Icc] at ha
    simp only [Int.toNat_of_nonneg ha.1]
    congr 2
    omega

/-- For `k, t ∈ ℕ`, `𝖱(k + 1, t) = binom(t - 1, 2k + 1) (1/2)^t` (truncated subtraction). -/
theorem rawMass_succ_natCast (k t : ℕ) :
    rawMass (k + 1) t = ((t - 1).choose (2 * k + 1) : ℝ) * (1 / 2) ^ t := by
  induction k generalizing t with
  | zero =>
    rw [rawMass_natCast_succ_eq_sum_antidiagonal]
    rcases t with _ | s
    · simp [rawMass_zero, varpi_of_le_one]
    · rw [Nat.sum_antidiagonal_succ']
      have h : ∀ x : ℕ, ((x + 1 : ℕ) : ℤ) ≠ 0 := fun x ↦ by omega
      simp only [rawMass_zero, h, ite_false, mul_zero, sum_const_zero, add_zero, Nat.cast_zero,
        ite_true, mul_one, varpi_natCast_eq_choose]
  | succ k ih =>
    rw [rawMass_natCast_succ_eq_sum_antidiagonal]
    have key := sum_antidiagonal_choose_pred_mul_choose_pred t (p := 1) (q := 2 * k + 1)
      le_rfl (by omega)
    rw [show 1 + (2 * k + 1) + 1 = 2 * (k + 1) + 1 by ring] at key
    rw [← key, Nat.cast_sum, sum_mul]
    refine sum_congr rfl fun ab hab ↦ ?_
    rw [mem_antidiagonal] at hab
    rw [varpi_natCast_eq_choose, ih, ← hab, pow_add]
    push_cast
    ring

/-- **Closed form of the raw-prefix mass.** For `k ≥ 1` and every integer `t`,
`𝖱(k, t) = binom(t - 1, 2k - 1) 2^{-t}`, reading `t - 1` as its positive part (both sides vanish
for `t ≤ 0`). -/
@[collatz_pos_dens "lem_rn_raw_mass_formula"]
theorem rawMass_eq_choose {k : ℕ} (hk : 1 ≤ k) (t : ℤ) :
    rawMass k t = ((t - 1).toNat.choose (2 * k - 1) : ℝ) * (2 : ℝ) ^ (-t) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  rcases le_or_gt 0 t with ht | ht
  · lift t to ℕ using ht
    rw [rawMass_succ_natCast, show ((t : ℤ) - 1).toNat = t - 1 by omega, zpow_neg,
      zpow_natCast, one_div_pow, one_div]
  · rw [rawMass_succ_of_lt_two _ (by omega), show (t - 1).toNat = 0 by omega,
      Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The raw-prefix mass of one pair: `𝖱(1, t) = binom(t - 1, 1) 2^{-t}`. -/
theorem rawMass_one (t : ℤ) :
    rawMass 1 t = ((t - 1).toNat.choose 1 : ℝ) * (2 : ℝ) ^ (-t) :=
  rawMass_eq_choose le_rfl t

end CollatzPosDens
