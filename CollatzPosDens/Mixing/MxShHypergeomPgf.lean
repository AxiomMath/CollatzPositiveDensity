/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# A factorial-moment bound for subsets

Let `S` be a finite set with `N` elements, `J` a set and `z ≥ 1` a real number. Choosing an
`m`-subset `X` of `S` uniformly at random, the number `|X ∩ J|` is hypergeometric, and its
probability generating function at `z` is at most that of a binomial law of parameter `m / N`:
$$\sum_{X \subseteq S,\ |X| = m} z^{|X \cap J|}
  \le \binom Nm \Bigl(1 + (z - 1)\frac mN\Bigr)^{|S \cap J|}.$$

The proof expands `z^c = ((z - 1) + 1)^c = ∑_{Y ⊆ X ∩ J} (z - 1)^{|Y|}`, exchanges the two sums
and counts, for each `Y ⊆ S ∩ J` with `|Y| = h ≤ m`, the `m`-subsets of `S` containing `Y`: there
are `binom (N - h) (m - h)` of them, and `binom (N - h) (m - h) ≤ binom N m (m / N)^h` since each
factor of `binom (N - h) (m - h) / binom N m = ∏_{i < h} (m - i) / (N - i)` is at most `m / N`.
Summing `binom N m ((z - 1) m / N)^{|Y|}` over `Y ⊆ S ∩ J` gives the right-hand side.

## Main results

* `CollatzPosDens.choose_sub_le_choose_mul_div_pow`:
  `binom (N - h) (m - h) ≤ binom N m (m / N)^h` for `h ≤ m ≤ N`.
* `CollatzPosDens.sum_powersetCard_pow_card_inter_le`: the bound above for a finset `S`.
* `CollatzPosDens.sum_powersetCard_Icc_pow_card_inter_le`: the case `S = {1, …, N}`,
  `J = {1, …, j}`, where the right-hand side reads `binom N m (1 + (z - 1) m / N)^j`.

## Implementation notes

The statements need no hypothesis besides `1 ≤ z`: when `m > N` both sides vanish, and when
`N = 0` the division `m / N` is `0` and both sides equal `binom 0 m`. In the case of intervals the
exponent `j` may exceed `N`, because the base is at least `1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- For `h ≤ m ≤ N`, `binom (N - h) (m - h) ≤ binom N m (m / N)^h`: the ratio of the two binomial
coefficients is `∏_{i < h} (m - i) / (N - i)`, and each factor is at most `m / N`. -/
theorem choose_sub_le_choose_mul_div_pow {N m h : ℕ} (hhm : h ≤ m) (hmN : m ≤ N) :
    ((N - h).choose (m - h) : ℝ) ≤ N.choose m * ((m : ℝ) / N) ^ h := by
  induction h with
  | zero => simp
  | succ h ih =>
    have ih := ih (by omega)
    have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hNh : (0 : ℝ) < ((N - h : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - h by omega)
    have key := Nat.add_one_mul_choose_eq (N - (h + 1)) (m - (h + 1))
    rw [show N - (h + 1) + 1 = N - h by omega, show m - (h + 1) + 1 = m - h by omega] at key
    have key' : ((N - h : ℕ) : ℝ) * ((N - (h + 1)).choose (m - (h + 1)) : ℝ) =
        ((N - h).choose (m - h) : ℝ) * ((m - h : ℕ) : ℝ) := by exact_mod_cast key
    have hratio : ((m - h : ℕ) : ℝ) * N ≤ (m : ℝ) * ((N - h : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      have : (h : ℝ) * m ≤ h * N := by gcongr
      nlinarith
    have hc0 : (0 : ℝ) ≤ ((N - h).choose (m - h) : ℝ) := by positivity
    rw [← mul_le_mul_iff_of_pos_left hNh, key', pow_succ]
    calc ((N - h).choose (m - h) : ℝ) * ((m - h : ℕ) : ℝ)
        ≤ ((N - h).choose (m - h) : ℝ) * ((m : ℝ) / N * ((N - h : ℕ) : ℝ)) := by
          gcongr
          rw [div_mul_eq_mul_div, le_div_iff₀ hN]
          exact hratio
      _ ≤ N.choose m * ((m : ℝ) / N) ^ h * ((m : ℝ) / N * ((N - h : ℕ) : ℝ)) := by
          gcongr
      _ = ((N - h : ℕ) : ℝ) * (N.choose m * (((m : ℝ) / N) ^ h * ((m : ℝ) / N))) := by ring

/-- The number of `m`-subsets of `S` containing a given `Y ⊆ S` is at most
`binom |S| m (m / |S|)^{|Y|}`. -/
theorem card_filter_powersetCard_subset_le {α : Type*} [DecidableEq α] {S Y : Finset α}
    (hY : Y ⊆ S) (m : ℕ) :
    (#{X ∈ S.powersetCard m | Y ⊆ X} : ℝ) ≤ (#S).choose m * ((m : ℝ) / #S) ^ #Y := by
  by_cases hYm : #Y ≤ m
  · by_cases hmS : m ≤ #S
    · rw [card_filter_powersetCard_subset Y S m hY hYm]
      exact choose_sub_le_choose_mul_div_pow hYm hmS
    · rw [powersetCard_eq_empty.2 (by omega)]
      simp only [filter_empty, card_empty, Nat.cast_zero]
      positivity
  · have : ({X ∈ S.powersetCard m | Y ⊆ X} : Finset (Finset α)) = ∅ := by
      refine filter_false_of_mem fun X hX hYX => hYm ?_
      exact (card_le_card hYX).trans (mem_powersetCard.1 hX).2.le
    rw [this, card_empty, Nat.cast_zero]
    positivity

/-- **Factorial-moment bound for subsets.** For a finset `S`, a finset `J` and a real `z ≥ 1`,
`∑_{X ⊆ S, |X| = m} z^{|X ∩ J|} ≤ binom |S| m (1 + (z - 1) m / |S|)^{|S ∩ J|}`. -/
theorem sum_powersetCard_pow_card_inter_le {α : Type*} [DecidableEq α] (S J : Finset α) (m : ℕ)
    {z : ℝ} (hz : 1 ≤ z) :
    ∑ X ∈ S.powersetCard m, z ^ #(X ∩ J) ≤
      (#S).choose m * (1 + (z - 1) * m / #S) ^ #(S ∩ J) := by
  have hexp (A : Finset α) (x : ℝ) : (x + 1) ^ #A = ∑ Y ∈ A.powerset, x ^ #Y := by
    rw [← sum_pow_mul_eq_add_pow]
    simp
  calc ∑ X ∈ S.powersetCard m, z ^ #(X ∩ J)
      = ∑ X ∈ S.powersetCard m, ∑ Y ∈ (X ∩ J).powerset, (z - 1) ^ #Y := by
        refine sum_congr rfl fun X _ => ?_
        rw [← hexp, sub_add_cancel]
    _ = ∑ Y ∈ (S ∩ J).powerset, ∑ X ∈ S.powersetCard m with Y ⊆ X, (z - 1) ^ #Y := by
        refine sum_comm' fun X Y => ?_
        simp only [mem_powersetCard, mem_powerset, mem_filter, subset_inter_iff]
        constructor
        · rintro ⟨⟨hXS, hX⟩, hYX, hYJ⟩
          exact ⟨⟨⟨hXS, hX⟩, hYX⟩, hYX.trans hXS, hYJ⟩
        · rintro ⟨⟨⟨hXS, hX⟩, hYX⟩, -, hYJ⟩
          exact ⟨⟨hXS, hX⟩, hYX, hYJ⟩
    _ = ∑ Y ∈ (S ∩ J).powerset, (#{X ∈ S.powersetCard m | Y ⊆ X} : ℝ) * (z - 1) ^ #Y := by
        simp [sum_const, nsmul_eq_mul]
    _ ≤ ∑ Y ∈ (S ∩ J).powerset, (#S).choose m * ((m : ℝ) / #S) ^ #Y * (z - 1) ^ #Y := by
        refine sum_le_sum fun Y hY => ?_
        have hz1 : (0 : ℝ) ≤ z - 1 := by linarith
        exact mul_le_mul_of_nonneg_right (card_filter_powersetCard_subset_le
          ((mem_powerset.1 hY).trans inter_subset_left) m) (pow_nonneg hz1 _)
    _ = (#S).choose m * (1 + (z - 1) * m / #S) ^ #(S ∩ J) := by
        rw [add_comm, hexp, mul_sum]
        refine sum_congr rfl fun Y _ => ?_
        rw [mul_assoc, ← mul_pow, mul_div_assoc]
        ring

/-- **Factorial-moment bound for subsets of an interval.** For natural numbers `N, m, j` and a
real `z ≥ 1`,
`∑_{X ⊆ {1, …, N}, |X| = m} z^{|X ∩ {1, …, j}|} ≤ binom N m (1 + (z - 1) m / N)^j`. -/
@[collatz_pos_dens "lem_mx_sh_hypergeom_pgf"]
theorem sum_powersetCard_Icc_pow_card_inter_le (N m j : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    ∑ X ∈ (Icc 1 N).powersetCard m, z ^ #(X ∩ Icc 1 j) ≤
      N.choose m * (1 + (z - 1) * m / N) ^ j := by
  have h := sum_powersetCard_pow_card_inter_le (Icc 1 N) (Icc 1 j) m hz
  rw [Nat.card_Icc, Nat.add_sub_cancel] at h
  refine h.trans ?_
  have hz1 : (0 : ℝ) ≤ z - 1 := by linarith
  have hbase : (1 : ℝ) ≤ 1 + (z - 1) * m / N := by
    have : (0 : ℝ) ≤ (z - 1) * m / N := by positivity
    linarith
  refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase ?_) (Nat.cast_nonneg _)
  calc #(Icc 1 N ∩ Icc 1 j) ≤ #(Icc 1 j) := card_le_card inter_subset_right
      _ = j := by simp

end CollatzPosDens
