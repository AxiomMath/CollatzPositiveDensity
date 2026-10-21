/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.FirstCrossing.Width
public import CollatzPosDens.OrdinaryTime.S07Bstar
public import CollatzPosDens.OrdinaryTime.S07Wstar
public import CollatzPosDens.OrdinaryTime.CkScaleDoubling
public import CollatzPosDens.OrdinaryTime.CkWidthLate
public import CollatzPosDens.Recipe.CovGen
public import Mathlib.Algebra.Order.Field.GeomSum

/-!
# The width sum is small against the scale sum

For every integer $n \ge$ `covGen` $= 23000$,
$$9000 \cdot \mathtt{widthSum}(n) \le \mathtt{scaleSum}(n),$$
where `widthSum n` $= \sum_{j=0}^{n-1} \mathrm{wd}(b_j)$ is the width sum and
`scaleSum n` $= \sum_{j=0}^{n} b_j$ is the scale sum, with $b_j$ = `scale j`. Below, $W_*(n)$
and $B_*(n)$ abbreviate `widthSum n` and `scaleSum n`.

The proof splits the indices $j < n$ of $W_*(n)$ into the set $S$ of those with $b_j < 2^{40}$
and the set $S'$ of those with $b_j \ge 2^{40}$.

*Early part.* On $S$, $\mathrm{wd}(b_j) \le b_j$. If $m$ is the largest element of $S$, geometric
growth of the scales gives $2^{40} > b_m \ge \mathsf g^{m-j} b_j$ for $j \in S$, with
$\mathsf g = 101/100$; the exponents $m - j$ are distinct, so
$\sum_{j \in S} b_j \le 2^{40} \sum_{i=0}^{m} (100/101)^i \le 101 \cdot 2^{40}$.

*Late part.* On $S'$, $20000\,\mathrm{wd}(b_j) \le b_j$, and these $b_j$ are summands of $B_*(n)$,
so $20000 \sum_{j \in S'} \mathrm{wd}(b_j) \le B_*(n)$.

*Conclusion.* As $\lfloor n/70 \rfloor \ge 328$, the scales doubling every $70$ generations give
$B_*(n) \ge b_n \ge 16544 \cdot 2^{328} \ge 2^{342}$, and
$9000 \cdot 101 \cdot 2^{40} < 2^{60} \le \frac{11}{20} 2^{342}$, so
$9000\,W_*(n) \le \frac{11}{20} B_*(n) + \frac{9}{20} B_*(n) = B_*(n)$.

## Main results

* `CollatzPosDens.nine_thousand_mul_widthSum_le_scaleSum`: `9000 * widthSum n ≤ scaleSum n` for
  `covGen ≤ n`.

## Implementation notes

The final comparison is carried out in `ℕ` after multiplying through by `20`: the claim becomes
`180000 * widthSum n ≤ 20 * scaleSum n`, which avoids all fractions. Only the geometric series of
the early part is summed in `ℝ`.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The scales below `2^{40}` among the generations `j < n` sum to at most `101 · 2^{40}`. -/
private theorem sum_scale_filter_lt_two_pow_forty_le (n : ℕ) :
    ∑ j ∈ (range n).filter (fun j => scale j < 2 ^ 40), scale j ≤ 101 * 2 ^ 40 := by
  set S := (range n).filter (fun j => scale j < 2 ^ 40)
  rcases S.eq_empty_or_nonempty with h | h
  · simp [h]
  set m := S.max' h
  have hbm : (scale m : ℝ) < 2 ^ 40 := by exact_mod_cast (mem_filter.1 (S.max'_mem h)).2
  set r : ℝ := 100 / 101
  have hr0 : 0 ≤ r := by norm_num [r]
  have hle : ∀ j ∈ S, (scale j : ℝ) ≤ 2 ^ 40 * r ^ (m - j) := by
    intro j hj
    have hjm : j ≤ m := S.le_max' j hj
    have hg := scale_add_ge_growthRatio_pow_mul j (m - j)
    rw [Nat.add_sub_cancel' hjm, growthRatio_cast] at hg
    have hrk : 0 ≤ r ^ (m - j) := pow_nonneg hr0 _
    have hone : r ^ (m - j) * (101 / 100 : ℝ) ^ (m - j) = 1 := by
      rw [← mul_pow]; norm_num [r]
    calc (scale j : ℝ) = r ^ (m - j) * ((101 / 100 : ℝ) ^ (m - j) * scale j) := by
          rw [← mul_assoc, hone, one_mul]
      _ ≤ r ^ (m - j) * 2 ^ 40 := mul_le_mul_of_nonneg_left (hg.trans hbm.le) hrk
      _ = 2 ^ 40 * r ^ (m - j) := mul_comm _ _
  have hsub : S ⊆ range (m + 1) := fun j hj => mem_range.2 (Nat.lt_succ_of_le (S.le_max' j hj))
  have hgeom : ∑ i ∈ range (m + 1), r ^ i ≤ 101 := by
    rw [range_eq_Ico]
    refine (geom_sum_Ico_le_of_lt_one hr0 (by norm_num [r])).trans (le_of_eq ?_)
    norm_num [r]
  have hreal : ((∑ j ∈ S, scale j : ℕ) : ℝ) ≤ 101 * 2 ^ 40 := by
    push_cast
    calc ∑ j ∈ S, (scale j : ℝ) ≤ ∑ j ∈ S, 2 ^ 40 * r ^ (m - j) := sum_le_sum hle
      _ ≤ ∑ j ∈ range (m + 1), 2 ^ 40 * r ^ (m - j) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 2 ^ 40 * ∑ i ∈ range (m + 1), r ^ i := by
          rw [← mul_sum, ← sum_range_reflect (fun i => r ^ i) (m + 1)]
          simp only [Nat.add_sub_cancel]
      _ ≤ 2 ^ 40 * 101 := by gcongr
      _ = 101 * 2 ^ 40 := mul_comm _ _
  exact_mod_cast hreal

/-- For every `n ≥ covGen`, nine thousand times the width sum `widthSum n` is at most the scale
sum `scaleSum n`. -/
@[collatz_pos_dens "lem_width_sum"]
theorem nine_thousand_mul_widthSum_le_scaleSum (n : ℕ) (hn : covGen ≤ n) :
    9000 * widthSum n ≤ scaleSum n := by
  rw [widthSum_def, ← sum_filter_add_sum_filter_not (range n) (fun j => scale j < 2 ^ 40)]
  set E := ∑ j ∈ (range n).filter (fun j => scale j < 2 ^ 40), wd (scale j)
  set L := ∑ j ∈ (range n).filter (fun j => ¬scale j < 2 ^ 40), wd (scale j)
  have hE : E ≤ 101 * 2 ^ 40 :=
    (sum_le_sum fun _ _ => (wd_lt_self (scale_pos _)).le).trans
      (sum_scale_filter_lt_two_pow_forty_le n)
  have hL : 20000 * L ≤ scaleSum n := by
    rw [mul_sum]
    refine (sum_le_sum fun j hj => twenty_thousand_mul_wd_le
      (not_lt.1 (mem_filter.1 hj).2)).trans ?_
    exact sum_le_sum_of_subset_of_nonneg
      (fun j hj => mem_range.2 (Nat.lt_succ_of_lt (mem_range.1 (mem_filter.1 hj).1)))
      fun _ _ _ => Nat.zero_le _
  have hk : 328 ≤ n / 70 := by rw [covGen_def] at hn; omega
  have hB : 2 ^ 14 * 2 ^ (n / 70) ≤ scaleSum n :=
    calc 2 ^ 14 * 2 ^ (n / 70) ≤ 16544 * 2 ^ (n / 70) := Nat.mul_le_mul_right _ (by norm_num)
      _ ≤ scale n := sixteen544_mul_two_pow_div_seventy_le_scale n
      _ ≤ scaleSum n := scale_le_scaleSum n
  have hc : 20 * (9000 * (101 * 2 ^ 40)) ≤ 11 * (2 ^ 14 * 2 ^ (n / 70)) := by
    have h66 : 2 ^ 26 * 2 ^ 40 ≤ 2 ^ (n / 70) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (by omega)
    calc 20 * (9000 * (101 * 2 ^ 40)) ≤ 11 * (2 ^ 14 * (2 ^ 26 * 2 ^ 40)) := by norm_num
      _ ≤ 11 * (2 ^ 14 * 2 ^ (n / 70)) := by gcongr
  generalize 2 ^ 14 * 2 ^ (n / 70) = P at hB hc
  generalize scaleSum n = B at hB hL ⊢
  generalize (2 : ℕ) ^ 40 = Q at hE hc
  nlinarith

end CollatzPosDens
