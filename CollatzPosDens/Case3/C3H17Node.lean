/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Case3.C3H17CapUp

/-!
# Rounded future costs

For integers `h ≥ 1` and `z` the rationals `cf⁺_h(z)` are defined by downward recursion on `h`:
`cf⁺_h(z) = 1` for `h ≥ 15`, and for `1 ≤ h ≤ 14`
`cf⁺_h(z) = 10^{-8} ⌈10^8 (1 - ∑_{d=2}^{17-h} ϖ(d) [1 - Ū_d(z / 2^{h+d}) G_d])⌉`,
where `G_d = cf⁺_{h+d}(9z)` if `d ∉ {4, 5}` and `h + d ≤ 15`, and `G_d = 1` otherwise. Here `ϖ` is
the Pascal weight and `Ū_d` the grid majorant of the capped packet factor. These are rational
majorants, rounded up to the mesh `10^{-8}`, of the future costs `cf_h(z)`.

## Main definitions

* `CollatzPosDens.c3H17Node`: the rounded future cost `cf⁺_h(z)`.

## Main results

* `CollatzPosDens.c3H17Node_of_le`: `cf⁺_h(z) = 1` for `h ≥ 15`.
* `CollatzPosDens.c3H17Node_of_lt`: the recursion for `h < 15`, with rational Pascal weights.
* `CollatzPosDens.c3H17Node_sum_cast`: the number inside the ceiling, read in `ℝ` with the
  weights `ϖ(d)`.
* `CollatzPosDens.c3H17Node_nonneg`, `CollatzPosDens.c3H17Node_le_one`: `0 ≤ cf⁺_h(z) ≤ 1`.

## Implementation notes

The cost is computable and rational-valued. The Pascal weight `ϖ(d) = (d - 1) 2^{-d}` (for
`d ≥ 2`) is real-valued in `CollatzPosDens.varpi`, so the definition uses its rational form
`(d - 1) 2^{-d}` on the summation range, where `d ≥ 2`; `c3H17Node_sum_cast` restates the
summand with `varpi`. The rounding `10^{-8} ⌈10^8 x⌉` is written `⌈10^8 x⌉ / 10^8`. The index
`h` ranges over all of `ℤ`, and for `h ≤ 0` the same recursion is used, extending the definition
in [mazur2026], which is stated for `h ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The rounded future costs: `cf⁺_h(z) = 1` for `h ≥ 15`, and otherwise
`cf⁺_h(z) = 10^{-8} ⌈10^8 (1 - ∑_{d=2}^{17-h} ϖ(d) [1 - Ū_d(z / 2^{h+d}) G_d])⌉` with
`G_d = cf⁺_{h+d}(9z)` if `d ∉ {4, 5}` and `h + d ≤ 15`, and `G_d = 1` otherwise; the Pascal weight
is written as `ϖ(d) = (d - 1) 2^{-d}`. -/
@[collatz_pos_dens "def_c3_h17_node"]
def c3H17Node (h z : ℤ) : ℚ :=
  if 15 ≤ h then 1
  else
    (⌈(10 ^ 8 : ℚ) * (1 - ∑ d ∈ (Finset.Icc (2 : ℤ) (17 - h)).attach,
        (((d : ℤ) : ℚ) - 1) * (2 : ℚ) ^ (-(d : ℤ)) *
          (1 - c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
            if (d : ℤ) ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z)
            else 1))⌉ : ℚ) / 10 ^ 8
termination_by (15 - h).toNat
decreasing_by
  have := d.2
  simp only [Finset.mem_Icc] at this
  omega

/-- The rounded future cost `cf⁺_h(z)` equals `1` for `h ≥ 15`. -/
theorem c3H17Node_of_le {h : ℤ} (hh : 15 ≤ h) (z : ℤ) : c3H17Node h z = 1 := by
  rw [c3H17Node]
  simp [hh]

/-- The recursion defining `cf⁺_h(z)` for `h < 15`. -/
theorem c3H17Node_of_lt {h : ℤ} (hh : h < 15) (z : ℤ) :
    c3H17Node h z =
      (⌈(10 ^ 8 : ℚ) * (1 - ∑ d ∈ Finset.Icc (2 : ℤ) (17 - h),
          ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) *
            (1 - c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
              if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z)
              else 1))⌉ : ℚ) / 10 ^ 8 := by
  rw [c3H17Node, ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    Finset.sum_attach _ (fun d : ℤ => ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) *
      (1 - c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
        if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z) else 1))]

/-- The rational Pascal weight agrees with `ϖ` for `d ≥ 2`. -/
private theorem cast_pascal {d : ℤ} (hd : 2 ≤ d) :
    ((((d : ℚ) - 1) * (2 : ℚ) ^ (-d) : ℚ) : ℝ) = varpi d := by
  rw [varpi_of_two_le hd]
  push_cast
  rfl

/-- The number inside the ceiling defining `cf⁺_h(z)`, `h < 15`, read in `ℝ` with the Pascal
weights `ϖ(d)`. -/
theorem c3H17Node_sum_cast {h : ℤ} (z : ℤ) :
    ((∑ d ∈ Finset.Icc (2 : ℤ) (17 - h),
          ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) *
            (1 - c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
              if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z)
              else 1) : ℚ) : ℝ) =
      ∑ d ∈ Finset.Icc (2 : ℤ) (17 - h), varpi d *
        (1 - (c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) : ℝ) *
          if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then (c3H17Node (h + d) (9 * z) : ℝ)
          else 1) := by
  push_cast
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [← cast_pascal hd.1]
  push_cast
  split_ifs <;> simp

/-- The Pascal weights on a finite range `2 ≤ d ≤ N` sum to at most `1`. -/
private theorem sum_pascal_le_one (N : ℤ) :
    ∑ d ∈ Finset.Icc (2 : ℤ) N, ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) ≤ 1 := by
  have key : ((∑ d ∈ Finset.Icc (2 : ℤ) N, ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) : ℚ) : ℝ) ≤ 1 := by
    push_cast
    have hs : ∑ d ∈ Finset.Icc (2 : ℤ) N, ((d : ℝ) - 1) * (2 : ℝ) ^ (-d) =
        ∑ n ∈ Finset.range (N - 1).toNat, varpi ((n : ℤ) + 2) := by
      symm
      refine Finset.sum_nbij' (fun n : ℕ => (n : ℤ) + 2) (fun d => (d - 2).toNat) ?_ ?_ ?_ ?_ ?_
      · intro n hn
        simp only [Finset.mem_range, Finset.mem_Icc] at hn ⊢
        omega
      · intro d hd
        simp only [Finset.mem_range, Finset.mem_Icc] at hd ⊢
        omega
      · intro n _
        simp
      · intro d hd
        simp only [Finset.mem_Icc] at hd
        omega
      · intro n _
        rw [varpi_of_two_le (by omega)]
    rw [hs]
    exact sum_le_hasSum _ (fun n _ => varpi_nonneg _) hasSum_varpi_add_two
  exact_mod_cast key

/-- The rounded future costs are at most `1`. -/
theorem c3H17Node_le_one (h z : ℤ) : c3H17Node h z ≤ 1 := by
  rcases le_or_gt 15 h with hh | hh
  · rw [c3H17Node_of_le hh]
  rw [c3H17Node_of_lt hh, div_le_one (by norm_num)]
  have hsum : 0 ≤ ∑ d ∈ Finset.Icc (2 : ℤ) (17 - h),
      ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) *
        (1 - c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
          if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z) else 1) := by
    refine Finset.sum_nonneg fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hw : (0 : ℚ) ≤ (d : ℚ) - 1 := by
      have : (2 : ℚ) ≤ d := by exact_mod_cast hd.1
      linarith
    have hU := c3H17CapUp_le_one d ((z : ℚ) / 2 ^ (h + d))
    have hU0 := c3H17CapUp_nonneg d ((z : ℚ) / 2 ^ (h + d))
    have hG : (if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z)
        else 1) ≤ 1 := by
      split_ifs
      · exact c3H17Node_le_one _ _
      · rfl
    have : c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
        (if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z) else 1) ≤ 1 := by
      rcases le_or_gt 0 (if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z)
        else 1) with h0 | h0
      · nlinarith
      · exact le_trans (mul_nonpos_of_nonneg_of_nonpos hU0 h0.le) zero_le_one
    have : (0 : ℚ) ≤ 2 ^ (-d) := by positivity
    exact mul_nonneg (mul_nonneg hw this) (by linarith)
  have : ⌈(10 ^ 8 : ℚ) * (1 - ∑ d ∈ Finset.Icc (2 : ℤ) (17 - h),
      ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) *
        (1 - c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
          if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z) else 1))⌉ ≤
      10 ^ 8 := by
    rw [Int.ceil_le]
    push_cast
    nlinarith
  exact_mod_cast this
termination_by (15 - h).toNat
decreasing_by
  simp only [Finset.mem_Icc] at *
  omega

/-- The rounded future costs are nonnegative. -/
theorem c3H17Node_nonneg (h z : ℤ) : 0 ≤ c3H17Node h z := by
  rcases le_or_gt 15 h with hh | hh
  · rw [c3H17Node_of_le hh]
    exact zero_le_one
  rw [c3H17Node_of_lt hh]
  refine div_nonneg ?_ (by norm_num)
  have hsum : ∑ d ∈ Finset.Icc (2 : ℤ) (17 - h),
      ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) *
        (1 - c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
          if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z) else 1) ≤
      ∑ d ∈ Finset.Icc (2 : ℤ) (17 - h), ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have hw : (0 : ℚ) ≤ ((d : ℚ) - 1) * 2 ^ (-d) := by
      have : (2 : ℚ) ≤ d := by exact_mod_cast hd.1
      have : (0 : ℚ) ≤ (d : ℚ) - 1 := by linarith
      positivity
    have hG : 0 ≤ (if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z)
        else 1) := by
      split_ifs
      · exact c3H17Node_nonneg _ _
      · exact zero_le_one
    have := mul_nonneg (c3H17CapUp_nonneg d ((z : ℚ) / 2 ^ (h + d))) hG
    exact mul_le_of_le_one_right hw (by linarith)
  have := sum_pascal_le_one (17 - h)
  have : (0 : ℤ) ≤ ⌈(10 ^ 8 : ℚ) * (1 - ∑ d ∈ Finset.Icc (2 : ℤ) (17 - h),
      ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) *
        (1 - c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
          if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z) else 1))⌉ := by
    exact Int.ceil_nonneg (mul_nonneg (by norm_num) (by linarith))
  exact_mod_cast this
termination_by (15 - h).toNat
decreasing_by
  simp only [Finset.mem_Icc] at *
  omega

end CollatzPosDens
