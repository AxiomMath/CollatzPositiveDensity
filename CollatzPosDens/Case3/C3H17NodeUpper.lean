/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17Node
public import CollatzPosDens.Case3.C3H17CapUpBound
public import CollatzPosDens.Case3.C3H17CostRange

/-!
# The rounded future costs are majorants

For all integers `h` and `z`, the future cost `cf_h(z)` (`CollatzPosDens.c3H17Cost`) is at most
the rounded future cost `cf⁺_h(z)` (`CollatzPosDens.c3H17Node`).

The proof is by downward induction on `h`. For `h ≥ 15` both sides are `1`. For `h ≤ 14`, write
`cf_h(z) = 1 - ∑_{d=2}^{17-h} ϖ(d) [1 - Φ^cap_d(z / 2^{h+d}) R_d]`. Each product
`Φ^cap_d(z / 2^{h+d}) R_d` of nonnegative factors is at most `Ū_d(z / 2^{h+d}) G_d`, since
`Φ^cap_d ≤ Ū_d` (`CollatzPosDens.trCapFactor_le_c3H17CapUp`), `Ū_d ≥ 0`, and either
`0 ≤ R_d = cf_{h+d}(9z) ≤ cf⁺_{h+d}(9z) = G_d` (by `CollatzPosDens.c3H17Cost_mem_Icc` and the
induction hypothesis) or `R_d = G_d = 1`. As `ϖ ≥ 0`, `cf_h(z)` is at most the number inside the
ceiling defining `cf⁺_h(z)`, hence at most `cf⁺_h(z)`.

## Main results

* `CollatzPosDens.c3H17Cost_le_c3H17Node`: `cf_h(z) ≤ cf⁺_h(z)`.

## Implementation notes

The bound is stated for every integer `h` rather than only for `h ≥ 1`; the proof is the same.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **The rounded future costs are majorants.** For all integers `h` and `z`,
`cf_h(z) ≤ cf⁺_h(z)`. -/
@[collatz_pos_dens "lem_c3_h17_node_upper"]
theorem c3H17Cost_le_c3H17Node (h z : ℤ) : c3H17Cost h z ≤ c3H17Node h z := by
  induction hn : (15 - h).toNat using Nat.strong_induction_on generalizing h z with
  | _ n ih =>
  rcases le_or_gt 15 h with hh | hh
  · rw [c3H17Cost_of_le hh, c3H17Node_of_le hh, Rat.cast_one]
  rw [c3H17Cost_of_lt hh, c3H17Node_of_lt hh]
  set x : ℚ := 1 - ∑ d ∈ Finset.Icc (2 : ℤ) (17 - h),
      ((d : ℚ) - 1) * (2 : ℚ) ^ (-d) *
        (1 - c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) *
          if d ∉ ({4, 5} : Finset ℤ) ∧ h + d ≤ 15 then c3H17Node (h + d) (9 * z) else 1) with hx
  have hceil : x ≤ (⌈(10 ^ 8 : ℚ) * x⌉ : ℚ) / 10 ^ 8 := by
    rw [le_div_iff₀ (by norm_num), mul_comm]
    exact Int.le_ceil _
  refine le_trans ?_ (Rat.cast_le.mpr hceil)
  rw [hx, Rat.cast_sub, Rat.cast_one, c3H17Node_sum_cast]
  refine sub_le_sub_left (Finset.sum_le_sum fun d hd => ?_) 1
  have hds := Finset.mem_Icc.mp hd
  refine mul_le_mul_of_nonneg_left (sub_le_sub_left ?_ 1) (varpi_nonneg d)
  have hθ : ((((z : ℚ) / 2 ^ (h + d) : ℚ)) : ℝ) = (z : ℝ) / (2 : ℝ) ^ (h + d) := by
    push_cast
    rfl
  have hΦ := trCapFactor_le_c3H17CapUp d ((z : ℚ) / 2 ^ (h + d))
  have hΦ0 := (trCapFactor_mem_Icc d ((z : ℚ) / 2 ^ (h + d) : ℚ)).1
  have hU0 : (0 : ℝ) ≤ (c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) : ℝ) := by
    exact_mod_cast c3H17CapUp_nonneg d _
  rw [hθ] at hΦ hΦ0
  split_ifs with hc
  · have hR0 := (c3H17Cost_mem_Icc (h + d) (9 * (z : ℝ))).1
    have hRG : c3H17Cost (h + d) (9 * (z : ℝ)) ≤ (c3H17Node (h + d) (9 * z) : ℝ) := by
      have := ih (15 - (h + d)).toNat (by omega) (h + d) (9 * z) rfl
      push_cast at this
      exact this
    calc trCapFactor d ((z : ℝ) / 2 ^ (h + d)) * c3H17Cost (h + d) (9 * (z : ℝ))
        ≤ (c3H17CapUp d ((z : ℚ) / 2 ^ (h + d)) : ℝ) * c3H17Cost (h + d) (9 * (z : ℝ)) :=
          mul_le_mul_of_nonneg_right hΦ hR0
      _ ≤ _ := mul_le_mul_of_nonneg_left hRG hU0
  · simpa using hΦ

end CollatzPosDens
