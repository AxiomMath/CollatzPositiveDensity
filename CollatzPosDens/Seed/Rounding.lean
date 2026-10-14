/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Seed.RoundedOffset

/-!
# Rounded offsets bracket the offset

For a word `v` and an integer precision `p`, the rounded offset `rd_p(v)` is obtained from the
offset `off(v) = ∑ᵢ 3^{i-1} 2^{-(a₁+⋯+aᵢ)}` by rounding each term up to the grid `2^{-p} ℤ`.
Since `x ≤ ⌈x⌉ < x + 1` for each of the `|v|` terms, the rounded offset overestimates the offset
by less than `|v| 2^{-p}`:
$$\mathrm{rd}_p(v) - |v|\,2^{-p} \le \mathrm{off}(v) \le \mathrm{rd}_p(v).$$

## Main results

* `CollatzPosDens.roundedOffset_sub_le_off_le`: the two-sided bracket above.
* `CollatzPosDens.off_le_roundedOffset`: `off(v) ≤ rd_p(v)`.
* `CollatzPosDens.roundedOffset_sub_le_off`: `rd_p(v) - |v| 2^{-p} ≤ off(v)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The rounded offset minus the offset is `2^{-p}` times the sum of the rounding errors
`⌈x_j⌉ - x_j` of the scaled terms. -/
private lemma roundedOffset_sub_off_eq (p : ℤ) (v : Word) :
    roundedOffset p v - off v = (2 : ℚ) ^ (-p) * ∑ j ∈ Finset.range v.length,
      (((⌈(2 : ℚ) ^ p * 3 ^ j * ((2 : ℚ) ^ Word.valSum (v.take (j + 1)))⁻¹⌉ : ℤ)
        : ℚ) - (2 : ℚ) ^ p * 3 ^ j * ((2 : ℚ) ^ Word.valSum (v.take (j + 1)))⁻¹) := by
  rw [roundedOffset, off_eq_sum, Finset.sum_sub_distrib, mul_sub]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← zpow_add₀ two_ne_zero, neg_add_cancel, zpow_zero, one_mul]

/-- The offset is at most the rounded offset. -/
theorem off_le_roundedOffset (p : ℤ) (v : Word) : off v ≤ roundedOffset p v := by
  rw [← sub_nonneg, roundedOffset_sub_off_eq]
  exact mul_nonneg (zpow_nonneg zero_le_two _)
    (Finset.sum_nonneg fun j _ => sub_nonneg.2 (Int.le_ceil _))

/-- The rounded offset exceeds the offset by at most `|v| 2^{-p}`. -/
theorem roundedOffset_sub_le_off (p : ℤ) (v : Word) :
    roundedOffset p v - v.length * (2 : ℚ) ^ (-p) ≤ off v := by
  rw [sub_le_comm, roundedOffset_sub_off_eq, mul_comm (v.length : ℚ)]
  refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg zero_le_two _)
  calc _ ≤ ∑ _j ∈ Finset.range v.length, (1 : ℚ) :=
        Finset.sum_le_sum fun _ _ => sub_le_iff_le_add'.2 (Int.ceil_lt_add_one _).le
    _ = v.length := by simp

/-- **Rounding lemma.** For every word `v` and every integer `p`,
`rd_p(v) - |v| 2^{-p} ≤ off(v) ≤ rd_p(v)`. -/
@[collatz_pos_dens "lem_s05_rounding"]
theorem roundedOffset_sub_le_off_le (p : ℤ) (v : Word) :
    roundedOffset p v - v.length * (2 : ℚ) ^ (-p) ≤ off v ∧ off v ≤ roundedOffset p v :=
  ⟨roundedOffset_sub_le_off p v, off_le_roundedOffset p v⟩

end CollatzPosDens
