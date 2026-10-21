/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17S
public import CollatzPosDens.Case3.C3H17Delta
public import CollatzPosDens.Case3.C3H17ValuesDataRowSpecA
public import CollatzPosDens.Case3.C3H17ValuesDataRowSpecB

/-!
# The aggregate deficits and ranges of the four phase classes

For every `s ∈ {1, 3, 5, 7}` the aggregate deficit and the aggregate range of the phase class of
`s` are the exact rationals
`(Sʰ_s, Dʰ_s) = (149160843578876007/53687091200000000, 90751350494755481/21474836480000000)` for
`s ∈ {1, 7}` and
`(Sʰ_s, Dʰ_s) = (319022353342658719/107374182400000000, 258514465939645767/53687091200000000)` for
`s ∈ {3, 5}`.

This is an exact finite computation. All arguments of the grid majorants `Ū_c` that occur are
turns `n / 2^17`, at which the rounded cosine bounds are explicit multiples of `10^{-18}`; the
rounded future costs `cf⁺_h(z)` depend only on `z mod 2^17`; and the cost table
`ct_{c,o}(m)` depends only on `m mod 2^17`. The odd residues modulo `2^17` are the numbers
`± 3^J`, `J < 2^15`, and the orbit of `s` under multiplication by `9` is `3^{2k}`, `3^{2k+1}`,
`-3^{2k+15627}`, `-3^{2k+1198}` for `s = 1, 3, 5, 7`. The computation runs in these
coordinates:

* the cosine bounds at the points `2^v 3^J / 2^17` are tabulated and checked against the
  defining Taylor polynomial;
* the majorants `10^8 Ū_c(± 2^v 3^J / 2^17)` are computed from the tabulated cosine bounds, with
  exact ceiling square roots;
* the values `10^8 cf⁺_h(3^J)`, `1 ≤ h ≤ 14`, are tabulated and checked against their defining
  recursion, from level `14` down to level `1`;
* for each of the `135` rows `(c, o)` the table values along the orbits of `1` and `3` are
  computed, with their sums and the extreme values of their centred partial sums; the orbits of
  `7` and `5` are rotations of the orbits of `1` and `3`, so that their orbit means and ranges
  agree.

## Main results

* `CollatzPosDens.c3H17S_c3H17Delta_eq`: the values of `(Sʰ_s, Dʰ_s)`.

## Implementation notes

The packet values `1 - δ'_{c,o}` are those of the packet recursion of the narrow deficit, and
the Lipschitz constants `ℓ_c` and `𝖫_h` are explicit rationals. All integer computations are in
natural numbers; sums of many cosine bounds are computed as sums of numbers whose lanes of
`72` bits hold `256` cosine bounds each.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

namespace C3H17Values

/-- The orbit means and ranges of every row are the table values. -/
theorem rowMR_all {c o : ℕ} (hc2 : 2 ≤ c) (hc : c ≤ 16) (ho1 : 1 ≤ o) (hoc : o ≤ c) :
    RowMR c o := by
  interval_cases c
  · interval_cases o
    · exact rowMR_2_1
    · exact rowMR_2_2
  · interval_cases o
    · exact rowMR_3_1
    · exact rowMR_3_2
    · exact rowMR_3_3
  · interval_cases o
    · exact rowMR_4_1
    · exact rowMR_4_2
    · exact rowMR_4_3
    · exact rowMR_4_4
  · interval_cases o
    · exact rowMR_5_1
    · exact rowMR_5_2
    · exact rowMR_5_3
    · exact rowMR_5_4
    · exact rowMR_5_5
  · interval_cases o
    · exact rowMR_6_1
    · exact rowMR_6_2
    · exact rowMR_6_3
    · exact rowMR_6_4
    · exact rowMR_6_5
    · exact rowMR_6_6
  · interval_cases o
    · exact rowMR_7_1
    · exact rowMR_7_2
    · exact rowMR_7_3
    · exact rowMR_7_4
    · exact rowMR_7_5
    · exact rowMR_7_6
    · exact rowMR_7_7
  · interval_cases o
    · exact rowMR_8_1
    · exact rowMR_8_2
    · exact rowMR_8_3
    · exact rowMR_8_4
    · exact rowMR_8_5
    · exact rowMR_8_6
    · exact rowMR_8_7
    · exact rowMR_8_8
  · interval_cases o
    · exact rowMR_9_1
    · exact rowMR_9_2
    · exact rowMR_9_3
    · exact rowMR_9_4
    · exact rowMR_9_5
    · exact rowMR_9_6
    · exact rowMR_9_7
    · exact rowMR_9_8
    · exact rowMR_9_9
  · interval_cases o
    · exact rowMR_10_1
    · exact rowMR_10_2
    · exact rowMR_10_3
    · exact rowMR_10_4
    · exact rowMR_10_5
    · exact rowMR_10_6
    · exact rowMR_10_7
    · exact rowMR_10_8
    · exact rowMR_10_9
    · exact rowMR_10_10
  · interval_cases o
    · exact rowMR_11_1
    · exact rowMR_11_2
    · exact rowMR_11_3
    · exact rowMR_11_4
    · exact rowMR_11_5
    · exact rowMR_11_6
    · exact rowMR_11_7
    · exact rowMR_11_8
    · exact rowMR_11_9
    · exact rowMR_11_10
    · exact rowMR_11_11
  · interval_cases o
    · exact rowMR_12_1
    · exact rowMR_12_2
    · exact rowMR_12_3
    · exact rowMR_12_4
    · exact rowMR_12_5
    · exact rowMR_12_6
    · exact rowMR_12_7
    · exact rowMR_12_8
    · exact rowMR_12_9
    · exact rowMR_12_10
    · exact rowMR_12_11
    · exact rowMR_12_12
  · interval_cases o
    · exact rowMR_13_1
    · exact rowMR_13_2
    · exact rowMR_13_3
    · exact rowMR_13_4
    · exact rowMR_13_5
    · exact rowMR_13_6
    · exact rowMR_13_7
    · exact rowMR_13_8
    · exact rowMR_13_9
    · exact rowMR_13_10
    · exact rowMR_13_11
    · exact rowMR_13_12
    · exact rowMR_13_13
  · interval_cases o
    · exact rowMR_14_1
    · exact rowMR_14_2
    · exact rowMR_14_3
    · exact rowMR_14_4
    · exact rowMR_14_5
    · exact rowMR_14_6
    · exact rowMR_14_7
    · exact rowMR_14_8
    · exact rowMR_14_9
    · exact rowMR_14_10
    · exact rowMR_14_11
    · exact rowMR_14_12
    · exact rowMR_14_13
    · exact rowMR_14_14
  · interval_cases o
    · exact rowMR_15_1
    · exact rowMR_15_2
    · exact rowMR_15_3
    · exact rowMR_15_4
    · exact rowMR_15_5
    · exact rowMR_15_6
    · exact rowMR_15_7
    · exact rowMR_15_8
    · exact rowMR_15_9
    · exact rowMR_15_10
    · exact rowMR_15_11
    · exact rowMR_15_12
    · exact rowMR_15_13
    · exact rowMR_15_14
    · exact rowMR_15_15
  · interval_cases o
    · exact rowMR_16_1
    · exact rowMR_16_2
    · exact rowMR_16_3
    · exact rowMR_16_4
    · exact rowMR_16_5
    · exact rowMR_16_6
    · exact rowMR_16_7
    · exact rowMR_16_8
    · exact rowMR_16_9
    · exact rowMR_16_10
    · exact rowMR_16_11
    · exact rowMR_16_12
    · exact rowMR_16_13
    · exact rowMR_16_14
    · exact rowMR_16_15
    · exact rowMR_16_16

/-- The aggregate deficit as the weighted sum of the table means. -/
theorem c3H17S_eq_sum {s : ℤ} (hs : s ∈ ({1, 3, 5, 7} : Finset ℤ)) :
    c3H17S s = ∑ c ∈ Icc (2 : ℤ) 16, ((c : ℚ) - 1) * (2 : ℚ) ^ (-c) *
      ∑ o ∈ Icc (1 : ℤ) c, (1 - meanVal s c o) := by
  unfold c3H17S
  refine sum_congr rfl fun c hc => congrArg _ (sum_congr rfl fun o ho => ?_)
  rw [mem_Icc] at hc ho
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, c = n := ⟨c.toNat, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, o = m := ⟨o.toNat, by omega⟩
  rw [(rowMR_all (by omega) (by omega) (by omega) (by omega) s hs).1]

/-- The aggregate range as the weighted sum of the table ranges. -/
theorem c3H17Delta_eq_sum {s : ℤ} (hs : s ∈ ({1, 3, 5, 7} : Finset ℤ)) :
    c3H17Delta s = ∑ c ∈ Icc (2 : ℤ) 16, ((c : ℚ) - 1) * (2 : ℚ) ^ (-c) *
      ∑ o ∈ Icc (1 : ℤ) c, rangeVal s c o := by
  unfold c3H17Delta
  refine sum_congr rfl fun c hc => congrArg _ (sum_congr rfl fun o ho => ?_)
  rw [mem_Icc] at hc ho
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, c = n := ⟨c.toNat, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, o = m := ⟨o.toNat, by omega⟩
  rw [(rowMR_all (by omega) (by omega) (by omega) (by omega) s hs).2]

/-- An entry of the table is the default entry or the entry of a row of the table with the
same `c`. -/
theorem rowEntry_eq_or_mem (c o : ℕ) : rowEntry c o = (1, 0, 0, 0, 0, 0, 0) ∨
    ∃ e ∈ rowTab, e.1 = c ∧ e.2.2 = rowEntry c o := by
  unfold rowEntry
  cases h : rowTab.find? (fun e => e.1 == c && e.2.1 == o) with
  | none => exact Or.inl rfl
  | some e =>
    have := List.find?_some h
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact Or.inr ⟨e, List.mem_of_find?_eq_some h, this.1, rfl⟩

/-- The denominator `2 ^ 14 · 10 ^ 8 · p_d` of the table values of the row `(c, o)`. -/
def rowDen (c o : ℤ) : ℕ := 2 ^ 14 * (10 ^ 8 * (rowEntry c.toNat o.toNat).1)

/-- The denominators `2 ^ c · 2 ^ 14 · 10 ^ 8 · p_d` of the rows all divide one common
denominator. -/
theorem rowDen_dvd : ∀ c ∈ Icc (2 : ℤ) 16, ∀ o ∈ Icc (1 : ℤ) c,
    2 ^ c.toNat * rowDen c o ∣ 2476375063658496000000000000000 := by
  have htab : ∀ e ∈ rowTab, 2 ^ e.1 * (2 ^ 14 * (10 ^ 8 * e.2.2.1)) ∣
      2476375063658496000000000000000 := by
    decide +kernel
  intro c hc o _
  rw [rowDen]
  rcases rowEntry_eq_or_mem c.toNat o.toNat with h | ⟨e, he, hce, h⟩
  · rw [h]
    exact (Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 (by rw [mem_Icc] at hc; omega)) _).trans
      (by norm_num : 2 ^ 16 * (2 ^ 14 * (10 ^ 8 * 1)) ∣ 2476375063658496000000000000000)
  · rw [← h, ← hce]
    exact htab e he

/-- The weight `D / (2 ^ c · 2 ^ 14 · 10 ^ 8 · p_d)` of the row `(c, o)` over the common
denominator `D` of `rowDen_dvd`. -/
def rowWt (c o : ℤ) : ℕ := 2476375063658496000000000000000 / (2 ^ c.toNat * rowDen c o)

/-- The numerators over the common denominator of `rowDen_dvd` of the four weighted sums of the
table values. One kernel evaluation reads every row once for all four. -/
theorem rowSums :
    (∑ c ∈ Icc (2 : ℤ) 16, ∑ o ∈ Icc (1 : ℤ) c,
      (c - 1) * ((rowDen c o : ℤ) - (rowEntry c.toNat o.toNat).2.1) * rowWt c o =
        6880205003786721008962560000000) ∧
    (∑ c ∈ Icc (2 : ℤ) 16, ∑ o ∈ Icc (1 : ℤ) c,
      (c - 1) * ((rowDen c o : ℤ) - (rowEntry c.toNat o.toNat).2.2.2.2.1) * rowWt c o =
        7357625296035871742645760000000) ∧
    (∑ c ∈ Icc (2 : ℤ) 16, ∑ o ∈ Icc (1 : ℤ) c,
      (c - 1) * (((rowEntry c.toNat o.toNat).2.2.1 : ℤ) -
        (rowEntry c.toNat o.toNat).2.2.2.1) * rowWt c o =
        10465010132572827242611200000000) ∧
    (∑ c ∈ Icc (2 : ℤ) 16, ∑ o ∈ Icc (1 : ℤ) c,
      (c - 1) * (((rowEntry c.toNat o.toNat).2.2.2.2.2.1 : ℤ) -
        (rowEntry c.toNat o.toNat).2.2.2.2.2.2) * rowWt c o =
        11924258937089375820303360000000) := by
  decide +kernel

/-- A weighted double sum over the rows with summands `a c o / b c o` is one integer over a
common multiple `D` of the denominators `2 ^ c · b c o`. -/
theorem sum_rows_eq_div (f : ℤ → ℤ → ℚ) (a : ℤ → ℤ → ℤ) (b : ℤ → ℤ → ℕ) (D : ℕ) (hD : D ≠ 0)
    (hdiv : ∀ c ∈ Icc (2 : ℤ) 16, ∀ o ∈ Icc (1 : ℤ) c, 2 ^ c.toNat * b c o ∣ D)
    (hf : ∀ c o, b c o ≠ 0 → f c o = a c o / (b c o : ℚ)) (N : ℤ)
    (hN : ∑ c ∈ Icc (2 : ℤ) 16, ∑ o ∈ Icc (1 : ℤ) c,
      (c - 1) * a c o * ((D / (2 ^ c.toNat * b c o) : ℕ) : ℤ) = N) :
    ∑ c ∈ Icc (2 : ℤ) 16, ((c : ℚ) - 1) * (2 : ℚ) ^ (-c) * ∑ o ∈ Icc (1 : ℤ) c, f c o =
      (N : ℚ) / D := by
  rw [← hN, Int.cast_sum, Finset.sum_div]
  refine sum_congr rfl fun c hc => ?_
  rw [Int.cast_sum, Finset.sum_div, Finset.mul_sum]
  refine sum_congr rfl fun o ho => ?_
  obtain ⟨k, hk⟩ := hdiv c hc o ho
  have hc0 : 0 ≤ c := by rw [mem_Icc] at hc; omega
  have hb : b c o ≠ 0 := by rintro h; rw [h, mul_zero, zero_mul] at hk; exact hD hk
  have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact hD hk
  have h2 : 2 ^ c.toNat * b c o ≠ 0 := mul_ne_zero (pow_ne_zero _ two_ne_zero) hb
  rw [hf c o hb, hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h2)]
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, c = n := ⟨c.toNat, by omega⟩
  rw [Int.toNat_natCast, zpow_neg, zpow_natCast]
  push_cast
  rw [mul_div_mul_right _ _ (Nat.cast_ne_zero.2 hk0)]
  ring

/-- The weighted sum of the table deficits `1 - meanVal 1 c o` equals
`149160843578876007 / 53687091200000000`. -/
theorem sum_meanVal_one : ∑ c ∈ Icc (2 : ℤ) 16, ((c : ℚ) - 1) * (2 : ℚ) ^ (-c) *
    ∑ o ∈ Icc (1 : ℤ) c, (1 - meanVal 1 c o) = 149160843578876007 / 53687091200000000 := by
  refine (sum_rows_eq_div (fun c o => 1 - meanVal 1 c o)
    (fun c o => (rowDen c o : ℤ) - (rowEntry c.toNat o.toNat).2.1) rowDen _
    (by norm_num) rowDen_dvd ?_ _ rowSums.1).trans (by norm_num)
  intro c o hb
  rw [meanVal, ite_eq_left (by decide), Int.cast_sub, Int.cast_natCast, Int.cast_natCast, sub_div,
    div_self (Nat.cast_ne_zero.2 hb), rowDen]
  push_cast
  rfl

/-- The weighted sum of the table deficits `1 - meanVal 3 c o` equals
`319022353342658719 / 107374182400000000`. -/
theorem sum_meanVal_three : ∑ c ∈ Icc (2 : ℤ) 16, ((c : ℚ) - 1) * (2 : ℚ) ^ (-c) *
    ∑ o ∈ Icc (1 : ℤ) c, (1 - meanVal 3 c o) = 319022353342658719 / 107374182400000000 := by
  refine (sum_rows_eq_div (fun c o => 1 - meanVal 3 c o)
    (fun c o => (rowDen c o : ℤ) - (rowEntry c.toNat o.toNat).2.2.2.2.1) rowDen _
    (by norm_num) rowDen_dvd ?_ _ rowSums.2.1).trans (by norm_num)
  intro c o hb
  rw [meanVal, ite_eq_right (by decide), Int.cast_sub, Int.cast_natCast, Int.cast_natCast, sub_div,
    div_self (Nat.cast_ne_zero.2 hb), rowDen]
  push_cast
  rfl

/-- The weighted sum of the table ranges `rangeVal 1 c o` equals
`90751350494755481 / 21474836480000000`. -/
theorem sum_rangeVal_one : ∑ c ∈ Icc (2 : ℤ) 16, ((c : ℚ) - 1) * (2 : ℚ) ^ (-c) *
    ∑ o ∈ Icc (1 : ℤ) c, rangeVal 1 c o = 90751350494755481 / 21474836480000000 := by
  refine (sum_rows_eq_div (fun c o => rangeVal 1 c o)
    (fun c o => ((rowEntry c.toNat o.toNat).2.2.1 : ℤ) -
      (rowEntry c.toNat o.toNat).2.2.2.1) rowDen _
    (by norm_num) rowDen_dvd ?_ _ rowSums.2.2.1).trans (by norm_num)
  intro c o hb
  rw [rangeVal, ite_eq_left (by decide), Int.cast_sub, Int.cast_natCast, Int.cast_natCast, rowDen]
  push_cast
  rfl

/-- The weighted sum of the table ranges `rangeVal 3 c o` equals
`258514465939645767 / 53687091200000000`. -/
theorem sum_rangeVal_three : ∑ c ∈ Icc (2 : ℤ) 16, ((c : ℚ) - 1) * (2 : ℚ) ^ (-c) *
    ∑ o ∈ Icc (1 : ℤ) c, rangeVal 3 c o = 258514465939645767 / 53687091200000000 := by
  refine (sum_rows_eq_div (fun c o => rangeVal 3 c o)
    (fun c o => ((rowEntry c.toNat o.toNat).2.2.2.2.2.1 : ℤ) -
      (rowEntry c.toNat o.toNat).2.2.2.2.2.2) rowDen _
    (by norm_num) rowDen_dvd ?_ _ rowSums.2.2.2).trans (by norm_num)
  intro c o hb
  rw [rangeVal, ite_eq_right (by decide), Int.cast_sub, Int.cast_natCast, Int.cast_natCast, rowDen]
  push_cast
  rfl

end C3H17Values

open C3H17Values in
/-- For `s ∈ {1, 3, 5, 7}`, the aggregate deficit and range `(Sʰ_s, Dʰ_s)` are
`(149160843578876007/53687091200000000, 90751350494755481/21474836480000000)` if `s ∈ {1, 7}`
and `(319022353342658719/107374182400000000, 258514465939645767/53687091200000000)` if
`s ∈ {3, 5}`. -/
@[collatz_pos_dens "lem_c3_h17_values"]
theorem c3H17S_c3H17Delta_eq {s : ℤ} (hs : s ∈ ({1, 3, 5, 7} : Finset ℤ)) :
    (c3H17S s, c3H17Delta s) =
      if s ∈ ({1, 7} : Finset ℤ) then
        (149160843578876007 / 53687091200000000, 90751350494755481 / 21474836480000000)
      else (319022353342658719 / 107374182400000000, 258514465939645767 / 53687091200000000) := by
  rw [c3H17S_eq_sum hs, c3H17Delta_eq_sum hs]
  simp only [mem_insert, mem_singleton] at hs ⊢
  rcases hs with rfl | rfl | rfl | rfl
  · rw [ite_eq_left (by norm_num), sum_meanVal_one, sum_rangeVal_one]
  · rw [ite_eq_right (by norm_num), sum_meanVal_three, sum_rangeVal_three]
  · rw [ite_eq_right (by norm_num)]
    simp only [meanVal_five, rangeVal_five]
    rw [sum_meanVal_three, sum_rangeVal_three]
  · rw [ite_eq_left (by norm_num)]
    simp only [meanVal_seven, rangeVal_seven]
    rw [sum_meanVal_one, sum_rangeVal_one]

end CollatzPosDens
