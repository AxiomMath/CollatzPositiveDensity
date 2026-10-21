/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.StoppingTrace.TrPacketDeficit

/-!
# The root packet correction

For `ω, k ∈ ℕ`, the root packet correction is the real number
`T^{root}_{ω,k} := ∑_{c = max {k, ω, 2} + 1}^{16} ϖ(c) δ^{pk}_{c,c-ω}`, the sum over the root
letters `c` above the cutoff `k`, above the offset `ω` and above `2` of the Pascal weight
`ϖ = CollatzPosDens.varpi` times the packet deficit `δ^{pk} = CollatzPosDens.trPacketDeficit`;
the empty sum is `0`. Since `ϖ(c) = (c - 1) 2^{-c}` for `c ≥ 2` and
`(c - 1) δ^{pk}_{c,o} = F_{c,o}(0)`, where `F = CollatzPosDens.trPacketValue` is the packet value,
each term is the rational number `2^{-c} F_{c,c-ω}(0)`, so the correction is an explicit rational
number.

## Main definitions

* `CollatzPosDens.trTailGain ω k`: the root packet correction `T^{root}_{ω,k}`.

## Main results

* `CollatzPosDens.trTailGain_eq_ratCast`: `T^{root}_{ω,k}` is the rational number
  `∑_{c = max {k, ω, 2} + 1}^{16} 2^{-c} F_{c,c-ω}(0)`.
* `CollatzPosDens.trTailGain_eq_zero`: `T^{root}_{ω,k} = 0` when `16 ≤ k` or `16 ≤ ω`.
* `CollatzPosDens.trTailGain_zero_twelve`: `T^{root}_{0,12} = 1197 / 13107200`.
* `CollatzPosDens.trTailGain_one_eight`, `trTailGain_six_eight`, `trTailGain_nine_eight`,
  `trTailGain_thirteen_eight`, `trTailGain_sixteen_eight`: the values of `T^{root}_{ω,8}` for
  `ω ∈ {1, 6, 9, 13, 16}`.

## References

* [Mazur, *Collatz positive density*], §9.7.
-/

@[expose] public section

namespace CollatzPosDens

/-- The root packet correction
`T^{root}_{ω,k} := ∑_{c = max {k, ω, 2} + 1}^{16} ϖ(c) δ^{pk}_{c,c-ω}`, with `ϖ` the Pascal weight
`CollatzPosDens.varpi` and `δ^{pk}` the packet deficit `CollatzPosDens.trPacketDeficit`. The
subtraction `c - ω` is that of `ℕ`; it is exact since `ω < c` on the range of summation. -/
@[collatz_pos_dens "def_tr_tail_gain"]
noncomputable def trTailGain (ω k : ℕ) : ℝ :=
  ∑ c ∈ Finset.Icc (max k (max ω 2) + 1) 16, varpi c * (trPacketDeficit c (c - ω) : ℝ)

/-- The root packet correction is the rational number
`∑_{c = max {k, ω, 2} + 1}^{16} 2^{-c} F_{c,c-ω}(0)`. -/
theorem trTailGain_eq_ratCast (ω k : ℕ) :
    trTailGain ω k = ((∑ c ∈ Finset.Icc (max k (max ω 2) + 1) 16,
      trPacketValue c (c - ω) 0 / 2 ^ c : ℚ) : ℝ) := by
  rw [trTailGain, Rat.cast_sum]
  refine Finset.sum_congr rfl fun c hc => ?_
  have h2 : 2 ≤ c := by
    have := (Finset.mem_Icc.1 hc).1
    omega
  have h1 : c ≠ 1 := by omega
  rw [varpi_of_two_le (by exact_mod_cast h2), ← sub_one_mul_trPacketDeficit h1, zpow_neg,
    zpow_natCast]
  push_cast
  ring

/-- The root packet correction vanishes when `16 ≤ k` or `16 ≤ ω`: the sum is then empty. -/
theorem trTailGain_eq_zero {ω k : ℕ} (h : 16 ≤ k ∨ 16 ≤ ω) : trTailGain ω k = 0 := by
  rw [trTailGain, Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-- The sum `∑_{c=a}^{16} 2^{-c} F_{c,c-ω}(0)` through the natural-number evaluator
`CollatzPosDens.pvN` of the packet values, scaled by `10^6 · 2^{16}`. -/
theorem sum_trPacketValue_div_eq_pvN (ω a : ℕ) :
    (∑ c ∈ Finset.Icc a 16, trPacketValue c (c - ω) 0 / 2 ^ c : ℚ) =
      ((∑ c ∈ Finset.Icc a 16, pvN c (c - ω) * 2 ^ (16 - c) : ℕ) : ℚ) / (10 ^ 6 * 2 ^ 16) := by
  rw [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  have h2 : (2 : ℚ) ^ 16 = 2 ^ (16 - c) * 2 ^ c := by
    rw [← pow_add, Nat.sub_add_cancel (Finset.mem_Icc.1 hc).2]
  rw [trPacketValue_eq_pvN, h2]
  push_cast
  field_simp

/-- `T^{root}_{0,12} = ∑_{c=13}^{16} ϖ(c) δ^{pk}_{c,c} = 1197 / 13107200`. -/
theorem trTailGain_zero_twelve : trTailGain 0 12 = 1197 / 13107200 := by
  rw [trTailGain_eq_ratCast, sum_trPacketValue_div_eq_pvN,
    show ∑ c ∈ Finset.Icc (max 12 (max 0 2) + 1) 16, pvN c (c - 0) * 2 ^ (16 - c) =
      5985000 by decide +kernel]
  norm_num

/-- `T^{root}_{1,8} = 4595457 / 1310720000`. -/
theorem trTailGain_one_eight : trTailGain 1 8 = 4595457 / 1310720000 := by
  rw [trTailGain_eq_ratCast, sum_trPacketValue_div_eq_pvN,
    show ∑ c ∈ Finset.Icc (max 8 (max 1 2) + 1) 16, pvN c (c - 1) * 2 ^ (16 - c) =
      229772850 by decide +kernel]
  norm_num

/-- `T^{root}_{6,8} = 13575489 / 1638400000`. -/
theorem trTailGain_six_eight : trTailGain 6 8 = 13575489 / 1638400000 := by
  rw [trTailGain_eq_ratCast, sum_trPacketValue_div_eq_pvN,
    show ∑ c ∈ Finset.Icc (max 8 (max 6 2) + 1) 16, pvN c (c - 6) * 2 ^ (16 - c) =
      543019560 by decide +kernel]
  norm_num

/-- `T^{root}_{9,8} = 800801 / 204800000`. -/
theorem trTailGain_nine_eight : trTailGain 9 8 = 800801 / 204800000 := by
  rw [trTailGain_eq_ratCast, sum_trPacketValue_div_eq_pvN,
    show ∑ c ∈ Finset.Icc (max 8 (max 9 2) + 1) 16, pvN c (c - 9) * 2 ^ (16 - c) =
      256256320 by decide +kernel]
  norm_num

/-- `T^{root}_{13,8} = 697807 / 3276800000`. -/
theorem trTailGain_thirteen_eight : trTailGain 13 8 = 697807 / 3276800000 := by
  rw [trTailGain_eq_ratCast, sum_trPacketValue_div_eq_pvN,
    show ∑ c ∈ Finset.Icc (max 8 (max 13 2) + 1) 16, pvN c (c - 13) * 2 ^ (16 - c) =
      13956140 by decide +kernel]
  norm_num

/-- `T^{root}_{16,8} = 0`. -/
theorem trTailGain_sixteen_eight : trTailGain 16 8 = 0 :=
  trTailGain_eq_zero (Or.inr le_rfl)

end CollatzPosDens
