/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrTailGain
public import CollatzPosDens.StoppingTrace.TrTreeCertificateData1
public import CollatzPosDens.StoppingTrace.TrTreeCertificateData2
public import CollatzPosDens.StoppingTrace.TrTreeCertificateData3

/-!
# The gap-zero certificate

For every odd integer `m` with `0 < m < 2^16` and every real `β` with `|β| ≤ 1/3`, there are
reals `a ≤ β ≤ b` in `[-1/3, 1/3]` such that
`F^{cut⁰, W}_{0,0}(m + β) - T^{root}_{0,12} < 77/100`, where `F` is the tree cost
`CollatzPosDens.trTreeCost`, `cut⁰` the gap-zero cutoff `CollatzPosDens.trZeroCutoff`,
`W = W^{0,12,14}_{m,a,b}` the white-test policy `CollatzPosDens.trWhitePolicy` and
`T^{root}_{0,12} = 1197/13107200` the root packet correction `CollatzPosDens.trTailGain`.

The proof is a finite exact computation. The odd integers are covered by residue classes
modulo `2^k`, `k ≤ 17`, and for each class the interval `[-1/3, 1/3]` of `β` is covered by
cells `[a, b]` obtained by bisection; for each cell the kernel checks that an explicit upper
bound for the tree cost on the cell is below `77/100 + T^{root}_{0,12}`
(`CollatzPosDens.TrTreeCertificate.cell_spec`). Each retained factor is bounded on the cell from
an approximate sum of units at the midpoint (`CollatzPosDens.trCapFactor_le_min_of_norm_sum_le`),
and the tree cost node by node (`CollatzPosDens.trTreeCost_le_of_node_bound`). The checker and
its soundness are in `CollatzPosDens.TrTreeCertificate.good_of_checkR`; the `211` accepted cells
of the `80` classes, of depth at most `6`, assemble into
`CollatzPosDens.TrTreeCertificate.good_one_one`. The least margin is about `2.26 · 10^{-4}` below
`77/100 + T^{root}_{0,12}`.

## Main results

* `CollatzPosDens.trTreeCost_sub_trTailGain_lt`: the gap-zero certificate.

## References

* [Mazur, *Collatz positive density*], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

namespace TrTreeCertificate

/-- The certificate: every odd residue class modulo `2` is covered. -/
theorem good_one_one : Good 1 1 :=
  (Good.split (k := 1) (res := 1) rfl (by norm_num) (Good.split (k := 2) (res := 1) rfl (by
  norm_num) (Good.split (k := 3) (res := 1) rfl (by norm_num) (Good.split (k := 4) (res := 1)
  rfl (by norm_num) (Good.split (k := 5) (res := 1) rfl (by norm_num) (Good.split (k := 6) (res
  := 1) rfl (by norm_num) (Good.split (k := 7) (res := 1) rfl (by norm_num) (Good.split (k := 8)
  (res := 1) rfl (by norm_num) (Good.split (k := 9) (res := 1) rfl (by norm_num) (Good.split (k
  := 10) (res := 1) rfl (by norm_num) (Good.split (k := 11) (res := 1) rfl (by norm_num)
  (Good.split (k := 12) (res := 1) rfl (by norm_num) (Good.split (k := 13) (res := 1) rfl (by
  norm_num) (Good.split (k := 14) (res := 1) rfl (by norm_num) (Good.split (k := 15) (res := 1)
  rfl (by norm_num) good_16_1 good_16_32769) good_15_16385) good_14_8193) good_13_4097)
  (Good.split (k := 12) (res := 2049) rfl (by norm_num) good_13_2049 good_13_6145)) (Good.split
  (k := 11) (res := 1025) rfl (by norm_num) good_12_1025 good_12_3073)) good_10_513) good_9_257)
  good_8_129) good_7_65) good_6_33) (Good.split (k := 5) (res := 17) rfl (by norm_num) good_6_17
  (Good.split (k := 6) (res := 49) rfl (by norm_num) good_7_49 (Good.split (k := 7) (res := 113)
  rfl (by norm_num) (Good.split (k := 8) (res := 113) rfl (by norm_num) (Good.split (k := 9)
  (res := 113) rfl (by norm_num) (Good.split (k := 10) (res := 113) rfl (by norm_num)
  good_11_113 good_11_1137) good_10_625) good_9_369) good_8_241)))) good_4_9) good_3_5)
  (Good.split (k := 2) (res := 3) rfl (by norm_num) good_3_3 (Good.split (k := 3) (res := 7) rfl
  (by norm_num) good_4_7 (Good.split (k := 4) (res := 15) rfl (by norm_num) (Good.split (k := 5)
  (res := 15) rfl (by norm_num) (Good.split (k := 6) (res := 15) rfl (by norm_num) (Good.split
  (k := 7) (res := 15) rfl (by norm_num) good_8_15 (Good.split (k := 8) (res := 143) rfl (by
  norm_num) good_9_143 (Good.split (k := 9) (res := 399) rfl (by norm_num) good_10_399
  (Good.split (k := 10) (res := 911) rfl (by norm_num) good_11_911 good_11_1935)))) good_7_79)
  good_6_47) (Good.split (k := 5) (res := 31) rfl (by norm_num) good_6_31 (Good.split (k := 6)
  (res := 63) rfl (by norm_num) good_7_63 (Good.split (k := 7) (res := 127) rfl (by norm_num)
  good_8_127 (Good.split (k := 8) (res := 255) rfl (by norm_num) good_9_255 (Good.split (k := 9)
  (res := 511) rfl (by norm_num) good_10_511 (Good.split (k := 10) (res := 1023) rfl (by
  norm_num) (Good.split (k := 11) (res := 1023) rfl (by norm_num) good_12_1023 good_12_3071)
  (Good.split (k := 11) (res := 2047) rfl (by norm_num) (Good.split (k := 12) (res := 2047) rfl
  (by norm_num) good_13_2047 good_13_6143) (Good.split (k := 12) (res := 4095) rfl (by norm_num)
  good_13_4095 (Good.split (k := 13) (res := 8191) rfl (by norm_num) good_14_8191 (Good.split (k
  := 14) (res := 16383) rfl (by norm_num) good_15_16383 good_15_32767))))))))))))))

end TrTreeCertificate

open TrTreeCertificate in
/-- **The gap-zero certificate.** For every odd integer `m` with `0 < m < 2^16` and every real
`β` with `|β| ≤ 1/3`, there are reals `a, b` with `-1/3 ≤ a ≤ β ≤ b ≤ 1/3` such that
`F^{cut⁰, W^{0,12,14}_{m,a,b}}_{0,0}(m + β) - T^{root}_{0,12} < 77/100`. -/
@[collatz_pos_dens "lem_tr_tree_certificate"]
theorem trTreeCost_sub_trTailGain_lt {m : ℤ} (hm : Odd m) (hm0 : 0 < m) (hm1 : m < 2 ^ 16)
    {β : ℝ} (hβ : |β| ≤ 1 / 3) :
    ∃ a b : ℝ, -(1 / 3) ≤ a ∧ a ≤ β ∧ β ≤ b ∧ b ≤ 1 / 3 ∧
      trTreeCost trZeroCutoff (trWhitePolicy 0 12 14 m a b) 0 0 (m + β) - trTailGain 0 12 <
        77 / 100 := by
  obtain ⟨n, rfl⟩ := hm
  have e : (2 * n + 1 : ℤ) = 1 + 2 ^ 1 * n := by ring
  have h := good_one_one n (e ▸ hm0) (e ▸ hm1) β hβ
  rw [← e] at h
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := h
  refine ⟨a, b, h1, h2, h3, h4, ?_⟩
  rw [trTailGain_zero_twelve]
  rw [bound_eq] at h5
  linarith

end CollatzPosDens
