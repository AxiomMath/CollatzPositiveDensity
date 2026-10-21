/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.FirstCrossing.FcMarginal
public import CollatzPosDens.FirstCrossing.FcTiltMaximal
public import CollatzPosDens.Transfer.S03Log3Bounds

/-!
# Early crossing in the first block

Let `b = 16544`, so that `w_b = 9926`, `ℓ_b = 6618` and `h_b = 26470`. The words
`v ∈ ℤ_{≥1}^{h_b}` whose valuation sum crosses the centred barrier `H_{b,r_b}` early, at some
`ℓ_b ≤ i < 13726`, have geometric mass at most `(24/25)^{1169} (576/575)^{13725}`.

For such `i`, with `m = b - i ≥ 2819`, the barrier is `H_{b,r_b}(i) = 2b - B(m)`, and
`B(m) < m log₂ 3 + 1 < (317/200) m + 1`, so a crossing forces `A_i(v) - 2i ≥ 2m - B(m) ≥ 1169`.
The event depends only on the prefix `v_{≤ 13725}`, so the marginal identity
`geomMass_setOf_take_mem` and the tilted maximal inequality `fcTiltMaximal_geomMass_le` with
`H = 13725`, `v = 1169` and `δ = 1/24` give the bound.

## Main results

* `CollatzPosDens.ceilLog3_le_two_mul_sub_1169`: `B(m) ≤ 2m - 1169` for `m ≥ 2819`.
* `CollatzPosDens.fcFirstEarly_geomMass_le`: the early-crossing bound.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- For `m ≥ 2819`, the rounded logarithm satisfies `B(m) ≤ 2m - 1169`, since
`B(m) < m log₂ 3 + 1` and `log₂ 3 < 317/200`. -/
theorem ceilLog3_le_two_mul_sub_1169 {m : ℕ} (hm : 2819 ≤ m) :
    (ceilLog3 m : ℤ) ≤ 2 * m - 1169 := by
  have h1 := ceilLog3_lt_mul_logb_add_one m
  have h2 := logb_two_three_bounds.2
  have hm' : (2819 : ℝ) ≤ m := by exact_mod_cast hm
  have h3 : ((ceilLog3 m : ℤ) : ℝ) < ((2 * m - 1168 : ℤ) : ℝ) := by
    push_cast
    nlinarith
  have h4 := Int.cast_lt.1 h3
  omega

/-- Early crossing in the first block: with `b = 16544`,
`𝐩({v ∈ ℤ_{≥1}^{h_b} : ∃ i, ℓ_b ≤ i < 13726, A_i(v) ≥ H_{b,r_b}(i)})
  ≤ (24/25)^{1169} (576/575)^{13725}`. -/
@[collatz_pos_dens "lem_fc_first_early"]
theorem fcFirstEarly_geomMass_le :
    geomMass {v : Word | v.length = hb 16544 ∧
        ∃ i, lb 16544 ≤ i ∧ i < 13726 ∧
          barrier 16544 (rb 16544) i ≤ (Word.valSum (v.take i) : ℤ)} ≤
      ENNReal.ofReal ((24 / 25 : ℝ) ^ 1169 * (576 / 575) ^ 13725) := by
  have hhb : hb 16544 = 26470 := by rw [hb_eq]
  have hlb : lb 16544 = 6618 := by rw [lb_eq]
  set E' := {x : Word | x.length = 13725 ∧
    ∃ i, 1 ≤ i ∧ i ≤ 13725 ∧ ((1169 : ℕ) : ℤ) ≤ (Word.valSum (x.take i) : ℤ) - 2 * i}
  have hsub : {v : Word | v.length = hb 16544 ∧
      ∃ i, lb 16544 ≤ i ∧ i < 13726 ∧
        barrier 16544 (rb 16544) i ≤ (Word.valSum (v.take i) : ℤ)} ⊆
      {v : Word | v.length = hb 16544 ∧ v.take 13725 ∈ E'} := by
    rintro v ⟨hlen, i, hi1, hi2, hcross⟩
    rw [hlb] at hi1
    refine ⟨hlen, ?_, i, by omega, by omega, ?_⟩
    · rw [List.length_take, hlen, hhb]; rfl
    · rw [List.take_take, min_eq_left (by omega)]
      rw [barrier_of_ge _ (by omega : i ≤ 16544)] at hcross
      have hB := ceilLog3_le_two_mul_sub_1169 (m := 16544 - i) (by omega)
      push_cast at hB ⊢
      omega
  have hmarg := geomMass_setOf_take_mem (t := 13725) (h := hb 16544) (by rw [hhb]; norm_num)
    (E := E') (fun w hw => hw.1)
  refine (geomMass_mono hsub).trans (hmarg.le.trans ?_)
  refine (fcTiltMaximal_geomMass_le 13725 (1169 : ℕ) (δ := 1 / 24) (by norm_num)
    (by norm_num)).trans_eq ?_
  congr 1
  rw [zpow_neg, zpow_natCast, zpow_neg, zpow_natCast, ← inv_pow, ← inv_pow,
    show (1 + 1 / 24 : ℝ)⁻¹ = 24 / 25 by norm_num,
    show (1 - (1 / 24) ^ 2 : ℝ)⁻¹ = 576 / 575 by norm_num]

end CollatzPosDens
