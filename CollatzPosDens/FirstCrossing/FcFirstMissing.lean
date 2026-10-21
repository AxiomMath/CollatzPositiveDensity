/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.Hb
public import CollatzPosDens.FirstCrossing.FcMarginal
public import CollatzPosDens.FirstCrossing.FcTiltLower
public import CollatzPosDens.Transfer.S03Log3Bounds

/-!
# Missing crossing in the first block

Let `b = 16544`, so that `h_b = 26470`. We bound the geometric mass of the words `v ∈ ℤ_{≥1}^{h_b}`
whose prefix valuation sum `A_{19362}(v)` stays below the centred barrier `H_{b,r_b}(19362)`:
`𝐩({v : A_{19362}(v) < H_{b,r_b}(19362)}) ≤ (31/32)^{1170} (1024/1023)^{19362}`.

Since `19362 = b + 2818`, the barrier is `H_{b,r_b}(19362) = 2b + B(2818)`, and
`B(2818) < 2818 log₂ 3 + 1 < 2818 · 317/200 + 1` gives `H_{b,r_b}(19362) - 2 · 19362 ≤ -1169`.
So on this set `A_{19362}(v) - 2 · 19362 ≤ -1170`. The condition only involves the prefix
`v_{≤ 19362}`, so by the marginal identity the mass is that of the corresponding set of words of
length `19362`, which the exact-tilt lower tail with `δ = 1/32` bounds.

## Main results

* `CollatzPosDens.fcFirstMissing_geomMass_le`: the missing-crossing bound.

## Implementation notes

The prefix valuation sum `A_{19362}(v)` is `Word.valSum (v.take 19362)`. The bound is the real
number `(31/32)^{1170} (1024/1023)^{19362}` viewed in `ℝ≥0∞`; its powers are never evaluated.

## References

* [Mazur, *Collatz positive density*], §15.5.
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- The barrier deviation at the end of the first block:
`H_{16544,r_{16544}}(19362) - 2 · 19362 ≤ -1169`. -/
private theorem fcFirstMissing_barrier_le :
    barrier 16544 (rb 16544) 19362 - 2 * 19362 ≤ -1169 := by
  rw [barrier_of_le _ (by norm_num), show (19362 : ℕ) - 16544 = 2818 by norm_num]
  have h := ceilLog3_lt_mul_logb_add_one 2818
  have hl := (logb_two_three_bounds).2
  have hB : (ceilLog3 2818 : ℝ) < 4468 := by push_cast at h; linarith
  have hB' : ceilLog3 2818 < 4468 := by exact_mod_cast hB
  push_cast
  omega

/-- **Missing crossing in the first block.** For `b = 16544`,
`𝐩({v ∈ ℤ_{≥1}^{h_b} : A_{19362}(v) < H_{b,r_b}(19362)}) ≤ (31/32)^{1170} (1024/1023)^{19362}`. -/
@[collatz_pos_dens "lem_fc_first_missing"]
theorem fcFirstMissing_geomMass_le :
    geomMass {v : Word | v.length = hb 16544 ∧
        (Word.valSum (v.take 19362) : ℤ) < barrier 16544 (rb 16544) 19362} ≤
      ENNReal.ofReal ((31 / 32 : ℝ) ^ 1170 * (1024 / 1023 : ℝ) ^ 19362) := by
  have hhb : hb 16544 = 26470 := by norm_num [hb_eq]
  set E' : Set Word := {x : Word | x.length = 19362 ∧ (x.valSum : ℤ) - 2 * 19362 ≤ -1170}
  have hsub : {v : Word | v.length = hb 16544 ∧
        (Word.valSum (v.take 19362) : ℤ) < barrier 16544 (rb 16544) 19362} ⊆
      {v : Word | v.length = hb 16544 ∧ v.take 19362 ∈ E'} := by
    rintro v ⟨hvl, hvA⟩
    refine ⟨hvl, ?_, ?_⟩
    · rw [List.length_take, hvl, hhb]; rfl
    · have := fcFirstMissing_barrier_le
      push_cast
      omega
  have hmarg := geomMass_setOf_take_mem (t := 19362) (h := hb 16544) (by rw [hhb]; norm_num)
    (E := E') fun w hw => hw.1
  have htilt := fcTiltLower_geomMass_le 19362 1170 (δ := 1 / 32) (by norm_num) (by norm_num)
  have hval : (1 - 1 / 32 : ℝ) ^ 1170 * ((1 - (1 / 32) ^ 2) ^ 19362)⁻¹ =
      (31 / 32 : ℝ) ^ 1170 * (1024 / 1023 : ℝ) ^ 19362 := by
    rw [← inv_pow, show (1 - (1 / 32 : ℝ) ^ 2)⁻¹ = 1024 / 1023 by norm_num,
      show (1 - 1 / 32 : ℝ) = 31 / 32 by norm_num]
  rw [hval] at htilt
  push_cast at htilt
  exact (geomMass_mono hsub).trans (hmarg.trans_le htilt)

end CollatzPosDens
