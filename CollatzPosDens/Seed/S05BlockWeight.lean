/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.WeightUpper
public import CollatzPosDens.Seed.S05FourThirds
public import CollatzPosDens.Maps.Weight

/-!
# The weight of a central block

For every level `b ≥ 256`, every `K ≥ 0` and every word `w` of the central family `𝒞(b, K)`,
$$16^{e_b}\,\omega(w) < 1 - 2^{-3b}.$$

Since `𝒞(b, K) ⊆ 𝒲(b, r_b, K)`, the weight bound for first-crossing words with `u = r_b` gives
`ω(w) < 2 (3/4)^b`. As `e_b = ⌈b/100⌉` and `b ≥ 256`, the power comparison
`4 · 16^{e_b} ≤ (4/3)^b` holds. Hence `16^{e_b} ω(w) < 1/2 ≤ 1 - 2^{-3b}`.

## Main results

* `CollatzPosDens.sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily`:
  `16^{e_b} ω(w) < 1 - 2^{-3b}` for `b ≥ 256` and `w ∈ 𝒞(b, K)`.

## Implementation notes

The levels `b` and `K` are natural numbers, and the inequality is stated in `ℚ`, where the
weight lives, with `2^{-3b}` written as `(2^{3b})⁻¹`. The power comparison is used in its
cleared-denominator form `4 · 16^{e_b} · 3^b ≤ 4^b` in `ℕ`.

## References

* [Mazur, *Collatz positive density*], §17.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Weight of a central block.** For `b ≥ 256`, `K ≥ 0` and `w ∈ 𝒞(b, K)`,
`16^{e_b} ω(w) < 1 - 2^{-3b}`. -/
@[collatz_pos_dens "lem_s05_block_weight"]
theorem sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily {b K : ℕ} {w : Word}
    (hb : 256 ≤ b) (hw : w ∈ centralFamily b K) :
    (16 : ℚ) ^ eb b * w.weight < 1 - (2 ^ (3 * b))⁻¹ := by
  have h1 := weight_le_of_mem_firstCrossing (centralFamily_subset_firstCrossing b K hw)
  rw [show 1 + rb b - rb b = 1 by ring, zpow_one] at h1
  have hp : 4 * 16 ^ eb b * 3 ^ b ≤ 4 ^ b :=
    four_mul_sixteen_pow_mul_three_pow_le_four_pow hb (by rw [eb_eq]; omega)
  have hp' : (4 : ℚ) * 16 ^ eb b * 3 ^ b ≤ 4 ^ b := by exact_mod_cast hp
  have h4 : (0 : ℚ) < 4 ^ b := by positivity
  have hinv : ((2 : ℚ) ^ (3 * b))⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num)
      (le_self_pow₀ (by norm_num) (by omega))
  have key : (16 : ℚ) ^ eb b * (2 * (3 / 4) ^ b) ≤ 1 / 2 := by
    rw [div_pow, show (16 : ℚ) ^ eb b * (2 * (3 ^ b / 4 ^ b))
      = (4 * 16 ^ eb b * 3 ^ b) / (2 * 4 ^ b) by field_simp; ring, div_le_iff₀ (by positivity)]
    linarith
  calc (16 : ℚ) ^ eb b * w.weight < 16 ^ eb b * (2 * (3 / 4) ^ b) := by gcongr
    _ ≤ 1 / 2 := key
    _ ≤ 1 - (2 ^ (3 * b))⁻¹ := by linarith

end CollatzPosDens
