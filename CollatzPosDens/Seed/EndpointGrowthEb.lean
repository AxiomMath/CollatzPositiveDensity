/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.Maps.AffineIdentity
public import CollatzPosDens.Maps.OffsetBound
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.Seed.BlockWeight
public import CollatzPosDens.Seed.OffsetSmall

/-!
# Growth of endpoints by `16^{e_b}`

Let `b ≥ 9` and `K ≥ 0`, let `R` be an integer with `R ≥ 16^b`, and let `w ∈ 𝒞(b, K)`. Then
`src(w, R) > 16^{e_b} R`.

By the affine identity, `ω(w) src(w, R) = R - off(w)`. Since `w ∈ 𝒲(b, r_b, K)`, the offset
satisfies `off(w) < 2^b = 2^{-3b} 16^b ≤ 2^{-3b} R`, so `R - off(w) > (1 - 2^{-3b}) R`, while the
block-weight bound gives `16^{e_b} ω(w) < 1 - 2^{-3b}`. Dividing by `ω(w) > 0` gives the claim.

## Main results

* `CollatzPosDens.sixteen_pow_eb_mul_lt_src_of_mem_centralFamily`: for `b ≥ 9`, `R ≥ 16^b` and
  `w ∈ 𝒞(b, K)`, one has `16^{e_b} R < src(w, R)`.

## Implementation notes

The levels `b` and `K` are natural numbers and the comparison takes place in `ℚ`, where the
source lives. The argument uses neither the oddness of `R` nor the admissibility of `w` from `R`,
so neither is assumed.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Growth of endpoints by `16^{e_b}`.** Let `b ≥ 9`, `K ≥ 0`, let `R` be an integer with
`R ≥ 16^b` and let `w ∈ 𝒞(b, K)`. Then `src(w, R) > 16^{e_b} R`. -/
@[collatz_pos_dens "lem_s05_endpoint_growth_eb"]
theorem sixteen_pow_eb_mul_lt_src_of_mem_centralFamily {b K : ℕ} (hb : 9 ≤ b) {R : ℤ}
    (hR : 16 ^ b ≤ R) {w : Word} (hw : w ∈ centralFamily b K) :
    (16 : ℚ) ^ eb b * R < src w R := by
  have hoff := off_lt_two_pow_of_mem_firstCrossing (centralFamily_subset_firstCrossing b K hw)
  have haff := eq_weight_mul_src_add_off w R
  have hRq : (16 : ℚ) ^ b ≤ R := by exact_mod_cast hR
  have hoffR : off w * 2 ^ (3 * b) < R :=
    calc off w * 2 ^ (3 * b) < 2 ^ b * 2 ^ (3 * b) := by gcongr
      _ = 16 ^ b := by
        rw [← pow_add, show b + 3 * b = 4 * b by ring, pow_mul]
        norm_num
      _ ≤ R := hRq
  have h₁ := mul_lt_mul_of_pos_right (sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily hb hw)
    (lt_of_lt_of_le (by positivity) hRq)
  have h₂ : off w < ((2 : ℚ) ^ (3 * b))⁻¹ * R := by
    rwa [inv_mul_eq_div, lt_div_iff₀ (by positivity)]
  refine lt_of_mul_lt_mul_left ?_ (Word.weight_pos w).le
  linarith

end CollatzPosDens
