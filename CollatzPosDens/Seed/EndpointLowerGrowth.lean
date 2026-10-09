/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Admissible
public import CollatzPosDens.Maps.AffineIdentity
public import CollatzPosDens.FirstCrossing.Rb
public import CollatzPosDens.FirstCrossing.WeightUpper
public import CollatzPosDens.Seed.OffsetSmall

/-!
# Growth of endpoints: the lower bound

Let `b ≥ 1`, `K ≥ 0`, let `R` be an odd integer with `R ≥ 16^b`, and let
`w ∈ 𝒲(b, r_b, K)` be admissible from `R`. Then `src(w, R) ≥ ¼ (4/3)^b R`.

Indeed `off(w) < 2^b ≤ R/2`, so `R - off(w) ≥ R/2`; the affine identity gives
`src(w, R) = (R - off(w)) / ω(w)`, and `ω(w) ≤ 2 (3/4)^b`.

## Main results

* `CollatzPosDens.endpoint_lower_growth_of_two_mul_two_pow_le`: the bound for every
  rational `R ≥ 2 · 2^b`.
* `CollatzPosDens.endpoint_lower_growth`: the bound for odd integers `R ≥ 16^b` and words `w`
  admissible from `R`.

## Implementation notes

The argument uses only `R ≥ 2 · 2^b` and `w ∈ 𝒲(b, r_b, K)`; oddness of `R` and admissibility
of `w` are not needed, and are kept in `endpoint_lower_growth` only to match the source. The
general form is `endpoint_lower_growth_of_two_mul_two_pow_le`, from which `endpoint_lower_growth`
follows since `16^b ≥ 2 · 2^b` for `b ≥ 1`.

## References

* [Mazur, *Collatz positive density*], §17.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `w ∈ 𝒲(b, r_b, K)` and a rational `R ≥ 2 · 2^b`, `src(w, R) ≥ ¼ (4/3)^b R`. -/
theorem endpoint_lower_growth_of_two_mul_two_pow_le {b K : ℕ} {w : Word}
    (hw : w ∈ firstCrossing b (rb b) K) {R : ℚ} (hR : 2 * 2 ^ b ≤ R) :
    1 / 4 * (4 / 3) ^ b * R ≤ src w R := by
  have hoff := off_lt_two_pow_of_mem_firstCrossing hw
  have hω := weight_le_of_mem_firstCrossing hw
  rw [add_sub_cancel_right, zpow_one] at hω
  have hω0 := Word.weight_pos w
  have h2b : (0 : ℚ) < 2 ^ b := by positivity
  rw [show src w R = (R - off w) / w.weight by
    rw [eq_div_iff hω0.ne']
    linarith [eq_weight_mul_src_add_off w R]]
  calc 1 / 4 * (4 / 3 : ℚ) ^ b * R = (R / 2) / (2 * (3 / 4) ^ b) := by
        rw [div_pow, div_pow]
        field_simp
        ring
    _ ≤ (R - off w) / w.weight := div_le_div₀ (by linarith) (by linarith) hω0 hω

/-- **Growth of endpoints (lower bound).** Let `b ≥ 1`, `K ≥ 0`, let `R` be an odd integer with
`R ≥ 16^b`, and let `w ∈ 𝒲(b, r_b, K)` be admissible from `R`. Then
`src(w, R) ≥ ¼ (4/3)^b R`. -/
@[collatz_pos_dens "lem_endpoint_lower_growth"]
theorem endpoint_lower_growth {b K : ℕ} (hb : 1 ≤ b) {R : ℤ} (_hodd : Odd R)
    (hR : 16 ^ b ≤ R) {w : Word} (hw : w ∈ firstCrossing b (rb b) K)
    (_hadm : Admissible R w) : 1 / 4 * (4 / 3 : ℚ) ^ b * R ≤ src w R := by
  refine endpoint_lower_growth_of_two_mul_two_pow_le hw ?_
  calc (2 : ℚ) * 2 ^ b ≤ 8 ^ b * 2 ^ b := by
        gcongr
        exact le_trans (by norm_num) (le_self_pow₀ (by norm_num) (by omega))
    _ = 16 ^ b := by
        rw [← mul_pow]
        norm_num
    _ ≤ R := by exact_mod_cast hR

end CollatzPosDens
