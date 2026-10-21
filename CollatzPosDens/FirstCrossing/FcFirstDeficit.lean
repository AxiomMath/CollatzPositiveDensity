/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.FcCover
public import CollatzPosDens.FirstCrossing.FcFirstEarly
public import CollatzPosDens.FirstCrossing.FcFirstEarlyValue
public import CollatzPosDens.FirstCrossing.FcFirstMissing
public import CollatzPosDens.FirstCrossing.FcFirstMissingValue
public import CollatzPosDens.FirstCrossing.Scales

/-!
# The deficit of the first family

At the first generation `j = 0` the central family has deficit
$$1-\mathbf p(\mathcal C(b_0,K_0))<\tfrac1{20000000}.$$

Here `b_0 = 16544` and `K_0 = 29`. Since `2^{14} < 16544 ≤ 2^{15}`, `lg 16544 = 15`, and
`2817² < 32 · 16544 · 15 = 7941120 ≤ 2818²`, so `wd 16544 = 2818`; the central family is then
the set of words of `𝒲(16544, r_{16544}, 29)` of length in `[13726, 19362]`, and
`ℓ_{16544} = 6618 < 13726 ≤ 19362 ≤ 26470 = h_{16544}`. The covering bound for a first-crossing
window bounds the deficit by the early-crossing mass (less than `1/3000000000`), the
missing-crossing mass (less than `1/39000000`) and the overshoot loss `2^{-30}`, and
$$\frac1{3000000000}+\frac1{39000000}+\frac1{2^{30}}<\frac1{20000000}.$$

## Main results

* `CollatzPosDens.wd_16544`: `wd 16544 = 2818`.
* `CollatzPosDens.centralFamily_16544_29`: `𝒞(16544, 29)` is the length window
  `[13726, 19362]` of `𝒲(16544, r_{16544}, 29)`.
* `CollatzPosDens.one_sub_geomMass_centralFamily_scale_zero_lt`:
  `1 - 𝐩(𝒞(b_0, K_0)) < 1/20000000`.

## Implementation notes

The geometric mass is `ℝ≥0∞`-valued, so the bound `1/20000000` is written `20000000⁻¹ : ℝ≥0∞`
and `1 - 𝐩(·)` is truncated subtraction.

## References

* [Mazur, *Collatz positive density*], §15.5.
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- The width at the first scale: `wd 16544 = 2818`, since `lg 16544 = 15` and
`2817² < 32 · 16544 · 15 ≤ 2818²`. -/
theorem wd_16544 : wd 16544 = 2818 := by
  have hlg : lg 16544 = 15 := by
    refine le_antisymm (lg_le_iff_le_two_pow.2 (by norm_num)) ?_
    by_contra h
    have := lg_le_iff_le_two_pow.1 (show lg 16544 ≤ 14 by omega)
    norm_num at this
  have hceil : ⌈√(32 * ((16544 : ℕ) : ℝ) * ((lg 16544 : ℕ) : ℝ))⌉₊ = 2818 := by
    rw [hlg, Nat.ceil_eq_iff (by norm_num)]
    push_cast
    constructor
    · rw [Real.lt_sqrt (by norm_num)]; norm_num
    · rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [wd_def, hceil]
  norm_num

/-- At `b = 16544`, `K = 29`, the central family is the length window `[13726, 19362]` of the
first-crossing family `𝒲(16544, r_{16544}, 29)`. -/
theorem centralFamily_16544_29 :
    centralFamily 16544 29 =
      {w | w ∈ firstCrossing 16544 (rb 16544) 29 ∧ 13726 ≤ w.length ∧ w.length ≤ 19362} := by
  ext w
  rw [mem_centralFamily, wd_16544]
  rfl

/-- At the first generation the central family has deficit
`1 - 𝐩(𝒞(b_0, K_0)) < 1/20000000`, where `b_0 = 16544` and `K_0 = 29`. -/
@[collatz_pos_dens "lem_fc_first_deficit"]
theorem one_sub_geomMass_centralFamily_scale_zero_lt :
    1 - geomMass (centralFamily (scale 0) (cap 0)) < 20000000⁻¹ := by
  have hcap : cap 0 = 29 := rfl
  rw [scale_zero, hcap, centralFamily_16544_29]
  refine (one_sub_geomMass_firstCrossing_window_le 16544 (rb 16544) 29
    (by rw [lb_eq]; norm_num) (by norm_num) (by rw [hb_eq]; norm_num)).trans_lt ?_
  have hE := fcFirstEarly_geomMass_le
  have hM := fcFirstMissing_geomMass_le
  set a : ℝ := (24 / 25 : ℝ) ^ 1169 * (576 / 575) ^ 13725 with ha_def
  set c : ℝ := (31 / 32 : ℝ) ^ 1170 * (1024 / 1023 : ℝ) ^ 19362 with hc_def
  have ha : a < 1 / 3000000000 := fcFirstEarly_value_lt
  have hc : c < 1 / 39000000 := fcFirstMissingValue_lt
  have ha0 : 0 ≤ a := by positivity
  have hc0 : 0 ≤ c := by positivity
  clear_value a c
  have hpow : (2⁻¹ : ℝ≥0∞) ^ (29 + 1) = ENNReal.ofReal ((2⁻¹ : ℝ) ^ (29 + 1)) := by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
      ENNReal.ofReal_ofNat]
  have htarget : (20000000⁻¹ : ℝ≥0∞) = ENNReal.ofReal (20000000⁻¹ : ℝ) := by
    rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  calc _ ≤ ENNReal.ofReal a + ENNReal.ofReal c + (2⁻¹ : ℝ≥0∞) ^ (29 + 1) :=
        add_le_add (add_le_add hE hM) le_rfl
    _ = ENNReal.ofReal (a + c + (2⁻¹ : ℝ) ^ (29 + 1)) := by
        rw [hpow, ← ENNReal.ofReal_add ha0 hc0, ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
    _ < 20000000⁻¹ := by
        rw [htarget, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
        have h : (2⁻¹ : ℝ) ^ (29 + 1) = 1 / 1073741824 := by norm_num
        rw [h]
        linarith

end CollatzPosDens
