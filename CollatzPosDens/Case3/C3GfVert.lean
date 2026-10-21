/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnJointPgf
public import CollatzPosDens.Renewal.RnJointPgfValue
public import CollatzPosDens.Transfer.S02DevEta
public import CollatzPosDens.Transfer.S02DevY
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The vertical deviation generating function

For each Fourier index `ι`, the joint generating function of a hold at the point `(1, y_dv(ι))`
lies below `y_dv(ι) ^ η_dv(ι)`, where `(y_dv, η_dv) = (169/168, 6579/500)` for `ι = o` and
`(y_dv, η_dv) = (144/143, 1653/125)` for `ι = b`.

Put `y = y_dv(ι)`. Since `0 < y < 2` and `Σ(y) = y² / (2 - y)² - (3/16) y⁴ - (1/8) y⁵ < 1`
(`Σ(y) = 21000337467604235 / 29858592925679616` for `ι = o` and
`Σ(y) = 212855428255680 / 301437226181663` for `ι = b`), the closed form of the joint generating
function gives the rational value `𝖦(1, y) = a / b`, with
`(a, b) = (9577713826824949, 8858255458075381)` for `ι = o` and
`(a, b) = (97132784504832, 88581797925983)` for `ι = b`. Writing `η_dv = e / k`, the integer
inequality `a ^ k * (denominator of y) ^ e < b ^ k * (numerator of y) ^ e` says
`𝖦(1, y) ^ k < y ^ e`, and taking positive `k`th roots gives `𝖦(1, y) < y ^ η_dv`.

## Main results

* `CollatzPosDens.holdJointPgf_one_devY_eq_o`, `CollatzPosDens.holdJointPgf_one_devY_eq_b`:
  the exact values of `𝖦(1, y_dv(ι))`.
* `CollatzPosDens.holdJointPgf_one_devY_lt`: `𝖦(1, y_dv(ι)) < y_dv(ι) ^ η_dv(ι)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The value `𝖦(1, y_dv(o)) = 9577713826824949 / 8858255458075381`. -/
theorem holdJointPgf_one_devY_eq_o :
    holdJointPgf 1 (devY .o : ℝ) =
      ENNReal.ofReal (9577713826824949 / 8858255458075381) := by
  rw [devY_cast_o, holdJointPgf_eq one_pos (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The value `𝖦(1, y_dv(b)) = 97132784504832 / 88581797925983`. -/
theorem holdJointPgf_one_devY_eq_b :
    holdJointPgf 1 (devY .b : ℝ) = ENNReal.ofReal (97132784504832 / 88581797925983) := by
  rw [devY_cast_b, holdJointPgf_eq one_pos (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `p / q < (n / d) ^ (e / k)` (a positive real power) from the integer comparison
`p ^ k * d ^ e < q ^ k * n ^ e`. -/
private lemma div_lt_div_rpow_of_nat_gfVert {p q n d k e : ℕ} (hq : 0 < q) (hn : 0 < n)
    (hd : 0 < d) (hk : k ≠ 0) (h : p ^ k * d ^ e < q ^ k * n ^ e) :
    (p / q : ℝ) < ((n : ℝ) / d) ^ ((e : ℝ) / k) := by
  have hb : (0 : ℝ) ≤ (n : ℝ) / d := by positivity
  rw [← pow_lt_pow_iff_left₀ (by positivity) (Real.rpow_nonneg hb _) hk,
    ← Real.rpow_natCast (((n : ℝ) / d) ^ ((e : ℝ) / k)), ← Real.rpow_mul hb,
    div_mul_cancel₀ _ (by exact_mod_cast hk), Real.rpow_natCast, div_pow, div_pow,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  have h' := (Nat.cast_lt (α := ℝ)).2 h
  push_cast at h'
  linarith

/-- **The vertical deviation generating function.** For every Fourier index `ι`,
`𝖦(1, y_dv(ι)) < y_dv(ι) ^ η_dv(ι)`. -/
@[collatz_pos_dens "lem_c3_gf_vert"]
theorem holdJointPgf_one_devY_lt (ι : FIndex) :
    holdJointPgf 1 (devY ι : ℝ) < ENNReal.ofReal ((devY ι : ℝ) ^ (devEta ι : ℝ)) := by
  have hR : 0 < (devY ι : ℝ) ^ (devEta ι : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast devY_pos ι) _
  cases ι
  · rw [holdJointPgf_one_devY_eq_o, ENNReal.ofReal_lt_ofReal_iff hR, devY_cast_o,
      devEta_cast_o]
    have h := div_lt_div_rpow_of_nat_gfVert (p := 9577713826824949) (q := 8858255458075381)
      (n := 169) (d := 168) (k := 500) (e := 6579) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)
    exact_mod_cast h
  · rw [holdJointPgf_one_devY_eq_b, ENNReal.ofReal_lt_ofReal_iff hR, devY_cast_b,
      devEta_cast_b]
    have h := div_lt_div_rpow_of_nat_gfVert (p := 97132784504832) (q := 88581797925983)
      (n := 144) (d := 143) (k := 125) (e := 1653) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by decide +kernel)
    exact_mod_cast h

end CollatzPosDens
