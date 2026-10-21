/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnJointPgfValue
public import CollatzPosDens.Transfer.S02DevB
public import CollatzPosDens.Transfer.S02DevSigma

/-!
# The drift-free deviation generating functions

Write `𝖦 = holdJointPgf` for the joint generating function of a hold. For each Fourier index `ι`
let `b = devB ι` and `σ = devSigma ι`, so that `(b, σ) = (51/50, 257/2000)` for `ι = o` and
`(b, σ) = (43/42, 383/2500)` for `ι = b`. For `ς ∈ {1, -1}` we show `𝖦(b^{4ς}, b^{-ς}) < b^σ`.

With `X = b^{4ς}` and `y = b^{-ς} ∈ (0, 2)`, the closed form `holdJointPgf_eq` applies, since
`X Σ(y) < 1` for `Σ(y) = y² / (2 - y)² - (3/16) y⁴ - (1/8) y⁵`. It gives the exact rational values
* `ι = o`: `𝖦(b⁴, b⁻¹) = 106892500 / 106627249` and `𝖦(b⁻⁴, b) = 393435063 / 392435263`;
* `ι = b`: `𝖦(b⁴, b⁻¹) = 45463572 / 45304601` and `𝖦(b⁻⁴, b) = 164732957 / 164140421`.

Writing `σ = e / k`, in each case `𝖦^k < b^e` is an exact comparison of natural numbers after
clearing denominators, and taking positive `k`th roots gives `𝖦 < b^σ`.

## Main results

* `CollatzPosDens.holdJointPgf_devB_one_eq_o`, `CollatzPosDens.holdJointPgf_devB_neg_one_eq_o`,
  `CollatzPosDens.holdJointPgf_devB_one_eq_b`, `CollatzPosDens.holdJointPgf_devB_neg_one_eq_b`:
  the exact values of `𝖦(b⁴, b⁻¹)` and `𝖦(b⁻⁴, b)` at both indices.
* `CollatzPosDens.holdJointPgf_devB_lt`: `𝖦(devB ι ^ (4ς), devB ι ^ (-ς)) < devB ι ^ devSigma ι`
  for every index `ι` and `ς ∈ {1, -1}`.

## References

* [Mazur, *Collatz positive density*, §10.1]
-/
@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- `holdJointPgf (devB .o ^ 4) (devB .o ^ (-1)) = 106892500 / 106627249`. -/
theorem holdJointPgf_devB_one_eq_o :
    holdJointPgf ((devB .o : ℝ) ^ (4 * (1 : ℤ))) ((devB .o : ℝ) ^ (-(1 : ℤ))) =
      ENNReal.ofReal (106892500 / 106627249) := by
  rw [devB_cast_o]
  norm_num only [zpow_neg, zpow_one, mul_one, zpow_ofNat]
  rw [holdJointPgf_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `holdJointPgf (devB .o ^ (-4)) (devB .o) = 393435063 / 392435263`. -/
theorem holdJointPgf_devB_neg_one_eq_o :
    holdJointPgf ((devB .o : ℝ) ^ (4 * (-1 : ℤ))) ((devB .o : ℝ) ^ (-(-1 : ℤ))) =
      ENNReal.ofReal (393435063 / 392435263) := by
  rw [devB_cast_o]
  norm_num only [zpow_neg, neg_neg, zpow_one, mul_neg, mul_one, zpow_ofNat]
  rw [holdJointPgf_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `holdJointPgf (devB .b ^ 4) (devB .b ^ (-1)) = 45463572 / 45304601`. -/
theorem holdJointPgf_devB_one_eq_b :
    holdJointPgf ((devB .b : ℝ) ^ (4 * (1 : ℤ))) ((devB .b : ℝ) ^ (-(1 : ℤ))) =
      ENNReal.ofReal (45463572 / 45304601) := by
  rw [devB_cast_b]
  norm_num only [zpow_neg, zpow_one, mul_one, zpow_ofNat]
  rw [holdJointPgf_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `holdJointPgf (devB .b ^ (-4)) (devB .b) = 164732957 / 164140421`. -/
theorem holdJointPgf_devB_neg_one_eq_b :
    holdJointPgf ((devB .b : ℝ) ^ (4 * (-1 : ℤ))) ((devB .b : ℝ) ^ (-(-1 : ℤ))) =
      ENNReal.ofReal (164732957 / 164140421) := by
  rw [devB_cast_b]
  norm_num only [zpow_neg, neg_neg, zpow_one, mul_neg, mul_one, zpow_ofNat]
  rw [holdJointPgf_eq (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- `p / q < (n / d) ^ (e / k)` (a positive real power) from the integer comparison
`p ^ k * d ^ e < q ^ k * n ^ e`. -/
private lemma div_lt_div_rpow_of_nat_gfDrift {p q n d k e : ℕ} (hq : 0 < q) (hn : 0 < n)
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

/-- **The drift-free deviation generating functions.** For every Fourier index `ι` and
`ς ∈ {1, -1}`, `holdJointPgf (devB ι ^ (4ς)) (devB ι ^ (-ς)) < devB ι ^ devSigma ι`. -/
@[collatz_pos_dens "lem_c3_gf_drift"]
theorem holdJointPgf_devB_lt (ι : FIndex) {ς : ℤ} (hς : ς = 1 ∨ ς = -1) :
    holdJointPgf ((devB ι : ℝ) ^ (4 * ς)) ((devB ι : ℝ) ^ (-ς)) <
      ENNReal.ofReal ((devB ι : ℝ) ^ (devSigma ι : ℝ)) := by
  have hpos : 0 < (devB ι : ℝ) ^ (devSigma ι : ℝ) :=
    Real.rpow_pos_of_pos (by exact_mod_cast devB_pos ι) _
  cases ι <;> rcases hς with rfl | rfl
  · rw [holdJointPgf_devB_one_eq_o, ENNReal.ofReal_lt_ofReal_iff hpos, devB_cast_o,
      devSigma_cast_o]
    have h := div_lt_div_rpow_of_nat_gfDrift (p := 106892500) (q := 106627249) (n := 51)
      (d := 50) (k := 2000) (e := 257) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel)
    exact_mod_cast h
  · rw [holdJointPgf_devB_neg_one_eq_o, ENNReal.ofReal_lt_ofReal_iff hpos, devB_cast_o,
      devSigma_cast_o]
    have h := div_lt_div_rpow_of_nat_gfDrift (p := 393435063) (q := 392435263) (n := 51)
      (d := 50) (k := 2000) (e := 257) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel)
    exact_mod_cast h
  · rw [holdJointPgf_devB_one_eq_b, ENNReal.ofReal_lt_ofReal_iff hpos, devB_cast_b,
      devSigma_cast_b]
    have h := div_lt_div_rpow_of_nat_gfDrift (p := 45463572) (q := 45304601) (n := 43)
      (d := 42) (k := 2500) (e := 383) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel)
    exact_mod_cast h
  · rw [holdJointPgf_devB_neg_one_eq_b, ENNReal.ofReal_lt_ofReal_iff hpos, devB_cast_b,
      devSigma_cast_b]
    have h := div_lt_div_rpow_of_nat_gfDrift (p := 164732957) (q := 164140421) (n := 43)
      (d := 42) (k := 2500) (e := 383) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by decide +kernel)
    exact_mod_cast h

end CollatzPosDens
