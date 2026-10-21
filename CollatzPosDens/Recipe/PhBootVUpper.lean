/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.PhBootPowerLower
public import CollatzPosDens.Transfer.MxBootV

/-!
# An upper bound for `v_b`

The constant coefficient of the bootstrap profile is `v_b = f(z) log c_bt` with
`z = c_bt ^ a_mx(b)` and `f(x) = x/(x - 1)^2`. The function `f` is decreasing on `(1, ∞)`: for
`1 < x ≤ y`, `x (y - 1)^2 - y (x - 1)^2 = (y - x)(x y - 1) ≥ 0`. With
`z > z_0 := 1116557504/10^9 > 1` and `0 < log c_bt < ℓ⁺ := 76034686276/10^12`,
$$0 < v_{\mathrm b} \le f(z_0)\log c_{\mathrm{bt}} < f(z_0)\,\ell^+ = 6.24902663181433\ldots
< \frac{624902664}{10^8}.$$

## Main results

* `CollatzPosDens.bootV_mem_Ioo`: `0 < v_b < 624902664/10^8`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `x ↦ x/(x - 1)^2` is antitone on `(1, ∞)`, in cleared form:
`x (y - 1)^2 - y (x - 1)^2 = (y - x)(x y - 1) ≥ 0` for `1 < x ≤ y`. -/
private lemma bootV_upper_ratio_antitone {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    y * (x - 1) ^ 2 ≤ x * (y - 1) ^ 2 := by
  have h : x * (y - 1) ^ 2 - y * (x - 1) ^ 2 = (y - x) * (x * y - 1) := by ring
  have : 0 ≤ (y - x) * (x * y - 1) := mul_nonneg (by linarith) (by nlinarith)
  linarith

/-- `0 < v_b < 624902664/10^8` for the constant coefficient of the bootstrap profile
`v_b = c_bt ^ a_mx(b) · log c_bt / (c_bt ^ a_mx(b) - 1)^2`. -/
@[collatz_pos_dens "lem_ph_boot_v_upper"]
theorem bootV_mem_Ioo : 0 < bootV .b ∧ bootV .b < 624902664 / 10 ^ 8 := by
  refine ⟨bootV_pos .b, ?_⟩
  set z : ℝ := (bootChainRatio : ℝ) ^ (amix .b : ℝ) with hzdef
  set L : ℝ := Real.log (bootChainRatio : ℝ) with hLdef
  have hz : (1116557504 / 10 ^ 9 : ℝ) < z := lt_bootChainRatio_rpow_amix_b
  have hL : L < 76034686276 / 10 ^ 12 := log_bootChainRatio_mem_Ioo.2
  have hL0 : 0 < L := log_bootChainRatio_pos
  have hmono := bootV_upper_ratio_antitone (x := 1116557504 / 10 ^ 9) (y := z) (by norm_num) hz.le
  have hnum : (1116557504 / 10 ^ 9 : ℝ) * (76034686276 / 10 ^ 12) <
      624902664 / 10 ^ 8 * (1116557504 / 10 ^ 9 - 1) ^ 2 := by norm_num
  have hz1 : 0 < (z - 1) ^ 2 := pow_pos (by linarith) 2
  rw [bootV_eq, ← hzdef, ← hLdef, div_lt_iff₀ hz1]
  set d : ℝ := (1116557504 / 10 ^ 9 - 1) ^ 2 with hd
  have hd0 : 0 < d := by rw [hd]; norm_num
  refine lt_of_mul_lt_mul_right ?_ hd0.le
  calc z * L * d < z * (76034686276 / 10 ^ 12) * d := by gcongr
    _ = z * d * (76034686276 / 10 ^ 12) := by ring
    _ ≤ 1116557504 / 10 ^ 9 * (z - 1) ^ 2 * (76034686276 / 10 ^ 12) := by gcongr
    _ = 1116557504 / 10 ^ 9 * (76034686276 / 10 ^ 12) * (z - 1) ^ 2 := by ring
    _ < 624902664 / 10 ^ 8 * d * (z - 1) ^ 2 := by gcongr
    _ = 624902664 / 10 ^ 8 * (z - 1) ^ 2 * d := by ring

end CollatzPosDens
