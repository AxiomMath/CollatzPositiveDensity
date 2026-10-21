/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.MxProfile
public import CollatzPosDens.Transfer.S02AtanhBounds
public import CollatzPosDens.Mixing.MxShLogLower

/-!
# The exact chained profile is below the mixing profile

For each Fourier index `ι ∈ {o, b}` and every real `x ≥ n₀ = 2^80`, the exact chained profile
`𝔐^ex_ι` (`CollatzPosDens.mxExactProfile ι`) is at most the propagation mixing profile `𝔐_ι`
(`CollatzPosDens.mxProfile ι`).

At `ι = b` the two profiles are the same function. At `ι = o`, write `c = c_bt = 1079/1000`,
`a = a_mx(o) = 18693/10000`, `z = c ^ a` and `L = log x ≥ 160/3`. The atanh series gives
`log c ≥ 2 (c - 1)/(c + 1) = 158/2079`, and `log c ≤ c - 1 = 79/1000`. Hence
`a log c ≥ 164083/1155000 ≥ 71/500` and `z = exp (a log c) ≥ 1 + 71/500 + (71/500)^2/2 ≥ 23/20`,
so `u_o = 1/(z - 1) ≤ 20/3` and, as `t ↦ t/(t - 1)^2` decreases on `(1, ∞)`,
`v_o = z log c/(z - 1)^2 ≤ (79/1000)(460/9) = 1817/450`. With `w_b = 15·10^6/164241 ≤ 105`,
$$18\,(u_{\mathrm o} L + v_{\mathrm o}) \le \Bigl(120 + \frac{49059}{36000}\Bigr) L \le 126\, L,$$
which gives `𝔐^ex_o(x) ≤ 126 B_F(o) x^{-a} L + 105 x^{-2} = 𝔐_o(x)`.

## Main results

* `CollatzPosDens.mxExactProfile_le_mxProfile`: `𝔐^ex_ι(x) ≤ 𝔐_ι(x)` for `n₀ ≤ x`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The lower bound `158/2079 ≤ log c_bt`, the first atanh partial sum at `c_bt = 1079/1000`. -/
private theorem mxExactProfileLe_log_lower : (158 / 2079 : ℝ) ≤ log (bootChainRatio : ℝ) := by
  have h := (log_mem_atanh_partialSum (y := (bootChainRatio : ℝ))
    (by rw [bootChainRatio_cast]; norm_num) 1).1
  rw [bootChainRatio_cast] at h ⊢
  norm_num at h ⊢
  linarith

/-- The upper bound `log c_bt ≤ 79/1000`, from `log y ≤ y - 1`. -/
private theorem mxExactProfileLe_log_upper : log (bootChainRatio : ℝ) ≤ 79 / 1000 := by
  have h := log_le_sub_one_of_pos (x := (bootChainRatio : ℝ)) (by exact_mod_cast bootChainRatio_pos)
  rw [bootChainRatio_cast] at h ⊢
  linarith

/-- The lower bound `23/20 ≤ c_bt ^ a_mx(o)`. -/
private theorem mxExactProfileLe_z_lower :
    (23 / 20 : ℝ) ≤ (bootChainRatio : ℝ) ^ (amix .o : ℝ) := by
  have hc0 : (0 : ℝ) < bootChainRatio := by exact_mod_cast bootChainRatio_pos
  rw [rpow_def_of_pos hc0]
  have hr : (71 / 500 : ℝ) ≤ log (bootChainRatio : ℝ) * (amix .o : ℝ) := by
    have := mxExactProfileLe_log_lower
    rw [amix_cast_o]
    nlinarith
  have h2 := quadratic_le_exp_of_nonneg (x := (71 / 500 : ℝ)) (by norm_num)
  have h3 := exp_le_exp.2 hr
  norm_num at h2
  linarith

/-- The exact chained profile is below the mixing profile: for every Fourier index `ι` and every
real `x ≥ n₀`, `𝔐^ex_ι(x) ≤ 𝔐_ι(x)`, where `𝔐^ex_ι` is the exact chained profile and `𝔐_ι` the
propagation mixing profile. -/
@[collatz_pos_dens "lem_mx_exact_profile_le"]
theorem mxExactProfile_le_mxProfile (ι : FIndex) {x : ℝ} (hx : (mxGateLevel : ℝ) ≤ x) :
    mxExactProfile ι x ≤ mxProfile ι x := by
  cases ι
  · have hL : (160 / 3 : ℝ) ≤ log x := le_log_of_two_pow_eighty_le hx
    have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast mxGateLevel_pos) hx
    have hz := mxExactProfileLe_z_lower
    have hlc0 := log_bootChainRatio_pos
    have hlc := mxExactProfileLe_log_upper
    set z := (bootChainRatio : ℝ) ^ (amix .o : ℝ) with hzdef
    have hz1 : 0 < z - 1 := by linarith
    have hu : bootU .o ≤ 20 / 3 := by
      rw [bootU_eq, ← hzdef, div_le_iff₀ hz1]; linarith
    -- `z/(z-1)^2 ≤ 460/9`, from `ζ (z-1)^2 - z (ζ-1)^2 = (z-ζ)(ζ z-1) ≥ 0` at `ζ = 23/20`
    have hzq : z / (z - 1) ^ 2 ≤ 460 / 9 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (sub_nonneg.2 hz) (by linarith : (0 : ℝ) ≤ 23 / 20 * z - 1)]
    have hv : bootV .o ≤ 1817 / 450 := by
      have e : bootV .o = z / (z - 1) ^ 2 * log (bootChainRatio : ℝ) := by
        rw [bootV_eq, ← hzdef]; ring
      rw [e]
      calc z / (z - 1) ^ 2 * log (bootChainRatio : ℝ) ≤ 460 / 9 * (79 / 1000) :=
            mul_le_mul hzq hlc hlc0.le (by norm_num)
        _ = 1817 / 450 := by norm_num
    have hw : (bootW : ℝ) ≤ 105 := by rw [bootW_cast]; norm_num
    have hcoef : 18 * (bootU .o * log x + bootV .o) ≤ 126 * log x := by
      nlinarith
    have hB := fourierPrefactor_nonneg .o
    have hp := (rpow_pos_of_pos hx0 (-(amix .o : ℝ))).le
    have hq := (rpow_pos_of_pos hx0 (-2 : ℝ)).le
    rw [mxExactProfile_eq, mxProfile_o]
    have h1 : fourierPrefactor .o * x ^ (-(amix .o : ℝ)) *
        (18 * (bootU .o * log x + bootV .o)) ≤
        fourierPrefactor .o * x ^ (-(amix .o : ℝ)) * (126 * log x) :=
      mul_le_mul_of_nonneg_left hcoef (mul_nonneg hB hp)
    have h2 : (bootW : ℝ) * x ^ (-2 : ℝ) ≤ 105 * x ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right hw hq
    linarith
  · exact le_of_eq rfl

end CollatzPosDens
