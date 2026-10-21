/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.MxProfile
public import CollatzPosDens.Transfer.S02Log2Bstar
public import CollatzPosDens.Mixing.MxShLogLower
public import CollatzPosDens.Recipe.PhBootUUpper
public import CollatzPosDens.Recipe.PhBootVUpper
public import CollatzPosDens.Transfer.MxBootW

/-!
# A power bound for the original propagation mixing profile

Beyond the mixing gate level `n₀ = 2^80`, the propagation mixing profile at the original Fourier
index, `𝔐_o(x) = 126 B_F(o) x^{-a} log x + 105 x^{-2}` with `a = a_mx(o) = 18693/10000`, is
bounded by a single power term:
$$\mathfrak M_{\mathrm o}(x) \le 2^{365}\, x^{-a_{\mathrm{mx}}(\mathrm o)} \log x.$$

Indeed `a ≤ 2` and `log x ≥ 160/3 ≥ 1`, so `x^{-2} ≤ x^{-a} ≤ x^{-a} log x`; the binary logarithm
of the Fourier prefactor satisfies `log₂ B_F(o) < 351`, so `B_F(o) < 2^351`, and
`126 · 2^351 + 105 ≤ 2^365`.

At the bootstrap index, `𝔐_b(x) = 18 B_F(b) x^{-a} (u_b log x + v_b) + w x^{-2}` with
`a = a_mx(b) = 29/20`, the same argument gives
$$\mathfrak M_{\mathrm b}(x) \le 2^{96}\, x^{-a_{\mathrm{mx}}(\mathrm b)} \log x.$$
Here `u_b < 8.5794562` and `v_b < 6.24902664`, so
`u_b log x + v_b ≤ (u_b + 3 v_b / 160) log x ≤ 8.7 log x` from `log x ≥ 160/3`, and
`log₂ B_F(b) < 88.1188851177` gives `B_F(b)^2 < 2^177`, hence `B_F(b) < 1.42 · 2^88`; finally,
with `w_b ≤ 92`, `18 · 8.7 · 1.42 · 2^88 + 92 ≤ 2^96`.

## Main results

* `CollatzPosDens.fourierPrefactor_o_lt_two_pow`: `B_F(o) < 2^351`.
* `CollatzPosDens.mxProfile_o_le_two_pow_mul`: for `x ≥ n₀`,
  `𝔐_o(x) ≤ 2^365 x^{-a_mx(o)} log x`.
* `CollatzPosDens.mxProfile_b_le_two_pow_mul`: for `x ≥ n₀`,
  `𝔐_b(x) ≤ 2^96 x^{-a_mx(b)} log x`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The Fourier prefactor at the original index is below `2^351`, from `log₂ B_F(o) < 351`. -/
theorem fourierPrefactor_o_lt_two_pow : fourierPrefactor .o < 2 ^ 351 := by
  have h := logb_two_fourierPrefactor_mem_o.2
  have h' : logb 2 (fourierPrefactor .o) < (351 : ℕ) := by
    push_cast; linarith [show (3257939550288 / 10 ^ 10 : ℝ) < 351 by norm_num]
  rw [logb_lt_iff_lt_rpow (by norm_num) (fourierPrefactor_pos .o), rpow_natCast] at h'
  exact h'

/-- A power bound for the original propagation mixing profile: for every real `x ≥ n₀`,
`𝔐_o(x) ≤ 2^365 x^{-a_mx(o)} log x`. -/
@[collatz_pos_dens "lem_mx_profile_power"]
theorem mxProfile_o_le_two_pow_mul {x : ℝ} (hx : (mxGateLevel : ℝ) ≤ x) :
    mxProfile .o x ≤ 2 ^ 365 * x ^ (-(amix .o : ℝ)) * log x := by
  have hlog : (160 / 3 : ℝ) ≤ log x := le_log_of_two_pow_eighty_le hx
  replace hx : (2 : ℝ) ^ 80 ≤ x := by rw [mxGateLevel_def, Nat.cast_pow] at hx; exact_mod_cast hx
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hlog1 : 1 ≤ log x := le_trans (by norm_num) hlog
  set t : ℝ := x ^ (-(amix .o : ℝ)) with ht
  have ht0 : 0 ≤ t := rpow_nonneg hx0.le _
  have ha2 : (amix .o : ℝ) ≤ 2 := by exact_mod_cast (amix_lt_two .o).le
  have h2 : x ^ (-2 : ℝ) ≤ t := rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have htL : t ≤ t * log x := le_mul_of_one_le_right ht0 hlog1
  have hB := fourierPrefactor_o_lt_two_pow
  have hB0 := fourierPrefactor_nonneg .o
  -- `2^365 = 2^14 · 2^351` and `105 ≤ 2^7 ≤ 2^351`, without evaluating the large powers
  have hc : 126 * fourierPrefactor .o + 105 ≤ (2 : ℝ) ^ 365 := by
    have hsplit : (2 : ℝ) ^ 365 = 2 ^ 14 * 2 ^ 351 := by rw [← pow_add]
    have h105 : (105 : ℝ) ≤ 2 ^ 351 :=
      le_trans (by norm_num : (105 : ℝ) ≤ 2 ^ 7) (pow_le_pow_right₀ (by norm_num) (by norm_num))
    rw [hsplit]
    generalize (2 : ℝ) ^ 351 = P at hB h105 ⊢
    norm_num
    linarith
  have htL0 : 0 ≤ t * log x := mul_nonneg ht0 (by linarith)
  rw [mxProfile_o, ← ht]
  calc 126 * fourierPrefactor .o * t * log x + 105 * x ^ (-2 : ℝ)
      ≤ 126 * fourierPrefactor .o * t * log x + 105 * (t * log x) := by gcongr; linarith
    _ = (126 * fourierPrefactor .o + 105) * (t * log x) := by ring
    _ ≤ 2 ^ 365 * (t * log x) := mul_le_mul_of_nonneg_right hc htL0
    _ = 2 ^ 365 * t * log x := (mul_assoc _ _ _).symm

/-- A power bound for the bootstrap propagation mixing profile: for every real `x ≥ n₀`,
`𝔐_b(x) ≤ 2^96 x^{-a_mx(b)} log x`. -/
theorem mxProfile_b_le_two_pow_mul {x : ℝ} (hx : (mxGateLevel : ℝ) ≤ x) :
    mxProfile .b x ≤ 2 ^ 96 * x ^ (-(amix .b : ℝ)) * log x := by
  have hlog : (160 / 3 : ℝ) ≤ log x := le_log_of_two_pow_eighty_le hx
  replace hx : (2 : ℝ) ^ 80 ≤ x := by rw [mxGateLevel_def, Nat.cast_pow] at hx; exact_mod_cast hx
  have hx1 : 1 ≤ x := le_trans (by norm_num) hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx1
  have hlog1 : 1 ≤ log x := le_trans (by norm_num) hlog
  set t : ℝ := x ^ (-(amix .b : ℝ)) with ht
  have ht0 : 0 ≤ t := rpow_nonneg hx0.le _
  have ha2 : (amix .b : ℝ) ≤ 2 := by exact_mod_cast (amix_lt_two .b).le
  have h2 : x ^ (-2 : ℝ) ≤ t := rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have htL : t ≤ t * log x := le_mul_of_one_le_right ht0 hlog1
  have htL0 : 0 ≤ t * log x := mul_nonneg ht0 (by linarith)
  obtain ⟨hu0, hu⟩ := bootU_mem_Ioo
  obtain ⟨hv0, hv⟩ := bootV_mem_Ioo
  have hB0 := fourierPrefactor_pos .b
  -- the linear factor: `u log x + v ≤ (u + 3 v / 160) log x ≤ 8.7 log x`
  have huv : bootU .b * log x + bootV .b ≤ 87 / 10 * log x := by
    have : bootV .b ≤ 3 / 160 * bootV .b * log x := by
      have := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 3 / 160 * bootV .b)
      linarith
    nlinarith
  -- `B_F(b)^2 < 2^177 = 2 (2^88)^2`, from `log₂ B_F(b) < 88.1188851177`
  have hB2 : fourierPrefactor .b ^ 2 < 2 * ((2 : ℝ) ^ 88) ^ 2 := by
    have h := logb_two_fourierPrefactor_mem_b.2
    have h' : logb 2 (fourierPrefactor .b ^ 2) < (177 : ℕ) := by
      rw [logb_pow]; push_cast
      linarith [show (881188851177 / 10 ^ 10 : ℝ) < 177 / 2 by norm_num]
    rw [logb_lt_iff_lt_rpow (by norm_num) (by positivity), rpow_natCast] at h'
    rw [← pow_mul, ← pow_succ']
    exact h'
  have hP92 : (92 : ℝ) ≤ 2 ^ 88 :=
    le_trans (by norm_num : (92 : ℝ) ≤ 2 ^ 7) (pow_le_pow_right₀ (by norm_num) (by norm_num))
  have hw : (bootW : ℝ) ≤ 92 := by rw [bootW_cast]; norm_num
  have hw0 : (0 : ℝ) ≤ bootW := by rw [bootW_cast]; norm_num
  -- `2^96 = 2^8 · 2^88`, without evaluating the large powers
  have hc : 18 * fourierPrefactor .b * (87 / 10) + bootW ≤ (2 : ℝ) ^ 96 := by
    have hsplit : (2 : ℝ) ^ 96 = 2 ^ 8 * 2 ^ 88 := by rw [← pow_add]
    rw [hsplit]
    generalize (2 : ℝ) ^ 88 = P at hB2 hP92 ⊢
    have hB : fourierPrefactor .b ≤ 142 / 100 * P := by nlinarith
    norm_num
    linarith
  rw [mxProfile_b, ← ht]
  calc 18 * fourierPrefactor .b * t * (bootU .b * log x + bootV .b) + bootW * x ^ (-2 : ℝ)
      ≤ 18 * fourierPrefactor .b * t * (87 / 10 * log x) + bootW * (t * log x) := by
        gcongr; linarith
    _ = (18 * fourierPrefactor .b * (87 / 10) + bootW) * (t * log x) := by ring
    _ ≤ 2 ^ 96 * (t * log x) := mul_le_mul_of_nonneg_right hc htL0
    _ = 2 ^ 96 * t * log x := (mul_assoc _ _ _).symm

end CollatzPosDens
