/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.MxProfile
public import CollatzPosDens.Mixing.MxShLogLower
public import CollatzPosDens.Mixing.MxShLogPowerAntitone

/-!
# The propagation mixing profiles are antitone beyond the gate level

For each Fourier index `ι ∈ {o, b}`, the propagation mixing profile `𝔐_ι` is antitone on the ray
$[n_0, \infty)$, where $n_0 = 2^{80}$ is the mixing gate level.

For $x \ge 2^{80}$ we have $\log x \ge \frac{160}{3}$ and $a_{\mathrm{mx}}(ι) \ge 1$, so
$a_{\mathrm{mx}}(ι) \log x \ge 1$ and the damped logarithm
$x \mapsto x^{-a_{\mathrm{mx}}(ι)}\log x$ is antitone from $x$ on;
$x \mapsto x^{-a_{\mathrm{mx}}(ι)}$ and $x \mapsto x^{-2}$ are antitone on the positive reals. Each
profile is a nonnegative combination of these terms: the coefficients `B_F(ι)`, `u_b`, `v_b`, `w_b`
are positive.

## Main results

* `CollatzPosDens.mxProfile_antitoneOn`: for `n₀ ≤ x ≤ y`, `𝔐_ι(y) ≤ 𝔐_ι(x)`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The propagation mixing profiles are antitone beyond the gate level: for every index `ι` and
reals `n₀ ≤ x ≤ y`, `𝔐_ι(y) ≤ 𝔐_ι(x)`. -/
@[collatz_pos_dens "lem_mx_profile_antitone"]
theorem mxProfile_antitoneOn (ι : FIndex) {x y : ℝ} (hx : (mxGateLevel : ℝ) ≤ x)
    (hxy : x ≤ y) : mxProfile ι y ≤ mxProfile ι x := by
  have hlog : (160 / 3 : ℝ) ≤ log x := le_log_of_two_pow_eighty_le hx
  replace hx : (2 : ℝ) ^ 80 ≤ x := by rw [mxGateLevel_def, Nat.cast_pow] at hx; exact_mod_cast hx
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num) hx
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have ha1 : (1 : ℝ) ≤ amix ι := by exact_mod_cast (one_lt_amix ι).le
  have hεx : 1 ≤ (amix ι : ℝ) * log x := by nlinarith
  have h1 : y ^ (-(amix ι : ℝ)) * log y ≤ x ^ (-(amix ι : ℝ)) * log x :=
    rpow_neg_mul_log_le_of_one_le_mul_log hx1 hxy hεx
  have h2 : y ^ (-2 : ℝ) ≤ x ^ (-2 : ℝ) :=
    rpow_le_rpow_of_nonpos hx0 hxy (by norm_num)
  have h3 : y ^ (-(amix ι : ℝ)) ≤ x ^ (-(amix ι : ℝ)) :=
    rpow_le_rpow_of_nonpos hx0 hxy (by linarith)
  have hB := fourierPrefactor_nonneg ι
  cases ι
  · rw [mxProfile_o, mxProfile_o, mul_assoc (126 * fourierPrefactor .o),
      mul_assoc (126 * fourierPrefactor .o)]
    gcongr
  · have hu := bootU_pos .b
    have hv := bootV_pos .b
    have hw : (0 : ℝ) ≤ bootW := by exact_mod_cast bootW_pos.le
    have e : ∀ z : ℝ, mxProfile .b z =
        18 * fourierPrefactor .b * (bootU .b * (z ^ (-(amix .b : ℝ)) * log z) +
          bootV .b * z ^ (-(amix .b : ℝ))) + (bootW : ℝ) * z ^ (-2 : ℝ) := by
      intro z; rw [mxProfile_b]; ring
    rw [e, e]
    gcongr

end CollatzPosDens
