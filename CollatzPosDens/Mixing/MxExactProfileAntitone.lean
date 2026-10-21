/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Transfer.MxExactProfile
public import CollatzPosDens.Mixing.MxShLogLower
public import CollatzPosDens.Mixing.MxShLogPowerAntitone

/-!
# The exact chained profile is antitone beyond the gate level

For each Fourier index `ι ∈ {o, b}`, the exact chained profile `𝔐^ex_ι`
(`CollatzPosDens.mxExactProfile ι`) is antitone on the ray $[n_0, \infty)$, where
$n_0 = 2^{80}$ is the mixing gate level `CollatzPosDens.mxGateLevel`.

For $x \ge 2^{80}$ we have $\log x \ge \frac{160}{3}$ and $a = a_{\mathrm{mx}}(\iota) \ge 1$, so
$a \log x \ge 1$ and the damped logarithm $t \mapsto t^{-a}\log t$ is antitone from $x$ on;
$t \mapsto t^{-a}$ and $t \mapsto t^{-2}$ are antitone on the positive reals. Writing
$$\mathfrak M^{\mathrm{ex}}_\iota(x) = 18 B_{\mathrm F}(\iota)\bigl(u_\iota x^{-a}\log x
  + v_\iota x^{-a}\bigr) + w_{\mathrm b} x^{-2},$$
the profile is a nonnegative combination of these three terms, since `B_F(ι) ≥ 0` and
`u_ι`, `v_ι`, `w_b` are positive.

## Main results

* `CollatzPosDens.mxExactProfile_antitoneOn`: for `n₀ ≤ x ≤ y`, `𝔐^ex_ι(y) ≤ 𝔐^ex_ι(x)`.
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- The exact chained profile is antitone beyond the gate level: for every Fourier index `ι` and
reals `n₀ ≤ x ≤ y`, `𝔐^ex_ι(y) ≤ 𝔐^ex_ι(x)`. -/
@[collatz_pos_dens "lem_mx_exact_profile_antitone"]
theorem mxExactProfile_antitoneOn (ι : FIndex) {x y : ℝ} (hx : (mxGateLevel : ℝ) ≤ x)
    (hxy : x ≤ y) : mxExactProfile ι y ≤ mxExactProfile ι x := by
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
  have hu := bootU_pos ι
  have hv := bootV_pos ι
  have hw : (0 : ℝ) ≤ bootW := by exact_mod_cast bootW_pos.le
  have e : ∀ t : ℝ, mxExactProfile ι t =
      18 * fourierPrefactor ι * (bootU ι * (t ^ (-(amix ι : ℝ)) * log t) +
        bootV ι * t ^ (-(amix ι : ℝ))) + (bootW : ℝ) * t ^ (-2 : ℝ) := by
    intro t; rw [mxExactProfile_eq]; ring
  rw [e, e]
  gcongr

end CollatzPosDens
