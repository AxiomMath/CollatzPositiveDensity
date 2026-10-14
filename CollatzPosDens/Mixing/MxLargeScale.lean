/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.MixingConst
public import CollatzPosDens.Mixing.MxChainRatio
public import CollatzPosDens.Mixing.MxHighRegime
public import CollatzPosDens.Mixing.MxOscTelescope

/-!
# Oscillation of the reference law at large scales

For integers `2 ^ 80000 ≤ m ≤ n`, the reference law `μ_n` has small oscillation at scale `m`:
$$\mathrm{Osc}_{m,n}(\mu_n) \le C\, m^{-3/2},$$
where `C = 477/20 · X_*^{A_*} + 159/10` is the mixing coefficient.

Write `B = 3 C_* 20^{A_*} + 2`, the constant of the high-regime bound. Since
`C_* = (160 D_*)^{A_*}`, one has `C_* 20^{A_*} = (3200 D_*)^{A_*} = X_*^{A_*}`, whence
`C = 159/20 · B`. The proof is by strong induction on `n - m`. Put `s = ⌊10 m / 9⌋`. If
`n ≤ s`, the pair `(m, n)` is in the high regime and
`Osc_{m,n}(μ_n) ≤ B n^{-3/2} ≤ B m^{-3/2}`.
Otherwise `m < s < n`, and telescoping through the scale `s` gives
`Osc_{m,n}(μ_n) ≤ Osc_{s,n}(μ_n) + Osc_{m,s}(μ_s) ≤ 179/20 · B s^{-3/2}` by the induction
hypothesis and the high regime. As `s ≥ a m` with `a = 99999/90000` and
`a^{-3/2} < 159/179`, this is at most `159/20 · B m^{-3/2}`.

## Main results

* `CollatzPosDens.mixingConst_eq_mul_highRegimeConst`: `C = 159/20 · (3 C_* 20^{A_*} + 2)`.
* `CollatzPosDens.oscillation_refLaw_le_mixingConst_of_two_pow_le`: the bound above.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The mixing coefficient is `159/20` times the high-regime constant:
`C = 159/20 · (3 C_* 20^{A_*} + 2)`. -/
theorem mixingConst_eq_mul_highRegimeConst :
    mixingConst = 159 / 20 * (3 * Cstar * 20 ^ (10241 / 4096 : ℝ) + 2) := by
  have hD : (0 : ℝ) ≤ Dstar := by exact_mod_cast Dstar_pos.le
  have h : Cstar * 20 ^ (10241 / 4096 : ℝ) = (Xstar : ℝ) ^ (Aexp : ℝ) := by
    rw [Cstar_def, ← Real.mul_rpow (by positivity) (by norm_num), cast_Xstar, Aexp_eq]
    push_cast
    ring_nf
  rw [mixingConst_def, ← h]
  ring

/-- If `99999 / 90000 * m ≤ s` with `0 < m`, then `s ^ (-3/2)` is at most
`(90000 / 99999) ^ (3/2) * m ^ (-3/2)`. -/
theorem rpow_neg_three_div_two_le_of_mul_le {m s : ℝ} (hm : 0 < m)
    (hsm : 99999 / 90000 * m ≤ s) :
    s ^ (-(3 / 2 : ℝ)) ≤ (90000 / 99999 : ℝ) ^ ((3 : ℝ) / 2) * m ^ (-(3 / 2 : ℝ)) :=
  calc s ^ (-(3 / 2 : ℝ)) ≤ (99999 / 90000 * m) ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hsm (by norm_num)
    _ = (90000 / 99999 : ℝ) ^ ((3 : ℝ) / 2) * m ^ (-(3 / 2 : ℝ)) := by
        rw [Real.mul_rpow (by norm_num) hm.le, Real.rpow_neg (by norm_num),
          ← Real.inv_rpow (by norm_num)]
        norm_num

/-- **Oscillation at large scales.** For integers `2 ^ 80000 ≤ m ≤ n`,
`Osc_{m,n}(μ_n) ≤ C m^{-3/2}`, with `C` the mixing coefficient. -/
@[collatz_pos_dens "lem_mx_large_scale"]
theorem oscillation_refLaw_le_mixingConst_of_two_pow_le {m n : ℕ} (hm : 2 ^ 80000 ≤ m)
    (hmn : m ≤ n) :
    oscillation hmn (fun y => (refLaw n y).toReal) ≤
      mixingConst * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
  rw [mixingConst_eq_mul_highRegimeConst]
  set B : ℝ := 3 * Cstar * 20 ^ (10241 / 4096 : ℝ) + 2 with hB
  have hB0 : 0 < B := by have := Cstar_pos; positivity
  induction h : n - m using Nat.strong_induction_on generalizing m n with
  | _ k ih =>
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by positivity) hm : 0 < m)
  have hm8 : 80000 ≤ m :=
    le_trans ((by norm_num : 80000 ≤ 2 ^ 17).trans
      (Nat.pow_le_pow_right (by norm_num) (by norm_num))) hm
  set s := 10 * m / 9 with hs
  by_cases hns : n ≤ s
  · have h9 : 9 * n ≤ 10 * m := by omega
    calc oscillation hmn (fun y => (refLaw n y).toReal)
        ≤ B * (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
          oscillation_refLaw_le_of_nine_mul_le (hm.trans hmn) hmn h9
      _ ≤ B * (m : ℝ) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hmpos
            (Nat.cast_le.mpr hmn) (by norm_num)) hB0.le
      _ ≤ 159 / 20 * B * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by
          have : 0 ≤ B * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
          linarith
  · push Not at hns
    have hms : m ≤ s := by omega
    have hsn : s ≤ n := hns.le
    have hs9 : 9 * s ≤ 10 * m := by omega
    have hsm : (99999 / 90000 : ℝ) * m ≤ s := by
      have h1 : (10 * m : ℝ) ≤ 9 * s + 8 := by exact_mod_cast (by omega : 10 * m ≤ 9 * s + 8)
      have h2 : (80000 : ℝ) ≤ m := by exact_mod_cast hm8
      linarith
    have hkey := ih (n - s) (by omega) (hm.trans hms) hsn rfl
    have hhigh := oscillation_refLaw_le_of_nine_mul_le (hm.trans hms) hms hs9
    have hpow := rpow_neg_three_div_two_le_of_mul_le hmpos hsm
    have hratio := mxChainRatio_lt
    calc oscillation hmn (fun y => (refLaw n y).toReal)
        ≤ oscillation hsn (fun y => (refLaw n y).toReal) +
            oscillation hms (fun x => (refLaw s x).toReal) :=
          oscillation_refLaw_le_add hms hsn
      _ ≤ 159 / 20 * B * (s : ℝ) ^ (-(3 / 2 : ℝ)) + B * (s : ℝ) ^ (-(3 / 2 : ℝ)) :=
          add_le_add hkey hhigh
      _ = 179 / 20 * B * (s : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
      _ ≤ 179 / 20 * B *
            ((90000 / 99999 : ℝ) ^ ((3 : ℝ) / 2) * (m : ℝ) ^ (-(3 / 2 : ℝ))) := by
          gcongr
      _ ≤ 179 / 20 * B * (159 / 179 * (m : ℝ) ^ (-(3 / 2 : ℝ))) := by
          gcongr
      _ = 159 / 20 * B * (m : ℝ) ^ (-(3 / 2 : ℝ)) := by ring

end CollatzPosDens
