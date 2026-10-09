/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Monotone.MoRate
public import CollatzPosDens.Monotone.MoRateD1
public import CollatzPosDens.Monotone.MoRateTiny
public import CollatzPosDens.Renewal.RnMgf
public import CollatzPosDens.Renewal.RnMgfBound
public import CollatzPosDens.Transfer.Aexp
public import CollatzPosDens.Transfer.D1
public import CollatzPosDens.Transfer.Dexp
public import CollatzPosDens.Transfer.W
public import CollatzPosDens.Transfer.DexpMargin

/-!
# The moment threshold for the near-top case

Let `m` be a natural number with `D1 ≤ m` and `Dexp ≤ m`. Then for every `s : ℕ` with
`s ≤ m / (log m)²`, `mgfNu45 (moRate Aexp m) ^ (s + 1) ≤ 1 + wStar / 8`.

Put `U = log m` and `t = moRate Aexp m`. The bound `Dexp ≤ m` gives `234 Aexp < wStar U`, hence
`U > 234`; the bound `D1 ≤ m` gives `0 ≤ t ≤ wStar / 32`, so `mgfNu45 t ≤ e^{13t/4}`. Since
`8 t (s + 1) ≤ 8 t (m / U² + 1) ≤ 36 Aexp / U`, one gets `13 t (s + 1) / 4 ≤ wStar / 16`, and
`e^y ≤ 1 + 2y` for `0 ≤ y ≤ 1/2`.

## Main results

* `CollatzPosDens.mgfNu45_moRate_pow_le`: `mgfNu45 (moRate Aexp m) ^ (s + 1)` is at most
  `1 + wStar / 8`.

## Implementation notes

`mgfNu45` takes values in `ℝ≥0∞`, so the bound is stated as `≤ ofReal (1 + wStar / 8)`. The
comparisons `D1 ≤ m` and `s ≤ m / (log m)²` are made in `ℝ`.

## References

* [Mazur, *Collatz positive density*], §8.4.
-/

@[expose] public section

namespace CollatzPosDens

open Real ENNReal

/-- If `D1 ≤ m`, `Dexp ≤ m` and `s ≤ m / (log m)²`, then
`mgfNu45 (moRate Aexp m) ^ (s + 1) ≤ 1 + wStar / 8`. -/
@[collatz_pos_dens "lem_mo_moment_threshold"]
theorem mgfNu45_moRate_pow_le {m : ℕ} (hm₁ : (D1 : ℝ) ≤ m) (hmexp : Dexp ≤ m) {s : ℕ}
    (hs : (s : ℝ) ≤ m / Real.log m ^ 2) :
    mgfNu45 (moRate Aexp m) ^ (s + 1) ≤ ENNReal.ofReal (1 + (wStar : ℝ) / 8) := by
  set A : ℝ := (Aexp : ℝ) with hAdef
  set w : ℝ := (wStar : ℝ) with hwdef
  set U := Real.log m with hUdef
  set t := moRate A m with htdef
  have hA : A = 10241 / 4096 := Aexp_cast
  have hw : w = 63 / 2500 := wStar_cast
  have hmargin : 234 * A < w * U := Dexp_margin (by exact_mod_cast hmexp)
  have hU : 234 < U := by rw [hA, hw] at hmargin; nlinarith
  have hD1 : (256 * A / w) ^ 2 + 2 ≤ (m : ℝ) := by
    have : (D1 : ℝ) = (256 * A / w) ^ 2 + 2 := by rw [D1_def]; push_cast; rfl
    linarith
  have ht0 : 0 ≤ t := moRate_nonneg (by rw [hA]; norm_num) m
  have ht1 : t ≤ w / 32 :=
    moRate_le_div_thirtyTwo (by rw [hA]; norm_num) (by rw [hw]; norm_num) hD1
  have htiny : 8 * t * (m / U ^ 2 + 1) ≤ 36 * A / U :=
    moRate_tiny (by rw [hA]; norm_num) (by linarith)
  have hU0 : 0 < U := by linarith
  have hy : 13 * t / 4 * ((s + 1 : ℕ) : ℝ) ≤ w / 16 := by
    have h8 : 8 * t * ((s + 1 : ℕ) : ℝ) ≤ 36 * A / U := by
      push_cast
      exact le_trans (by gcongr) htiny
    have h36 : 36 * A / U * 13 / 32 ≤ w / 16 := by
      have : 36 * A / U * 13 / 32 = 117 * A / (8 * U) := by field_simp; ring
      rw [this, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  have hexp : exp (w / 16) ≤ 1 + w / 8 := by
    have h1 := add_one_le_exp (-(w / 16))
    have hu : exp (w / 16) * exp (-(w / 16)) = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
    rw [hw] at h1 hu ⊢
    nlinarith [exp_pos ((63 / 2500 : ℝ) / 16)]
  calc mgfNu45 t ^ (s + 1) ≤ ENNReal.ofReal (exp (13 * t / 4)) ^ (s + 1) := by
        gcongr
        exact mgfNu45_le_exp ht0 (by rw [hw] at ht1; linarith)
    _ = ENNReal.ofReal (exp (13 * t / 4 * ((s + 1 : ℕ) : ℝ))) := by
        rw [← ENNReal.ofReal_pow (exp_pos _).le, ← exp_nat_mul]
        ring_nf
    _ ≤ ENNReal.ofReal (1 + w / 8) :=
        ENNReal.ofReal_le_ofReal ((exp_le_exp.2 hy).trans hexp)

end CollatzPosDens
