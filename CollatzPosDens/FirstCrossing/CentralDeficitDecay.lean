/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.FcCapRate
public import CollatzPosDens.FirstCrossing.FcDeficitBound
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales

/-!
# Decay of the central deficit along the scale sequence

Along the scales `b_j` and caps `K_j`, the geometric deficit of the central family decays
geometrically: for every `j ∈ ℕ`,
$$1 - \mathbf p(\mathcal C(b_j, K_j)) \le \frac12\,\mathsf g^{-3j/2} + 2^{-29}\cdot 2^{-j/56}.$$

Write `c = 529/10⁶`. The deficit of the central families is at most `T₁ + T₂ + 2^{-(K_j+1)}`
with `T₁ = 2e^{-c(b_j-14)}` and `T₂ = 2b_j^{-3/2}`.

* Since `b_j - 14 ≥ 16530 + 166j`, `T₁ ≤ 2e^{-16530c} e^{-166cj}`. As `log 𝗀 ≤ 𝗀 - 1 = 1/100`
  and `166c ≥ 3/200`, `e^{-166cj} ≤ 𝗀^{-3j/2}`; and `e^{16530c} ≥ 1 + 16530c > 8`. Hence
  `T₁ ≤ ¼ 𝗀^{-3j/2}`.
* Since `b_j ≥ 16544 𝗀^j ≥ 2^{14} 𝗀^j`, `T₂ ≤ 2 · 2^{-21} 𝗀^{-3j/2} ≤ ¼ 𝗀^{-3j/2}`.
* The cap term is at most `2^{-29} · 2^{-j/56}` by `CollatzPosDens.two_zpow_neg_cap_succ_le`.

## Main results

* `CollatzPosDens.one_sub_geomMass_centralFamily_scale_cap_le_rpow`: the bound above.

## Implementation notes

As in `CollatzPosDens.one_sub_geomMass_centralFamily_le_exp_add_rpow`, the deficit is taken in
`ℝ≥0∞` (truncated subtraction), and the real right-hand side is embedded by `ENNReal.ofReal`.
The proof works with natural powers of the real number `𝗀^{-3/2}`. The source bounds the power
term using `16544^{3/2} ≥ 8`; the bound `16544^{-3/2} ≤ 2^{-21}` used here is stronger.

## References

* [Mazur, *Collatz positive density*], §14.6.
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- `e^{-166c} ≤ 𝗀^{-3/2}` for `c = 529/10⁶`, since `(3/2) log 𝗀 ≤ 3/200 ≤ 166c`. -/
private theorem centralDeficitDecay_rho_le :
    exp (-(529 / 10 ^ 6) * 166) ≤ (growthRatio : ℝ) ^ (-(3 / 2 : ℝ)) := by
  rw [Real.rpow_def_of_pos growthRatio_cast_pos]
  apply exp_le_exp.2
  have hlog : log (growthRatio : ℝ) ≤ 1 / 100 := by
    have := Real.log_le_sub_one_of_pos growthRatio_cast_pos
    rw [growthRatio_cast] at this ⊢
    linarith
  linarith

/-- `e^{-16530c} ≤ 1/8` for `c = 529/10⁶`, since `e^{16530c} ≥ 1 + 16530c > 8`. -/
private theorem centralDeficitDecay_exp_le : exp (-(529 / 10 ^ 6) * 16530) ≤ 1 / 8 := by
  have := Real.add_one_le_exp ((529 / 10 ^ 6) * 16530)
  rw [neg_mul, exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
  norm_num at this ⊢
  linarith

/-- **Decay of the central deficit.** For every `j ∈ ℕ`,
`1 - 𝐩(𝒞(b_j, K_j)) ≤ ½ 𝗀^{-3j/2} + 2^{-29} · 2^{-j/56}`. -/
@[collatz_pos_dens "lem_central_deficit_decay"]
theorem one_sub_geomMass_centralFamily_scale_cap_le_rpow (j : ℕ) :
    1 - geomMass (centralFamily (scale j) (cap j)) ≤
      ENNReal.ofReal (1 / 2 * (growthRatio : ℝ) ^ (-(3 * j / 2 : ℝ)) +
        (2 : ℝ) ^ (-29 : ℤ) * (2 : ℝ) ^ (-((j : ℝ) / 56))) := by
  refine (one_sub_geomMass_centralFamily_le_exp_add_rpow j).trans
    (ENNReal.ofReal_le_ofReal ?_)
  set ς := (growthRatio : ℝ) ^ (-(3 / 2 : ℝ))
  have hς0 : 0 ≤ ς := (Real.rpow_pos_of_pos growthRatio_cast_pos _).le
  have hrate : (growthRatio : ℝ) ^ (-(3 * j / 2 : ℝ)) = ς ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul growthRatio_cast_pos.le]
    ring_nf
  rw [hrate]
  have hςj : 0 ≤ ς ^ j := pow_nonneg hς0 j
  have h1 : 2 * exp (-(529 / 10 ^ 6) * ((scale j : ℝ) - 14)) ≤ 1 / 4 * ς ^ j := by
    have hρ : exp (-(529 / 10 ^ 6) * 166) ^ j ≤ ς ^ j :=
      pow_le_pow_left₀ (exp_pos _).le centralDeficitDecay_rho_le j
    have hE := centralDeficitDecay_exp_le
    have hE0 := (exp_pos (-(529 / 10 ^ 6) * 16530)).le
    have hρ0 : 0 ≤ exp (-(529 / 10 ^ 6) * 166) ^ j := pow_nonneg (exp_pos _).le j
    have := exp_neg_mul_scale_sub_fourteen_le j
    nlinarith [mul_le_mul hE hρ hρ0 (by norm_num)]
  have h2 : 2 * (scale j : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 1 / 4 * ς ^ j := by
    have := scale_rpow_neg_three_halves_le j
    nlinarith
  have h3 := two_zpow_neg_cap_succ_le j
  linarith

end CollatzPosDens
