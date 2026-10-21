/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.SyrPeriodic
public import CollatzPosDens.Seed.Zn
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.CovGen
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Recipe.TargetExp
public import CollatzPosDens.Recipe.TailMargin
public import CollatzPosDens.Recipe.ZMargin
public import CollatzPosDens.Recipe.CountExp
public import CollatzPosDens.Terminal.AdmissibleScale
public import CollatzPosDens.Terminal.UnweightedMass
public import CollatzPosDens.Terminal.MarkLower
public import CollatzPosDens.Terminal.S06CountGate
public import CollatzPosDens.Terminal.S06CountHeight
public import CollatzPosDens.Terminal.S06CountAllowance
public import CollatzPosDens.Terminal.S06CountRoot
public import CollatzPosDens.Terminal.S06CountPower
public import CollatzPosDens.Terminal.S06ClipCensus

/-!
# Lower bound for the unweighted mass

Let `t ≥ t_min` (`targetFloor`) be an odd integer that is not Syracuse-periodic, with
`Z_{N_*}(t) > θ_tl + ε_Z` (`tailMargin + centralSumMargin`), let `j ≥ J_c` (`covGen`), and let
`X` be admissible for generation `j`. Then the unweighted mass satisfies
`Υ_{j,X}(t) > 2^{-λ_U} t^{1-κ_t}`, where `λ_U = countExp = 207` and `κ_t = targetExp = 25/11`.

Since `j ≥ J_c = 23000`, the marked mass satisfies `Θ_{j,X}(t) > 2^{-29}`. With the count
level `n = n_ct(t)` and height `B = B_ct(t) = 2^{52} t √(n log n) > 0`, the finite-profile census
and the count allowance give `2^{-29} < Θ_{j,X}(t) < (2/3) B Υ_{j,X}(t) + 2^{-32}`, whence
`B Υ_{j,X}(t) > 2^{-30}`. The count root and count power bounds give
`B < 2^{177} t^{1 + 5000/18693 + 1079/205623} = 2^{177} t^{14/11}`, so that
`Υ_{j,X}(t) > 2^{-207} t^{-14/11} = 2^{-207} t^{1-25/11}`.

## Main results

* `CollatzPosDens.countHeight_lt`: `B_ct(t) < 2^{177} t^{14/11}` for `t ≥ 1`.
* `CollatzPosDens.markedMass_le_census_short`:
  `Θ_{j,X}(t) ≤ 2^{177} t^{14/11} Υ_{j,X}(t) + 2^{-32}`.
* `CollatzPosDens.lt_unweightedMass_of_goodSeed`: `2^{-λ_U} t^{1-κ_t} < Υ_{j,X}(t)`.

## Implementation notes

The power `t^{1-κ_t}` is the real power `(t : ℝ) ^ (1 - (targetExp : ℝ))`.

## References

* [Mazur, *Collatz positive density*].
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Count height bound**. For every integer `t ≥ 1`, the clipping height satisfies
`B_ct(t) < 2^{177} t^{14/11}`. -/
@[collatz_pos_dens "lem_count_height"]
theorem countHeight_lt {t : ℕ} (ht : 1 ≤ t) :
    countHeight t < 2 ^ 177 * (t : ℝ) ^ (14 / 11 : ℝ) := by
  have htR : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htR0 : (0 : ℝ) < t := by linarith
  have hroot := sqrt_countLevel_mul_log_lt ht
  have hpow := one_add_log_rpow_lt htR
  have ha0 : 0 < (t : ℝ) ^ (5000 / 18693 : ℝ) := rpow_pos_of_pos htR0 _
  have e : (t : ℝ) ^ (14 / 11 : ℝ) =
      t * ((t : ℝ) ^ (5000 / 18693 : ℝ) * (t : ℝ) ^ (1079 / 205623 : ℝ)) := by
    rw [← rpow_add htR0, show (14 / 11 : ℝ) = 1 + (5000 / 18693 + 1079 / 205623) by norm_num,
      rpow_add htR0, rpow_one]
  rw [countHeight_def, e]
  calc 2 ^ 52 * (t : ℝ) * √((countLevel t : ℝ) * Real.log (countLevel t))
      < 2 ^ 52 * (t : ℝ) * (2 ^ 117 * (t : ℝ) ^ (5000 / 18693 : ℝ) *
          (1 + Real.log t) ^ (28693 / 37386 : ℝ)) := by gcongr
    _ < 2 ^ 52 * (t : ℝ) * (2 ^ 117 * (t : ℝ) ^ (5000 / 18693 : ℝ) *
          (2 ^ 8 * (t : ℝ) ^ (1079 / 205623 : ℝ))) := by gcongr
    _ = 2 ^ 177 * (t * ((t : ℝ) ^ (5000 / 18693 : ℝ) * (t : ℝ) ^ (1079 / 205623 : ℝ))) := by
        ring

/-- **Short census bound**. Let `t ≥ t_min` be an odd integer that is not Syracuse-periodic, and
let `X` be admissible for generation `j`. Then
`Θ_{j,X}(t) ≤ 2^{177} t^{14/11} Υ_{j,X}(t) + 2^{-32}`. -/
@[collatz_pos_dens "lem_census_short"]
theorem markedMass_le_census_short {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t)
    (hper : ¬ SyrPeriodic t) {j : ℕ} {X : ℝ} (hX : IsAdmissibleScale t j X) :
    markedMass j X t ≤ 2 ^ 177 * (t : ℝ) ^ (14 / 11 : ℝ) * unweightedMass j X t +
      2 ^ (-32 : ℤ) := by
  have ht1 : 1 ≤ t := le_trans (Nat.one_le_iff_ne_zero.2 targetFloor_pos.ne') ht
  have hB0 : 0 < countHeight t := by
    have hn0 : (0 : ℝ) < countLevel t := by exact_mod_cast countLevel_pos ht1
    have hL0 : 0 < Real.log (countLevel t) := log_countLevel_pos ht1
    have hsq0 := Real.sqrt_pos.2 (mul_pos hn0 hL0)
    rw [countHeight_def]; positivity
  have hcen := markedMass_le_clipCensus hodd ht hper hX (mxGateLevel_le_countLevel ht1) hB0
  have hall := countAllowance_lt ht1
  rw [show ((countLevel t : ℝ) ^ (-8 : ℤ)) = ((countLevel t : ℝ) ^ 8)⁻¹ by
    rw [zpow_neg, zpow_ofNat]] at hall
  have hU := unweightedMass_nonneg j X t
  have hBlt := countHeight_lt ht1
  refine hcen.trans (add_le_add (mul_le_mul_of_nonneg_right ?_ hU) hall.le)
  linarith

/-- **Unweighted mass lower bound**. Let `t ≥ t_min` be an odd integer that is not
Syracuse-periodic, with `Z_{N_*}(t) > θ_tl + ε_Z`, let `j ≥ J_c`, and let `X` be admissible for
generation `j`. Then `Υ_{j,X}(t) > 2^{-λ_U} t^{1-κ_t}` (positive real power). -/
@[collatz_pos_dens "lem_U_lower"]
theorem lt_unweightedMass_of_goodSeed {t : ℕ} (hodd : Odd t) (ht : targetFloor ≤ t)
    (hper : ¬ SyrPeriodic t)
    (hZ : (tailMargin : ℝ) + centralSumMargin < weightedCentralSum generationThreshold t)
    {j : ℕ} (hj : covGen ≤ j) {X : ℝ} (hX : IsAdmissibleScale t j X) :
    (2 : ℝ) ^ (-(countExp : ℤ)) * (t : ℝ) ^ (1 - (targetExp : ℝ)) <
      unweightedMass j X t := by
  have htR0 : (0 : ℝ) < t := by
    exact_mod_cast lt_of_lt_of_le targetFloor_pos ht
  have hΘ : (2 : ℝ) ^ (-29 : ℤ) < markedMass j X t := by
    have := two_zpow_neg_twentyNine_lt_markedMass (t := (t : ℤ)) (by exact_mod_cast hodd)
      (by exact_mod_cast ht) (by simpa using hZ) hj (by simpa using hX)
    simpa using this
  have hcen := markedMass_le_census_short hodd ht hper hX
  set U := unweightedMass j X t
  set Q : ℝ := (t : ℝ) ^ (14 / 11 : ℝ)
  set C : ℝ := (2 : ℝ) ^ 177
  have hCQ : 0 < C * Q := by positivity
  have hCQU : (2 : ℝ) ^ (-30 : ℤ) < C * Q * U := by
    have e29 : (2 : ℝ) ^ (-29 : ℤ) = 8 * 2 ^ (-32 : ℤ) := by norm_num
    have e30 : (2 : ℝ) ^ (-30 : ℤ) = 4 * 2 ^ (-32 : ℤ) := by norm_num
    have hp : (0 : ℝ) < 2 ^ (-32 : ℤ) := by positivity
    have key := hΘ.trans_le hcen
    rw [e29] at key
    rw [e30]
    generalize (2 : ℝ) ^ (-32 : ℤ) = x at *
    generalize C * Q * U = y at *
    linarith
  have hT : (t : ℝ) ^ (1 - (targetExp : ℝ)) * Q = 1 := by
    rw [← rpow_add htR0, targetExp_cast, show (1 - 25 / 11 + 14 / 11 : ℝ) = 0 by norm_num,
      rpow_zero]
  rw [countExp_def]
  have hc : (2 : ℝ) ^ (-((207 : ℕ) : ℤ)) * C = 2 ^ (-30 : ℤ) := by
    rw [show C = (2 : ℝ) ^ (177 : ℕ) from rfl, ← zpow_natCast (2 : ℝ) 177,
      ← zpow_add₀ two_ne_zero]
    norm_num
  have hlt : (2 : ℝ) ^ (-((207 : ℕ) : ℤ)) * (t : ℝ) ^ (1 - (targetExp : ℝ)) * (C * Q) <
      U * (C * Q) := by
    calc _ = (2 : ℝ) ^ (-((207 : ℕ) : ℤ)) * C * ((t : ℝ) ^ (1 - (targetExp : ℝ)) * Q) := by ring
      _ = 2 ^ (-30 : ℤ) := by rw [hc, hT, mul_one]
      _ < C * Q * U := hCQU
      _ = U * (C * Q) := by ring
  exact lt_of_mul_lt_mul_right hlt hCQ.le

end CollatzPosDens
