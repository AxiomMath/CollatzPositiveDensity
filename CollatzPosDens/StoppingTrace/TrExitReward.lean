/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrGapNonneg
public import CollatzPosDens.StoppingTrace.TrPacketBound
public import CollatzPosDens.StoppingTrace.TrPacketRange
public import CollatzPosDens.CharSum.ChOddDyadicExitStrip
public import CollatzPosDens.CharSum.ChOddDyadicExit
public import CollatzPosDens.CharSum.ChPaidRewardCap
public import CollatzPosDens.BlackSet.BkExitWidthBound

/-!
# The reward at an exit point

Fix a level `n`, a unit `ξ ∈ G_n` and the colour scale `ε_*`, and write `R_c(p)` for the paid
reward. Let `v ∈ 𝒫` be black with gap `s = gap(v)`, and let `r, c, o` be integers with
`r ≤ f_s` (the exit width), `3 ≤ c ≤ 16` and `o ≥ 1`. Then
```
exp(-z_* R_c(v + (r, s + o))) ≤ 1 - δ^{pk}_{c,o}.
```
Indeed `s ≥ 0` and `l(v) + s = l_Δ` for the canonical triangle `Δ = Δ(v)`, so
`y := v + (r, s + o) = (j(v) + r, l_Δ + o)`. The odd dyadic exit gives `j(y) ≤ ⌊n/2⌋` and
`ϑ(y) = (b + β) / 2^o` with `b` odd and `|β| ≤ 9^r ε_* 2^{-s} < 1/3`, by the exit-width bound
`3 ε_* 9^r < 2^s`. The paid-reward cap gives `e^{-z_* R_c(y)} ≤ max (φ_c(y), 2^{-16})` with
`φ_c(y) = Φ_{c-1}(ϑ(y))`, the packet bound gives `Φ_{c-1}(ϑ(y)) ≤ 1 - δ^{pk}_{c,o}`, and
`2^{-16} < 1/2 ≤ 1 - δ^{pk}_{c,o}` since `δ^{pk}_{c,o} ≤ 1/2`.

## Main results

* `CollatzPosDens.exp_neg_zStar_mul_chPaidReward_le_one_sub_trPacketDeficit`:
  `exp(-z_* R_c(v + (r, gap(v) + o))) ≤ 1 - δ^{pk}_{c,o}`.

## Implementation notes

The bounds `1 ≤ r` and `o ≤ c` are not needed: the statement holds for every `r ∈ ℕ` with
`r ≤ f_s` and every `o ≥ 1`.
The gap is an integer; the exit width is evaluated at its natural-number value
`gap(v).toNat`, which equals `gap(v)` because the gap is nonnegative.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **The reward at an exit point.** Let `ξ` be a unit, `v ∈ 𝒫` black at the colour scale
`ε_*`, `s = gap(v)`, `r ≤ f_s`, `3 ≤ c ≤ 16` and `o ≥ 1`. Then
`exp(-z_* R_c(v + (r, s + o))) ≤ 1 - δ^{pk}_{c,o}`. -/
@[collatz_pos_dens "lem_tr_exit_reward"]
theorem exp_neg_zStar_mul_chPaidReward_le_one_sub_trPacketDeficit {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) v)
    {r : ℕ} (hr : r ≤ bkExitWidth (trGap n ξ (epsStar : ℝ) v).toNat) {c o : ℕ}
    (hc₁ : 3 ≤ c) (hc₂ : c ≤ 16) (ho : 1 ≤ o) :
    Real.exp (-(zStar : ℝ) * chPaidReward n ξ (epsStar : ℝ) c
        (v + ((r : ℤ), trGap n ξ (epsStar : ℝ) v + o))) ≤
      1 - (trPacketDeficit c o : ℝ) := by
  obtain ⟨hε₀, hε⟩ := epsStar_mem_bkRange (K := ℝ)
  set s := (trGap n ξ (epsStar : ℝ) v).toNat with hs_def
  have hs : (s : ℤ) = trGap n ξ (epsStar : ℝ) v := Int.toNat_of_nonneg (trGap_nonneg ..)
  have hω : bkL v + s = (bkCanonTriangle n ξ (epsStar : ℝ) v hv).l := by
    rw [bkCanonTriangle_l, bkColTop_eq_add_trGap, hs]
  have hy : v + ((r : ℤ), trGap n ξ (epsStar : ℝ) v + o) =
      (bkJ v + r, (bkCanonTriangle n ξ (epsStar : ℝ) v hv).l + o) := by
    rw [← hω, ← hs]
    ext
    · simp [bkJ]
    · simp [bkL]; ring
  rw [hy]
  have hJ := bkJ_add_le_of_le_bkExitWidth hξ hε₀ hε hv hb hω hr
  obtain ⟨b, hbodd, β, hβ, hθ⟩ := exists_odd_bkTheta_dyadic_exit hξ hε₀ hε hv hb s hω r o ho
  have hβ3 : |β| ≤ 1 / 3 := by
    have hw := three_mul_epsStar_mul_nine_pow_lt (K := ℝ) hr
    have h2 : (0 : ℝ) < 2 ^ s := by positivity
    have hz : (2 : ℝ) ^ (-(s : ℤ)) = 1 / 2 ^ s := by rw [zpow_neg, zpow_natCast, one_div]
    rw [hz] at hβ
    refine hβ.trans ?_
    rw [mul_one_div, div_le_iff₀ h2]
    linarith
  have hcap := exp_neg_zStar_mul_chPaidReward_le (n := n) (ξ := ξ) (ε := (epsStar : ℝ))
    (c := (c : ℤ)) (p := (bkJ v + r, (bkCanonTriangle n ξ (epsStar : ℝ) v hv).l + o))
    (by exact_mod_cast hc₁) (by exact_mod_cast hc₂) hJ
  refine hcap.trans (max_le ?_ ?_)
  · rw [chRawFactor_of_two_le n ξ (by omega)]
    have hct : ((c : ℤ) - 1).toNat = c - 1 := by omega
    rw [hct]
    exact chPacketFn_le_one_sub_trPacketDeficit c o hbodd hβ3 ⟨0, by rw [hθ]; simp⟩
  · have hd := (trPacketDeficit_mem_Icc c o).2
    have hd' : (trPacketDeficit c o : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := Rat.cast_le.2 hd
    have h16 : (2 : ℝ) ^ (-16 : ℤ) = 1 / 65536 := by norm_num
    rw [h16]
    have : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by norm_num
    linarith

end CollatzPosDens
