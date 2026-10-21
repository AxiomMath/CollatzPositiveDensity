/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChOldReward
public import CollatzPosDens.CharSum.ChRawFactor
public import CollatzPosDens.CharSum.ChWhiteCancel
public import CollatzPosDens.CharSum.ChWhiteCancelFour
public import CollatzPosDens.CharSum.ChWhiteCancelFive
public import CollatzPosDens.CharSum.ChPacketBound
public import CollatzPosDens.CharSum.ChExpQuadratic

/-!
# The raw factor is bounded by the baseline paid reward

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε ≥ ε_*`. For every integer `c` and every
point `p ∈ 𝒫`, the raw factor satisfies `φ_c(p) ≤ exp(-z_* R^old_c(p))`.

When the reward vanishes this is `φ_c(p) ≤ 1`. For `c ∈ {3, 4, 5}` and `p` white it is the
cancellation at a white closing letter. In the remaining cases one splits off disjoint packets
`(k, t)` with `p - (0, k)` white and `t + 1 ∈ {4, 5}`: the packet bound gives
`n_c φ_c(p) ≤ n_c - M + M e^{-z_*}` with `n_c = c - 1`, and
`1 - a (1 - e^{-z}) ≤ 1 - z a (1 - z/2) ≤ exp(-z a (1 - z/2))` for `a ≥ 0`, `z ≥ 0`.

## Main results

* `CollatzPosDens.one_sub_mul_one_sub_exp_neg_le`: `1 - a(1 - e^{-z}) ≤ exp(-z a (1 - z/2))`.
* `CollatzPosDens.chRawFactor_le_exp_neg_chOldReward`: `φ_c(p) ≤ exp(-z_* R^old_c(p))`.

## References

* [Mazur, *Collatz positive density*], §5.
-/

@[expose] public section

namespace CollatzPosDens

/-- For `a ≥ 0` and `z ≥ 0`, `1 - a (1 - e^{-z}) ≤ exp(-z a (1 - z/2))`. -/
theorem one_sub_mul_one_sub_exp_neg_le {a z : ℝ} (ha : 0 ≤ a) (hz : 0 ≤ z) :
    1 - a * (1 - Real.exp (-z)) ≤ Real.exp (-(z * (a * (1 - z / 2)))) := by
  have h1 := exp_neg_le_one_sub_add_sq_div_two hz
  have h2 := Real.add_one_le_exp (-(z * (a * (1 - z / 2))))
  nlinarith [mul_le_mul_of_nonneg_left h1 ha]

/-- **The raw factor is bounded by the baseline paid reward.** If `ε ≥ ε_*`, then for every
integer `c` and `p ∈ 𝒫`, `φ_c(p) ≤ exp(-z_* R^old_c(p))`. -/
@[collatz_pos_dens "lem_ch_old_reward_bound"]
theorem chRawFactor_le_exp_neg_chOldReward {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ}
    (hε : (epsStar : ℝ) ≤ ε) (c : ℤ) {p : ℤ × ℤ} (hp : p ∈ bkPoints) :
    chRawFactor n ξ c p ≤ Real.exp (-((zStar : ℝ) * chOldReward n ξ ε c p)) := by
  have hwhite : ∀ {q : ℤ × ℤ}, IsBkWhite n ξ ε q → (epsStar : ℝ) < |bkTheta n ξ q| :=
    fun h => hε.trans_lt h.lt_abs_bkTheta
  have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
  have h1 : chRawFactor n ξ c p ≤ 1 := chRawFactor_le_one n ξ c p
  rcases lt_or_ge c 3 with hc | hc3
  · rw [chOldReward_of_not_mem (Or.inl hc)]; simpa using h1
  rcases lt_or_ge 16 c with hc | hc16
  · rw [chOldReward_of_not_mem (Or.inr hc)]; simpa using h1
  obtain rfl | rfl | rfl | hc6 : c = 3 ∨ c = 4 ∨ c = 5 ∨ 6 ≤ c := by omega
  · rw [chOldReward_three]
    split_ifs with hw
    · rw [mul_one, mul_comm]
      exact (chPairFactor_three_lt_exp (hwhite hw)).le
    · simpa using h1
  · rw [chOldReward_four]
    split_ifs with hw
    · simpa using (chPairFactor_four_lt_exp_neg (hwhite hw)).le
    · simpa using h1
  · rw [chOldReward_five]
    by_cases hw : IsBkWhite n ξ ε p
    · simpa [hw] using (chPairFactor_five_lt_exp (hwhite hw)).le
    by_cases hq : IsBkWhite n ξ ε (p - (0, 1))
    · simp only [hw, hq, ite_false, not_false_eq_true, and_self, ite_true, zero_add, mul_one]
      have hb := chRawFactor_le_packets n ξ (c := 5) (by norm_num) hp {(1, 3)}
        (by simp) (by simp)
      have h4 := chPairFactor_four_lt_exp_neg (hwhite hq)
      simp only [Finset.sum_singleton] at hb
      norm_num at hb
      calc chRawFactor n ξ 5 p ≤ 1 - 3 / 4 * (1 - Real.exp (-(zStar : ℝ))) := by linarith
        _ ≤ Real.exp (-((zStar : ℝ) * (3 / 4 * (1 - (zStar : ℝ) / 2)))) :=
          one_sub_mul_one_sub_exp_neg_le (by norm_num) hz
        _ = Real.exp (-((zStar : ℝ) * (18351 / 25000))) := by
          rw [zStar_cast]; norm_num
    · simpa [hw, hq] using h1
  · rw [chOldReward_of_six_le_of_le_sixteen hc6 hc16]
    obtain ⟨S, hS, hd, hsum⟩ := exists_sum_eq_chPacketCoverage (n := n) (ξ := ξ) (ε := ε)
      (c := c) (p := p)
    have hb := chRawFactor_le_packets n ξ (c := c) (by omega) hp S
      (fun kt hk => by have := add_le_of_mem_chPackets (hS hk); push_cast; omega) hd
    have hblock : ∑ kt ∈ S, (kt.2 : ℝ) * chRawFactor n ξ ((kt.2 : ℤ) + 1) (p - (0, (kt.1 : ℤ)))
        ≤ ∑ kt ∈ S, (kt.2 : ℝ) * Real.exp (-(zStar : ℝ)) := by
      refine Finset.sum_le_sum fun kt hk => ?_
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      have hw := hwhite (isBkWhite_of_mem_chPackets (hS hk))
      rcases snd_eq_three_or_four_of_mem_chPackets (hS hk) with h | h
      · rw [h]; exact (chPairFactor_four_lt_exp_neg hw).le
      · rw [h]; exact (chPairFactor_five_lt_exp hw).le
    rw [← Finset.sum_mul] at hblock
    have hM : ∑ kt ∈ S, (kt.2 : ℝ) = (chPacketCoverage n ξ ε c p : ℝ) := by
      rw [← hsum]; push_cast; rfl
    rw [hM] at hb hblock
    have hcpos : (0 : ℝ) < (c : ℝ) - 1 := by
      have : (6 : ℝ) ≤ c := by exact_mod_cast hc6
      linarith
    set M : ℝ := (chPacketCoverage n ξ ε c p : ℝ)
    have hle : chRawFactor n ξ c p ≤ 1 - M / ((c : ℝ) - 1) * (1 - Real.exp (-(zStar : ℝ))) := by
      have : M * (1 - Real.exp (-(zStar : ℝ))) / ((c : ℝ) - 1) ≤ 1 - chRawFactor n ξ c p := by
        rw [div_le_iff₀ hcpos]
        nlinarith
      rw [div_mul_eq_mul_div]
      linarith
    refine hle.trans ((one_sub_mul_one_sub_exp_neg_le (by positivity) hz).trans_eq ?_)
    ring_nf

end CollatzPosDens
