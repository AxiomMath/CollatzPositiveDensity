/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.Eb
public import CollatzPosDens.FirstCrossing.EbPower
public import CollatzPosDens.FirstCrossing.FcMinOvershoot
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.WeightUpper
public import CollatzPosDens.Seed.FourThirds
public import CollatzPosDens.FirstCrossing.CeilLog3
public import CollatzPosDens.FirstCrossing.Lb
public import CollatzPosDens.Maps.Weight
public import Mathlib.Tactic.IntervalCases

/-!
# The weight of a central block

For every level `b ≥ 9`, every `K ≥ 0` and every word `w` of the central family `𝒞(b, K)`,
$$16^{e_b}\,\omega(w) < 1 - 2^{-3b}.$$

Write `s = |w|` and `H = H_{b,r_b}`, so that `A(w) ≥ H(s) = 2b + B((s-b)_+) - B((b-s)_+)`.
The proof splits into four ranges of `b`.

* For `b ∈ {9, 10, 11}`, `e_b = 1` and the central family imposes `A(w) ≥ H(s) + μ_b(s)`,
  where the minimal overshoot satisfies `16 · 3^s · 2^{3b} < (2^{3b} - 1) 2^{H(s) + μ_b(s)}`.
* For `b = 12`, `e_b = 1` and `ℓ_{12} = 5`, so `s ≥ 6`. For `s ≥ 12` one has
  `2^{H(s)} ≥ 2^{24} 3^{s-12}`, and for `6 ≤ s < 12` the values `B(1), …, B(6)` are bounded
  above by `2, 4, 5, 7, 8, 10`; in every case `16 ω(w) ≤ 3^{10}/2^{16} < 1 - 2^{-36}`.
* For `13 ≤ b ≤ 255`, `ω(w) ≤ 2 (3/4)^b` and `9 · 3^b · 16^{e_b} < 4^{b+1}`, giving
  `16^{e_b} ω(w) < 8/9`.
* For `b ≥ 256`, `e_b = ⌈b/100⌉` and `4 · 16^{e_b} · 3^b ≤ 4^b`, which again gives
  `9 · 3^b · 16^{e_b} < 4^{b+1}` and hence `16^{e_b} ω(w) < 8/9`.

## Main results

* `CollatzPosDens.sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily`:
  `16^{e_b} ω(w) < 1 - 2^{-3b}` for `b ≥ 9` and `w ∈ 𝒞(b, K)`.

## Implementation notes

The levels `b` and `K` are natural numbers, and the inequality is stated in `ℚ`, where the
weight lives, with `2^{-3b}` written as `(2^{3b})⁻¹`. For `b = 12` the proof uses only the
upper bounds `B(j) ≤ n` (from `3^j ≤ 2^n`) for `1 ≤ j ≤ 6` and the lower bound
`3^j ≤ 2^{B(j)}`, rather than the exact barrier values; for `b ≥ 256` it uses the
cleared-denominator form of the comparison `4 · 16^{⌈b/100⌉} ≤ (4/3)^b`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `c ≤ A(w)`, then `ω(w) ≤ 3^{|w|} / 2^c`. -/
private theorem weight_le_of_le_valSum {w : Word} {c : ℕ} (h : c ≤ w.valSum) :
    w.weight ≤ 3 ^ w.length / 2 ^ c := by
  unfold Word.weight
  gcongr
  · norm_num

/-- The common tail of the cases `b ≥ 13`: from `9 · 3^b · 16^{e_b} < 4^{b+1}` and
`ω(w) ≤ 2 (3/4)^b`, deduce `16^{e_b} ω(w) < 1 - 2^{-3b}`. -/
private theorem lt_of_power {b K : ℕ} {w : Word} (hb : 2 ≤ b)
    (hw : w ∈ firstCrossing b (rb b) K) (hp : 9 * 3 ^ b * 16 ^ eb b < 4 ^ (b + 1)) :
    (16 : ℚ) ^ eb b * w.weight < 1 - (2 ^ (3 * b))⁻¹ := by
  have h1 := weight_le_of_mem_firstCrossing hw
  rw [show 1 + rb b - rb b = 1 by ring, zpow_one] at h1
  have hp' : (9 : ℚ) * 3 ^ b * 16 ^ eb b < 4 ^ (b + 1) := by exact_mod_cast hp
  have h9 : (9 : ℚ) ≤ 2 ^ (3 * b) := by
    calc (9 : ℚ) ≤ 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (3 * b) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hinv : ((2 : ℚ) ^ (3 * b))⁻¹ ≤ 1 / 9 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) h9
  have h4 : (0 : ℚ) < 4 ^ b := by positivity
  have key : (16 : ℚ) ^ eb b * (2 * (3 / 4) ^ b) < 8 / 9 := by
    rw [div_pow, lt_div_iff₀ (by norm_num)]
    rw [pow_succ] at hp'
    have : (16 : ℚ) ^ eb b * (2 * (3 ^ b / 4 ^ b)) * 9 = 2 * (9 * 3 ^ b * 16 ^ eb b) / 4 ^ b := by
      field_simp
    rw [this, div_lt_iff₀ h4]
    linarith
  calc (16 : ℚ) ^ eb b * w.weight ≤ 16 ^ eb b * (2 * (3 / 4) ^ b) := by gcongr
    _ < 8 / 9 := key
    _ ≤ 1 - (2 ^ (3 * b))⁻¹ := by linarith

private theorem sixteen_pow_eb_mul_weight_lt_of_lt_twelve {b K : ℕ} {w : Word} (hb : 9 ≤ b)
    (hb12 : b < 12) (hw : w ∈ centralFamily b K) :
    (16 : ℚ) ^ eb b * w.weight < 1 - (2 ^ (3 * b))⁻¹ := by
  have hsmall : b ∈ ({9, 10, 11} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hA := ((mem_centralFamily_of_small hsmall).1 hw).2
  have hspec := fcMinOvershoot_spec (show 1 ≤ b by omega) w.length
  rw [eb_of_le_twelve (by omega), pow_one]
  set H := barrier b (rb b) w.length + (fcMinOvershoot b w.length : ℤ)
  have h2 : (2 : ℝ) ^ H ≤ 2 ^ w.valSum := by
    rw [← zpow_natCast]
    exact zpow_le_zpow_right₀ one_le_two hA
  have hf := fcMinOvershoot_one_le_factor (show 1 ≤ b by omega)
  have hlt : (16 : ℝ) * 3 ^ w.length * 2 ^ (3 * b) < (2 ^ (3 * b) - 1) * 2 ^ w.valSum :=
    hspec.trans_le (mul_le_mul_of_nonneg_left h2 (by linarith))
  rw [← Rat.cast_lt (K := ℝ)]
  push_cast [Word.weight]
  rw [show (1 : ℝ) - (2 ^ (3 * b))⁻¹ = (2 ^ (3 * b) - 1) / 2 ^ (3 * b) by field_simp,
    mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
  exact hlt

private theorem weight_le_of_mem_firstCrossing_twelve {K : ℕ} {w : Word}
    (hfc : w ∈ firstCrossing 12 (rb 12) K) : w.weight ≤ 3 ^ 10 / 2 ^ 20 := by
  have hl : 5 < w.length := by
    have := lb_lt_length_of_mem_firstCrossing hfc
    rwa [lb_eq] at this
  have hA := barrier_le_valSum_of_mem_firstCrossing hfc
  rw [barrier_def] at hA
  rcases le_or_gt 12 w.length with hs | hs
  · obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hs
    rw [hj, show 12 + j - 12 = j by omega, show 12 - (12 + j) = 0 by omega,
      ceilLog3_zero] at hA
    have hc : 24 + ceilLog3 j ≤ w.valSum := by push_cast at hA; omega
    have h3 : ((3 : ℚ) ^ j) ≤ 2 ^ ceilLog3 j := mod_cast three_pow_le_two_pow_ceilLog3 j
    calc w.weight ≤ 3 ^ w.length / 2 ^ (24 + ceilLog3 j) := weight_le_of_le_valSum hc
      _ ≤ 3 ^ (12 + j) / (2 ^ 24 * 3 ^ j) := by
        rw [hj, pow_add (2 : ℚ)]
        gcongr
      _ ≤ 3 ^ 10 / 2 ^ 20 := by
        rw [pow_add, mul_comm ((2 : ℚ) ^ 24), ← div_div, mul_div_assoc,
          div_self (by positivity), mul_one]
        norm_num
  · have key : ∀ n, ceilLog3 (12 - w.length) ≤ n → 24 - n ≤ w.valSum := by
      intro n hn
      have : ceilLog3 (w.length - 12) = 0 := by
        rw [show w.length - 12 = 0 by omega, ceilLog3_zero]
      rw [this] at hA
      push_cast at hA
      omega
    obtain ⟨s, hs'⟩ : ∃ s, w.length = s := ⟨_, rfl⟩
    rw [hs'] at key hl hs
    have fin : ∀ n, 3 ^ (12 - s) ≤ 2 ^ n → (3 : ℚ) ^ s / 2 ^ (24 - n) ≤ 3 ^ 10 / 2 ^ 20 →
        w.weight ≤ 3 ^ 10 / 2 ^ 20 := fun n hn h =>
      (hs' ▸ weight_le_of_le_valSum (key n (ceilLog3_le_iff.2 hn))).trans h
    interval_cases s
    · exact fin 10 (by norm_num) (by norm_num)
    · exact fin 8 (by norm_num) (by norm_num)
    · exact fin 7 (by norm_num) (by norm_num)
    · exact fin 5 (by norm_num) (by norm_num)
    · exact fin 4 (by norm_num) (by norm_num)
    · exact fin 2 (by norm_num) (by norm_num)

/-- **Weight of a central block.** For `b ≥ 9`, `K ≥ 0` and `w ∈ 𝒞(b, K)`,
`16^{e_b} ω(w) < 1 - 2^{-3b}`. -/
@[collatz_pos_dens "lem_s05_block_weight"]
theorem sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily {b K : ℕ} {w : Word} (hb : 9 ≤ b)
    (hw : w ∈ centralFamily b K) :
    (16 : ℚ) ^ eb b * w.weight < 1 - (2 ^ (3 * b))⁻¹ := by
  have hfc := centralFamily_subset_firstCrossing b K hw
  rcases lt_or_ge b 12 with hb12 | hb12
  · exact sixteen_pow_eb_mul_weight_lt_of_lt_twelve hb hb12 hw
  rcases eq_or_lt_of_le hb12 with rfl | hb13
  · rw [eb_of_le_twelve le_rfl, pow_one]
    calc (16 : ℚ) * w.weight ≤ 16 * (3 ^ 10 / 2 ^ 20) := by
          gcongr
          exact weight_le_of_mem_firstCrossing_twelve hfc
      _ < 1 - (2 ^ (3 * 12))⁻¹ := by norm_num
  refine lt_of_power (by omega) hfc ?_
  rcases lt_or_ge b 256 with hb256 | hb256
  · have := eb_power (b := b) (by omega) (by omega)
    linarith [mul_comm (9 * 3 ^ b) (16 ^ eb b)]
  · have h := four_mul_sixteen_pow_mul_three_pow_le_four_pow (k := eb b) hb256
      (by rw [eb_of_le hb256]; omega)
    have h4 : 0 < 4 ^ b := by positivity
    rw [pow_succ]
    nlinarith

end CollatzPosDens
