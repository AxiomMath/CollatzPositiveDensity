/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShHalfMomentSum
public import CollatzPosDens.Mixing.MxShRatio

/-!
# The half moment of the offset in the degree cut

For integers `N` and `d` with `100 (d - 1) ≤ 51 (N - 1)` we show
$$\sum_{S \subseteq \{1, \dots, N\},\ |S| = d} \sqrt{\operatorname{Of}(S)} \le 40 \binom N d,$$
where `Of(S)` is the offset `CollatzPosDens.setOffset`.

For `d = 0` the only subset is `∅`, of offset `0`. For `d ≥ 1` put `p = (d - 1)/(N - 1)`, so that
`0 ≤ p ≤ 51/100`. The ratio `ρ = (1 + (√3 - 1) p)/√2` then satisfies `0 ≤ ρ < 39/40` by
`CollatzPosDens.mx_sh_ratio_lt`, so `∑_{i < N} ρ^i < 40`; together with `1/√2 ≤ 1` and
`binom (N - 1) (d - 1) ≤ binom N d`, the bound `CollatzPosDens.sum_powersetCard_sqrt_setOffset_le`
gives the claim.

## Main results

* `CollatzPosDens.sum_powersetCard_sqrt_setOffset_le_forty`: the half-moment bound.

## Implementation notes

In [mazur2026] the bound is stated under `N ≥ 2` and `0 ≤ d ≤ N` besides
`100 (d - 1) ≤ 51 (N - 1)`. Neither extra hypothesis is needed: for `d > N` the sum is empty, and
the remaining inequality forces `N ≥ 1` whenever `d ≥ 1`. For `N = 1`, the quotient
`(d - 1)/(N - 1)` is read as `0` (and then `d = 1`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- **Half moment of the offset in the degree cut.** For integers `N`, `d ≥ 0` with
`100 (d - 1) ≤ 51 (N - 1)` (in particular for `N ≥ 2` and `0 ≤ d ≤ N` with this inequality),
$$\sum_{S \subseteq \{1, \dots, N\},\ |S| = d} \sqrt{\operatorname{Of}(S)} \le 40 \binom N d.$$ -/
@[collatz_pos_dens "lem_mx_sh_half_moment"]
theorem sum_powersetCard_sqrt_setOffset_le_forty {N d : ℕ}
    (h : 100 * ((d : ℤ) - 1) ≤ 51 * ((N : ℤ) - 1)) :
    ∑ S ∈ (Icc 1 N).powersetCard d, √(setOffset S : ℝ) ≤ 40 * N.choose d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hN : 1 ≤ N := by omega
  have hR : (100 : ℝ) * ((d : ℝ) - 1) ≤ 51 * ((N : ℝ) - 1) := by exact_mod_cast h
  have hd1 : (0 : ℝ) ≤ (d : ℝ) - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  set p : ℝ := ((d : ℝ) - 1) / ((N : ℝ) - 1) with hp
  have hp0 : 0 ≤ p := by
    have : (0 : ℝ) ≤ (N : ℝ) - 1 := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    positivity
  have hp1 : p ≤ 51 / 100 := by
    rcases eq_or_lt_of_le hN with hN1 | hN1
    · rw [hp, ← hN1]; norm_num
    · have : (1 : ℝ) < N := by exact_mod_cast hN1
      rw [hp, div_le_iff₀ (by linarith)]
      linarith
  have h3 : 1 < √3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : 0 < √2 := by positivity
  have h2' : 1 ≤ √2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  set ρ : ℝ := (1 + (√3 - 1) * p) / √2 with hρ
  have hρ0 : 0 ≤ ρ := by
    have : 0 ≤ (√3 - 1) * p := mul_nonneg (by linarith) hp0
    positivity
  have hρ1 : ρ < 39 / 40 := by
    refine lt_of_le_of_lt ?_ mx_sh_ratio_lt
    rw [hρ]
    gcongr
  have hgeom : ∑ i ∈ range N, ρ ^ i ≤ 40 := by
    calc ∑ i ∈ range N, ρ ^ i ≤ ∑ i ∈ range N, (39 / 40 : ℝ) ^ i :=
          sum_le_sum fun i _ => pow_le_pow_left₀ hρ0 hρ1.le i
      _ = 40 * (1 - (39 / 40 : ℝ) ^ N) := by
          rw [geom_sum_eq (by norm_num)]; ring
      _ ≤ 40 := by
          have : (0 : ℝ) ≤ (39 / 40) ^ N := by positivity
          linarith
  have hchoose : (N - 1).choose (d - 1) ≤ N.choose d := by
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
    simp only [Nat.add_sub_cancel, Nat.choose_succ_succ]
    omega
  have hchooseR : ((N - 1).choose (d - 1) : ℝ) ≤ N.choose d := by exact_mod_cast hchoose
  have hinv : 1 / √2 ≤ 1 := by
    rw [div_le_one h2]; exact h2'
  calc ∑ S ∈ (Icc 1 N).powersetCard d, √(setOffset S : ℝ)
      ≤ (N - 1).choose (d - 1) * (1 / √2) * ∑ i ∈ range N, ρ ^ i :=
        sum_powersetCard_sqrt_setOffset_le hN hd
    _ ≤ N.choose d * 1 * 40 := by
        gcongr
    _ = 40 * N.choose d := by ring

end CollatzPosDens
