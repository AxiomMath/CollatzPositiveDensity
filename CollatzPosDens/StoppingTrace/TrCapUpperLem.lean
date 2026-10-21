/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChOddPackets
public import CollatzPosDens.StoppingTrace.TrCapFactor
public import CollatzPosDens.StoppingTrace.TrCapUpper

/-!
# The rational majorant bounds the capped packet factor

For every integer `c`, every rational `θ` and every rounding step `η`, the capped packet factor
`Φ^cap_c(θ)` is at most its rational majorant `U^η_c(θ)`.

The proof bounds each cosine `cos (2π (a_j - a_i) θ)` by the cosine bound `cb_{ij}`. If
`x = (a_j - a_i) θ` is an integer, `cb_{ij} = 1`. Otherwise, with `τ = x - round x ∈ [-1/2, 1/2)`,
`cos (2π x) = cos (2π τ)`; as `0 < π - π₀ < 10^{-15}` and `cos` is `1`-Lipschitz,
`cos (2π τ) ≤ cos (2π₀ τ) + 10^{-15}`, and for `|y| ≤ 4` the Taylor polynomial `P` of degree `25`
satisfies `cos y ≤ P(y)`. Summing over the pairs, `t^2 Φ_t(θ)^2 = t + 2 ∑_{i<j} cos(2π(a_j-a_i)θ)`
is at most `t^2 k^2 / 10^16`, so `Φ_t(θ) ≤ k / 10^8`.

## Main results

* `CollatzPosDens.cos_le_trCapCosPoly`: `cos y ≤ P(y)` for `|y| ≤ 4`.
* `CollatzPosDens.cos_two_pi_le_trCapCosBound`: `cos (2π x) ≤ cb(x)` for every rational `x`.
* `CollatzPosDens.trCapFactor_le_trCapUpper`: `Φ^cap_c(θ) ≤ U^η_c(θ)`.

## Implementation notes

[Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026] states
the bound for `η ∈ {0, 10^{-18}}`; it holds for every rational `η`, since rounding up to the grid
`η ℤ` (or not rounding, for `η ≤ 0`) only increases the cosine bound. The Taylor bound
`cos y ≤ P(y)` is derived from the exponential series truncated at degree `28`, whose real part is
`P(y) - y^26/26!`; this is sharper than the Lagrange remainder `|y|^26/26!`, so no additional error
term `(22/7)^26/26!` is needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- The real part of the exponential series of `y i` truncated at degree `2N` is the cosine
Taylor polynomial `∑_{k<N} (-1)^k y^(2k) / (2k)!`. -/
theorem re_sum_range_two_mul_exp_series (y : ℝ) (N : ℕ) :
    (∑ m ∈ range (2 * N), ((y : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)).re =
      ∑ k ∈ range N, (-1) ^ k * y ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      Complex.add_re, Complex.add_re, ih, sum_range_succ]
    have h1 : ((y : ℂ) * Complex.I) ^ (2 * N) / ((2 * N).factorial : ℂ) =
        (((-1) ^ N * y ^ (2 * N) / ((2 * N).factorial : ℝ) : ℝ) : ℂ) := by
      rw [mul_pow, pow_mul Complex.I, Complex.I_sq]
      push_cast; ring
    have h2 : ((y : ℂ) * Complex.I) ^ (2 * N + 1) / ((2 * N + 1).factorial : ℂ) =
        (((-1) ^ N * y ^ (2 * N + 1) / ((2 * N + 1).factorial : ℝ) : ℝ) : ℂ) * Complex.I := by
      rw [mul_pow, pow_succ Complex.I, pow_mul Complex.I, Complex.I_sq]
      push_cast; ring
    rw [h1, h2, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]

/-- The Taylor polynomial of degree `25` bounds the cosine from above on `[-4, 4]`. -/
theorem cos_le_trCapCosPoly {y : ℝ} (hy : |y| ≤ 4) :
    Real.cos y ≤ ∑ k ∈ range 13, (-1) ^ k * y ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  have hn : ‖(y : ℂ) * Complex.I‖ = |y| := by simp
  have hb := Complex.exp_bound' (x := (y : ℂ) * Complex.I) (n := 2 * 14)
    (by rw [hn]; norm_num; linarith)
  rw [hn] at hb
  have hre := (Complex.re_le_norm _).trans hb
  rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, re_sum_range_two_mul_exp_series,
    sum_range_succ] at hre
  have hy2 : y ^ 2 ≤ 16 := by
    have := sq_abs y ▸ pow_le_pow_left₀ (abs_nonneg y) hy 2
    linarith
  have h28 : |y| ^ (2 * 14) = y ^ 26 * y ^ 2 := by
    rw [Even.pow_abs ⟨14, by ring⟩]; ring
  rw [h28] at hre
  have h26 : 0 ≤ y ^ 26 := by positivity
  norm_num [Nat.factorial] at hre ⊢
  nlinarith [mul_le_mul_of_nonneg_left hy2 h26]

/-- `π₀ < π < π₀ + 10^{-15}`, so `|π - π₀| ≤ 10^{-15}`. -/
theorem abs_pi_sub_trCapPi0_le : |π - (trCapPi0 : ℝ)| ≤ 1 / 10 ^ 15 := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  rw [abs_le]
  constructor <;> norm_num [trCapPi0] <;> linarith

/-- The polynomial `P` commutes with the cast `ℚ → ℝ`. -/
theorem ratCast_trCapCosPoly (q : ℚ) :
    ((trCapCosPoly q : ℚ) : ℝ) =
      ∑ k ∈ range 13, (-1) ^ k * (q : ℝ) ^ (2 * k) / ((2 * k).factorial : ℝ) := by
  simp [trCapCosPoly]

/-- The cosine bound bounds `cos (2π x)` from above, for every rational `x` and every `η`. -/
theorem cos_two_pi_le_trCapCosBound (η x : ℚ) :
    Real.cos (2 * π * x) ≤ trCapCosBound η x := by
  by_cases hx : Int.fract x = 0
  · rw [trCapCosBound_of_fract_eq_zero hx]
    simpa using Real.cos_le_one _
  have hcb := le_trCapCosBound hx η
  set τ : ℚ := x - round x with hτ
  have hτI := sub_round_mem_Ico x
  rw [← hτ, Set.mem_Ico] at hτI
  have hτR : |(τ : ℝ)| ≤ 1 / 2 := by
    rw [abs_le]; constructor
    · have : ((-(1 / 2) : ℚ) : ℝ) ≤ τ := by exact_mod_cast hτI.1
      push_cast at this; linarith
    · have : (τ : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hτI.2.le
      push_cast at this; linarith
  have hcos : Real.cos (2 * π * x) = Real.cos (2 * π * τ) := by
    have hq : (x : ℝ) = τ + (round x : ℤ) := by rw [hτ]; push_cast; ring
    rw [hq, show 2 * π * ((τ : ℝ) + (round x : ℤ)) = 2 * π * τ + (round x : ℤ) * (2 * π) by ring,
      Real.cos_add_int_mul_two_pi]
  have hpi0 : (trCapPi0 : ℝ) = 3141592653589793 / 10 ^ 15 := by norm_num [trCapPi0]
  set y : ℝ := 2 * trCapPi0 * τ with hy
  have hyb : |y| ≤ 4 := by
    rw [hy, abs_mul, abs_of_pos (by rw [hpi0]; norm_num : (0 : ℝ) < 2 * trCapPi0), hpi0]
    nlinarith [abs_nonneg (τ : ℝ)]
  have hL := (abs_le.1 (Real.abs_cos_sub_cos_le (2 * π * τ) y)).2
  have hL' : |2 * π * τ - y| ≤ 1 / 10 ^ 15 := by
    rw [hy, show 2 * π * (τ : ℝ) - 2 * trCapPi0 * τ = (2 * τ) * (π - trCapPi0) by ring, abs_mul]
    have := abs_pi_sub_trCapPi0_le
    have h2τ : |2 * (τ : ℝ)| ≤ 1 := by rw [abs_mul]; norm_num; linarith
    calc |2 * (τ : ℝ)| * |π - trCapPi0| ≤ 1 * (1 / 10 ^ 15) := by gcongr
      _ = 1 / 10 ^ 15 := one_mul _
  have hT := cos_le_trCapCosPoly hyb
  have hcbR : (((trCapCosPoly (2 * trCapPi0 * τ) + trCapCosErr : ℚ)) : ℝ) ≤ trCapCosBound η x := by
    exact_mod_cast hcb
  have hE : (1 / 10 ^ 15 : ℝ) ≤ trCapCosErr := by
    rw [trCapCosErr]; push_cast
    have : (0 : ℝ) ≤ (22 / 7) ^ 26 / (Nat.factorial 26 : ℝ) := by positivity
    linarith
  rw [Rat.cast_add, ratCast_trCapCosPoly] at hcbR
  push_cast at hcbR
  rw [hcos]
  rw [← hy] at hcbR
  linarith

/-- **The rational majorant bounds the capped packet factor.** For every integer `c`, every
rational `θ` and every rational rounding step `η`, `Φ^cap_c(θ) ≤ U^η_c(θ)`. -/
@[collatz_pos_dens "lem_tr_cap_upper"]
theorem trCapFactor_le_trCapUpper (c : ℤ) (η θ : ℚ) :
    trCapFactor c θ ≤ trCapUpper c η θ := by
  by_cases h : 3 ≤ c ∧ c ≤ 16
  swap
  · rw [trCapFactor_of_not_mem h, trCapUpper_of_not_mem h, Rat.cast_one]
  rw [trCapFactor_of_mem h.1 h.2, trCapUpper_of_mem h.1 h.2]
  set t : ℕ := (c - 1).toNat with ht
  have ht2 : 2 ≤ t := by omega
  set k : ℕ := natCeilSqrt (trCapRadicand t η θ) with hk
  have htR : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hpair : chPacketPairSum t θ ≤
      t + 2 * ∑ j ∈ range t, ∑ i ∈ range j,
        ((trCapCosBound η ((((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ i - 1)) * θ) : ℚ) : ℝ) := by
    unfold chPacketPairSum
    gcongr with j _ i _
    have := cos_two_pi_le_trCapCosBound η ((((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ i - 1)) * θ)
    push_cast at this
    convert this using 3
    ring
  have hR : ((trCapRadicand t η θ : ℚ) : ℝ) ≤ (k : ℝ) ^ 2 := by
    exact_mod_cast le_natCeilSqrt_sq (trCapRadicand t η θ)
  have hRdef : ((trCapRadicand t η θ : ℚ) : ℝ) = 10 ^ 16 / (t : ℝ) ^ 2 *
      (t + 2 * ∑ j ∈ range t, ∑ i ∈ range j,
        ((trCapCosBound η ((((2 : ℚ) ^ j - 1) - ((2 : ℚ) ^ i - 1)) * θ) : ℚ) : ℝ)) := by
    simp [trCapRadicand]
  have hsq : chPacketFn t θ ^ 2 ≤ ((k : ℝ) / 10 ^ 8) ^ 2 := by
    rw [chPacketFn_sq, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [hRdef] at hR
    have h1 := mul_le_mul_of_nonneg_left hpair (by positivity : (0 : ℝ) ≤ 10 ^ 16)
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hR
    nlinarith
  have hΦ : chPacketFn t θ ≤ (k : ℝ) / 10 ^ 8 :=
    (pow_le_pow_iff_left₀ (chPacketFn_nonneg _ _) (by positivity) two_ne_zero).1 hsq
  have hcap : (2 : ℝ) ^ (-16 : ℤ) ≤ 1526 / 10 ^ 8 := by norm_num
  rw [Rat.cast_min, Rat.cast_one]
  refine le_min (max_le (chPacketFn_le_one _ _)
    (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num))) ?_
  push_cast
  refine max_le (hΦ.trans ?_) (hcap.trans ?_)
  · gcongr; exact le_max_left _ _
  · gcongr; exact le_max_right _ _

end CollatzPosDens
