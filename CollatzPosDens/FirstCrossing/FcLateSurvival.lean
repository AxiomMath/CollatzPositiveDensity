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
public import CollatzPosDens.FirstCrossing.FcDeficitBound
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Survival of the central families

For every `s ∈ ℕ`, the central families along the scales `b_j` with caps `K_j` survive with
probability close to `1`:
$$\prod_{j=0}^{s-1}\mathbf p(\mathcal C(b_j,K_j)) > \frac{199}{200}.$$

Write `d_j = 1 - 𝐩(𝒞(b_j, K_j))` and `c = 529/10⁶`. For deficits `d_j ∈ [0, 1]` one has
`∏ (1 - d_j) ≥ 1 - ∑ d_j`, so it suffices to show `∑_{j<s} d_j < 1/200`. The deficit bound
`d_j ≤ 2e^{-c(b_j-14)} + 2b_j^{-3/2} + 2^{-(K_j+1)}` splits the sum into three geometric sums.

* Since `b_j - 14 ≥ 16530 + 166j`, the exponential terms are at most `2e^{-16530c} ρ^j` with
  `ρ = e^{-166c}`; here `e^{166c} ≥ 1 + 166c + (166c)²/2` gives `1 - ρ ≥ 83/1000`, and
  `e^{16530c} = e^8 e^{16530c - 8} > 6000`. They sum to less than `2/(6000 · 83/1000)`.
* Since `b_j ≥ 16544 𝗀^j ≥ 2^{14} 𝗀^j`, the power terms are at most `2 · 2^{-21} (𝗀^{-3/2})^j`,
  and `𝗀^{-3/2} ≤ 𝗀^{-1} = 100/101`; they sum to at most `202 · 2^{-21}`.
* Since `K_j + 1 = 30 + ⌊j/56⌋` and each value of `⌊j/56⌋` occurs for `56` values of `j`, the
  cap terms sum to at most `56 · 2^{-29}`.

The three bounds add up to less than `1/200`.

## Main results

* `CollatzPosDens.lt_prod_geomMass_centralFamily`: the product bound above.
* `CollatzPosDens.one_sub_sum_le_prod_one_sub_ennreal`: `1 - ∑ a_i ≤ ∏ (1 - a_i)` in
  `ℝ≥0∞`, with truncated subtraction.

## Implementation notes

The masses live in `ℝ≥0∞` and `d_j` is the truncated difference `1 - 𝐩(𝒞(b_j, K_j))`. The
inequality `1 - ∑ a_i ≤ ∏ (1 - a_i)` holds in `ℝ≥0∞` for arbitrary `a_i` (a summand `a_i ≥ 1`
makes both sides vanish), and `𝐩 ≥ 1 - (1 - 𝐩)` holds for any `𝐩`, so the bound
`𝐩(𝒞(b_j, K_j)) ≤ 1` (from prefix-disjointness) used in [Mazur] to place `d_j` in `[0, 1]`
is not needed. [Mazur] bounds `e^{16530c} > 6275` by a partial exponential sum of `41`
terms, `1 - ρ` by `e^{-y} ≤ 1 - y + y²/2`, and `16544^{3/2} ≥ 2127000`; the slightly weaker
constants `6000`, the quadratic lower bound of `e^{166c}`, and `2^{21}` used here leave the
total below `1/200`.

## References

* [Mazur, *Collatz positive density*], §14.6.
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- In `ℝ≥0∞` with truncated subtraction, `1 - ∑ a_i ≤ ∏ (1 - a_i)` over any finite index set. -/
theorem one_sub_sum_le_prod_one_sub_ennreal {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi, add_comm, tsub_add_eq_tsub_tsub]
    have hy : 1 - ∑ j ∈ s, a j ≤ 1 := tsub_le_self
    calc 1 - ∑ j ∈ s, a j - a i ≤ (1 - a i) * (1 - ∑ j ∈ s, a j) := by
          rw [ENNReal.sub_mul fun _ _ => ne_top_of_le_ne_top ENNReal.one_ne_top hy, one_mul]
          exact tsub_le_tsub_left (mul_le_of_le_one_right' hy) _
      _ ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) := by gcongr

/-- For `0 ≤ x < 1`, the partial geometric sums satisfy `∑_{k<M} x^k ≤ 1 / (1 - x)`. -/
private theorem fcLateSurvival_geom_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (M : ℕ) :
    ∑ k ∈ Finset.range M, x ^ k ≤ 1 / (1 - x) := by
  rw [geom_sum_eq hx1.ne, ← neg_div_neg_eq, neg_sub, neg_sub]
  have : 0 ≤ x ^ M := pow_nonneg hx0 M
  gcongr
  linarith

/-- For `0 ≤ x < 1` and a period `p > 0`, `∑_{t<N} x^{⌊t/p⌋} ≤ p / (1 - x)`. -/
private theorem fcLateSurvival_sum_pow_div_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) {p : ℕ}
    (hp : 0 < p) (N : ℕ) : ∑ t ∈ Finset.range N, x ^ (t / p) ≤ p / (1 - x) := by
  have hblock : ∀ M, ∑ t ∈ Finset.range (p * M), x ^ (t / p) =
      p * ∑ k ∈ Finset.range M, x ^ k := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
      congr 1
      rw [Finset.sum_congr rfl fun r hr => by
        rw [show (p * M + r) / p = M by
          rw [Finset.mem_range] at hr
          rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hr, zero_add]]]
      simp
  calc ∑ t ∈ Finset.range N, x ^ (t / p)
      ≤ ∑ t ∈ Finset.range (p * N), x ^ (t / p) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (Nat.le_mul_of_pos_left N hp))
          fun _ _ _ => pow_nonneg hx0 _
    _ = p * ∑ k ∈ Finset.range N, x ^ k := hblock N
    _ ≤ p * (1 / (1 - x)) := by gcongr; exact fcLateSurvival_geom_le hx0 hx1 N
    _ = p / (1 - x) := by ring

/-- `e^{-16530c} < 1/6000` for `c = 529/10⁶`, from `e^{16530c} = e^8 e^{16530c - 8}`,
`e > 2.7182818283` and `e^x ≥ 1 + x + x²/2`. -/
private theorem fcLateSurvival_exp_neg_lt : exp (-(529 / 10 ^ 6) * 16530) < 1 / 6000 := by
  have h1 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 74437 / 100000 by norm_num)
  have he := Real.exp_one_gt_d9
  have h8 : (2.7182818283 : ℝ) ^ 8 < exp 1 ^ 8 := by gcongr
  have hsplit : exp ((529 / 10 ^ 6) * 16530) = exp 1 ^ 8 * exp (74437 / 100000) := by
    rw [Real.exp_one_pow, ← exp_add]; norm_num
  have hbig : 6000 < exp ((529 / 10 ^ 6) * 16530) := by
    rw [hsplit]
    have : 0 < exp (74437 / 100000) := exp_pos _
    nlinarith
  rw [neg_mul, exp_neg, inv_lt_comm₀ (exp_pos _) (by norm_num)]
  linarith

/-- `e^{-166c} ≤ 1 - 83/1000` for `c = 529/10⁶`, from `e^{166c} ≥ 1 + 166c + (166c)²/2`. -/
private theorem fcLateSurvival_rho_le : exp (-(529 / 10 ^ 6) * 166) ≤ 1 - 83 / 1000 := by
  have h1 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ (529 / 10 ^ 6) * 166 by norm_num)
  rw [neg_mul, exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
  norm_num at h1 ⊢
  linarith

/-- `𝗀^{-3/2} ≤ 100/101`. -/
private theorem fcLateSurvival_rate_le : (growthRatio : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 100 / 101 := by
  calc (growthRatio : ℝ) ^ (-(3 / 2 : ℝ)) ≤ (growthRatio : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le one_lt_growthRatio_cast.le (by norm_num)
    _ = 100 / 101 := by rw [Real.rpow_neg_one, growthRatio_cast]; norm_num

/-- The deficit majorant `2e^{-c(b_j-14)} + 2b_j^{-3/2} + 2^{-(K_j+1)}` sums to less than
`1/200` over `j < s`. -/
private theorem fcLateSurvival_sum_lt (s : ℕ) :
    ∑ j ∈ Finset.range s, (2 * exp (-(529 / 10 ^ 6) * ((scale j : ℝ) - 14)) +
      2 * (scale j : ℝ) ^ (-(3 / 2 : ℝ)) + (2 : ℝ) ^ (-((cap j : ℤ) + 1))) < 1 / 200 := by
  set E := exp (-(529 / 10 ^ 6) * 16530)
  set ρ := exp (-(529 / 10 ^ 6) * 166)
  set ς := (growthRatio : ℝ) ^ (-(3 / 2 : ℝ))
  have hE : E < 1 / 6000 := fcLateSurvival_exp_neg_lt
  have hE0 : 0 ≤ E := (exp_pos _).le
  have hρ0 : 0 ≤ ρ := (exp_pos _).le
  have hρ : ρ ≤ 1 - 83 / 1000 := fcLateSurvival_rho_le
  have hς0 : 0 ≤ ς := (Real.rpow_pos_of_pos growthRatio_cast_pos _).le
  have hς : ς ≤ 100 / 101 := fcLateSurvival_rate_le
  -- the exponential terms
  have h1 : ∑ j ∈ Finset.range s, 2 * exp (-(529 / 10 ^ 6) * ((scale j : ℝ) - 14)) ≤
      2 * E * (1000 / 83) := by
    calc _ ≤ ∑ j ∈ Finset.range s, 2 * E * ρ ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (exp_neg_mul_scale_sub_fourteen_le j) (by norm_num)
      _ = 2 * E * ∑ j ∈ Finset.range s, ρ ^ j := by rw [Finset.mul_sum]
      _ ≤ 2 * E * (1 / (1 - ρ)) := by
          gcongr; exact fcLateSurvival_geom_le hρ0 (by linarith) s
      _ ≤ 2 * E * (1000 / 83) := by
          have : 1 / (1 - ρ) ≤ 1000 / 83 := by
            rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
          exact mul_le_mul_of_nonneg_left this (by positivity)
  -- the power terms
  have h2 : ∑ j ∈ Finset.range s, 2 * (scale j : ℝ) ^ (-(3 / 2 : ℝ)) ≤ 202 / 2097152 := by
    calc _ ≤ ∑ j ∈ Finset.range s, 2 * (1 / 2097152) * ς ^ j := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (scale_rpow_neg_three_halves_le j) (by norm_num)
      _ = 2 * (1 / 2097152) * ∑ j ∈ Finset.range s, ς ^ j := by rw [Finset.mul_sum]
      _ ≤ 2 * (1 / 2097152) * (1 / (1 - ς)) := by
          gcongr; exact fcLateSurvival_geom_le hς0 (by linarith) s
      _ ≤ 202 / 2097152 := by
          have : 1 / (1 - ς) ≤ 101 := by
            rw [div_le_iff₀ (by linarith)]; linarith
          linarith
  -- the cap terms
  have h3 : ∑ j ∈ Finset.range s, (2 : ℝ) ^ (-((cap j : ℤ) + 1)) ≤ 112 / 2 ^ 30 := by
    have hcap (j : ℕ) : (2 : ℝ) ^ (-((cap j : ℤ) + 1)) = (1 / 2) ^ 30 * (1 / 2) ^ (j / 56) := by
      rw [two_zpow_neg_cap_add_one, cap, ← pow_add]
      norm_num
      ring_nf
    simp only [hcap, ← Finset.mul_sum]
    have := fcLateSurvival_sum_pow_div_le (x := 1 / 2) (by norm_num) (by norm_num)
      (p := 56) (by norm_num) s
    norm_num at this ⊢
    linarith
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have : 2 * E * (1000 / 83) < 2 * (1 / 6000) * (1000 / 83) := by gcongr
  have h30 : (112 : ℝ) / 2 ^ 30 < 1 / 10 ^ 6 := by norm_num
  linarith

/-- **Survival of the central masses**. For every `s ∈ ℕ`,
`∏_{j=0}^{s-1} 𝐩(𝒞(b_j, K_j)) > 199/200`. -/
@[collatz_pos_dens "lem_fc_late_survival"]
theorem lt_prod_geomMass_centralFamily (s : ℕ) :
    (199 / 200 : ℝ≥0∞) <
      ∏ j ∈ Finset.range s, geomMass (centralFamily (scale j) (cap j)) := by
  set p : ℕ → ℝ≥0∞ := fun j => geomMass (centralFamily (scale j) (cap j))
  set f : ℕ → ℝ := fun j => 2 * exp (-(529 / 10 ^ 6) * ((scale j : ℝ) - 14)) +
    2 * (scale j : ℝ) ^ (-(3 / 2 : ℝ)) + (2 : ℝ) ^ (-((cap j : ℤ) + 1))
  have hf0 (j : ℕ) : 0 ≤ f j := by positivity
  set A : ℝ := ∑ j ∈ Finset.range s, f j
  have hA : A < 1 / 200 := fcLateSurvival_sum_lt s
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun j _ => hf0 j
  have hsum : ∑ j ∈ Finset.range s, (1 - p j) ≤ ENNReal.ofReal A := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ => hf0 j]
    exact Finset.sum_le_sum fun j _ => one_sub_geomMass_centralFamily_le_exp_add_rpow j
  calc (199 / 200 : ℝ≥0∞) = ENNReal.ofReal (199 / 200) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    _ < ENNReal.ofReal (1 - A) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    _ = 1 - ENNReal.ofReal A := by
        rw [ENNReal.ofReal_sub _ hA0, ENNReal.ofReal_one]
    _ ≤ 1 - ∑ j ∈ Finset.range s, (1 - p j) := tsub_le_tsub_left hsum _
    _ ≤ ∏ j ∈ Finset.range s, (1 - (1 - p j)) := one_sub_sum_le_prod_one_sub_ennreal _ _
    _ ≤ ∏ j ∈ Finset.range s, p j := Finset.prod_le_prod fun _ _ => tsub_tsub_le

end CollatzPosDens
