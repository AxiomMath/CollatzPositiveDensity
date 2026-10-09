/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Clog
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.PhRatio
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.DeficitCentral
public import CollatzPosDens.FirstCrossing.ScalesB444
public import CollatzPosDens.FirstCrossing.ScalesGrowth
public import CollatzPosDens.FirstCrossing.ScalesLateLower
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Late survival of the central families

For every integer `s ≥ 444`, the central families along the scales `b_j` with caps `K_j`
survive with probability bounded below uniformly:
$$\prod_{j=444}^{s-1}\mathbf p(\mathcal C(b_j,K_j)) > \frac59.$$

Write `d_j = 1 - 𝐩(𝒞(b_j, K_j))`. For deficits `d_j ∈ [0, 1]` one has
`∏ (1 - d_j) ≥ 1 - ∑ d_j`. For `j = 444 + t` and `k = ⌊t/71⌋`, the growth of the scales gives
`b_j ≥ 16544 𝗀^t ≥ 16544 · 2^k`, hence `lg b_j ≥ 14 + k` and `min(L², 32L) ≥ 196 + 29k`. The
deficit bound for the central family then yields
`d_j ≤ 2e^{-98/15} 2^{-k} + 2^{-(30 + ⌊t/32⌋)}`, using `e^{29/30} > 2` and
`K_j + 1 ≥ 30 + ⌊t/32⌋`. Each value of `k` occurs for at most `71` values of `t`, so with
`e^{98/15} > 650` the deficits sum to less than `284/650 + 1/2048 < 4/9`.

## Main results

* `CollatzPosDens.five_ninths_lt_prod_geomMass_centralFamily`: the product bound above.
* `CollatzPosDens.one_sub_sum_le_prod_one_sub_ennreal`: `1 - ∑ a_i ≤ ∏ (1 - a_i)` in
  `ℝ≥0∞`, with truncated subtraction.

## Implementation notes

The masses live in `ℝ≥0∞` and `d_j` is the truncated difference `1 - 𝐩(𝒞(b_j, K_j))`. The
inequality `1 - ∑ a_i ≤ ∏ (1 - a_i)` holds in `ℝ≥0∞` for arbitrary `a_i` (a summand `a_i ≥ 1`
makes both sides vanish), and `𝐩 ≥ 1 - (1 - 𝐩)` holds for any `𝐩`, so the bound
`𝐩(𝒞(b_j, K_j)) ≤ 1` (from prefix-disjointness) used in the source to place `d_j` in `[0, 1]`
is not needed. The hypothesis `s ≥ 444` is dropped: for `s ≤ 444` the product is empty and
equals `1`. The exponential estimates use the quadratic lower bound `1 + x + x²/2 ≤ eˣ` and
`e > 2.7182818283` in place of longer partial sums.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
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
  have hgeom : ∀ M, ∑ k ∈ Finset.range M, x ^ k ≤ 1 / (1 - x) := by
    intro M
    rw [geom_sum_eq hx1.ne, ← neg_div_neg_eq, neg_sub, neg_sub]
    have : 0 ≤ x ^ M := pow_nonneg hx0 M
    gcongr
    linarith
  calc ∑ t ∈ Finset.range N, x ^ (t / p)
      ≤ ∑ t ∈ Finset.range (p * N), x ^ (t / p) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.range_subset_range.2 (Nat.le_mul_of_pos_left N hp))
          fun _ _ _ => pow_nonneg hx0 _
    _ = p * ∑ k ∈ Finset.range N, x ^ k := hblock N
    _ ≤ p * (1 / (1 - x)) := by gcongr; exact hgeom N
    _ = p / (1 - x) := by ring

/-- `e^{-29/30} ≤ 1/2`. -/
private theorem fcLateSurvival_exp_neg_le : exp (-(29 / 30)) ≤ 1 / 2 := by
  have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 29 / 30 by norm_num)
  rw [exp_neg, inv_le_comm₀ (exp_pos _) (by norm_num)]
  linarith

/-- `e^{-98/15} < 1/650`. -/
private theorem fcLateSurvival_exp_neg_lt : exp (-(98 / 15)) < 1 / 650 := by
  have h1 := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 8 / 15 by norm_num)
  have he := Real.exp_one_gt_d9
  have h6 : (2.7182818283 : ℝ) ^ 6 < exp 1 ^ 6 := by gcongr
  have hsplit : exp (98 / 15) = exp 1 ^ 6 * exp (8 / 15) := by
    rw [Real.exp_one_pow, ← exp_add]; norm_num
  have hbig : 650 < exp (98 / 15) := by
    rw [hsplit]
    have : 0 < exp (8 / 15) := exp_pos _
    nlinarith
  rw [exp_neg, inv_lt_comm₀ (exp_pos _) (by norm_num)]
  linarith

/-- The deficit at scale `444 + t`, real-valued majorant. -/
private noncomputable def fcLateSurvivalBound (t : ℕ) : ℝ :=
  2 * exp (-(98 / 15)) * (1 / 2) ^ (t / 71) + (1 / 2) ^ 30 * (1 / 2) ^ (t / 32)

private theorem fcLateSurvivalBound_nonneg (t : ℕ) : 0 ≤ fcLateSurvivalBound t := by
  unfold fcLateSurvivalBound; positivity

private theorem fcLateSurvival_exp_lg_le (t : ℕ) :
    exp (-min ((lg (scale (444 + t)) : ℝ) ^ 2) (32 * (lg (scale (444 + t)) : ℝ)) / 30) ≤
      exp (-(98 / 15)) * (1 / 2) ^ (t / 71) := by
  have hLR : (14 : ℝ) + ((t / 71 : ℕ) : ℝ) ≤ lg (scale (444 + t)) := by
    exact_mod_cast fourteen_add_div_seventy_one_le_lg_scale t
  set k : ℝ := ((t / 71 : ℕ) : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  have hkk : k ≤ k ^ 2 := by
    rw [hk]; exact_mod_cast Nat.le_self_pow (by norm_num) _
  set L : ℝ := ((lg (scale (444 + t)) : ℕ) : ℝ)
  have hm : 196 + 29 * k ≤ min (L ^ 2) (32 * L) :=
    le_min (by nlinarith [mul_le_mul hLR hLR (by linarith) (by linarith)]) (by linarith)
  calc exp (-min (L ^ 2) (32 * L) / 30) ≤ exp (-(98 / 15) + (t / 71 : ℕ) * (-(29 / 30))) := by
        apply exp_le_exp.2
        rw [← hk]
        linarith
    _ = exp (-(98 / 15)) * exp (-(29 / 30)) ^ (t / 71) := by
        rw [exp_add, exp_nat_mul]
    _ ≤ exp (-(98 / 15)) * (1 / 2) ^ (t / 71) := by
        gcongr; exact fcLateSurvival_exp_neg_le

/-- `1 - 𝐩(𝒞(b_{444+t}, K_{444+t})) ≤ 2e^{-98/15} 2^{-⌊t/71⌋} + 2^{-30} 2^{-⌊t/32⌋}`. -/
private theorem fcLateSurvival_deficit_le (t : ℕ) :
    1 - geomMass (centralFamily (scale (444 + t)) (cap (444 + t))) ≤
      ENNReal.ofReal (fcLateSurvivalBound t) := by
  have hu : 16384 ≤ scale (444 + t) := by
    have := scale_monotone (show 444 ≤ 444 + t by omega)
    rw [scale_444] at this; omega
  refine (one_sub_geomMass_centralFamily_le hu (cap (444 + t))).trans ?_
  have hmain := fcLateSurvival_exp_lg_le t
  have hcap : (2⁻¹ : ℝ≥0∞) ^ (cap (444 + t) + 1) ≤
      ENNReal.ofReal ((1 / 2) ^ 30 * (1 / 2) ^ (t / 32)) := by
    rw [← pow_add, ENNReal.ofReal_pow (by norm_num), one_div,
      ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
    exact pow_le_pow_right_of_le_one' (by norm_num) (by unfold cap; omega)
  unfold fcLateSurvivalBound
  rw [ENNReal.ofReal_add (by positivity) (by positivity), mul_assoc,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  gcongr

/-- The deficits sum to less than `4/9`. -/
private theorem fcLateSurvival_sum_lt (N : ℕ) :
    ∑ t ∈ Finset.range N, fcLateSurvivalBound t < 4 / 9 := by
  have h71 := fcLateSurvival_sum_pow_div_le (x := 1 / 2) (by norm_num) (by norm_num)
    (p := 71) (by norm_num) N
  have h32 := fcLateSurvival_sum_pow_div_le (x := 1 / 2) (by norm_num) (by norm_num)
    (p := 32) (by norm_num) N
  have he := fcLateSurvival_exp_neg_lt
  have he0 := (exp_pos (-(98 / 15))).le
  simp only [fcLateSurvivalBound, Finset.sum_add_distrib, ← Finset.mul_sum]
  norm_num at h71 h32 ⊢
  nlinarith

/-- **Late survival**. For every `s`, `∏_{j=444}^{s-1} 𝐩(𝒞(b_j, K_j)) > 5/9` (for `s ≤ 444` the
product is empty). -/
@[collatz_pos_dens "lem_fc_late_survival"]
theorem five_ninths_lt_prod_geomMass_centralFamily (s : ℕ) :
    (5 / 9 : ℝ≥0∞) <
      ∏ j ∈ Finset.Ico 444 s, geomMass (centralFamily (scale j) (cap j)) := by
  rw [Finset.prod_Ico_eq_prod_range]
  set N := s - 444
  set p : ℕ → ℝ≥0∞ := fun t => geomMass (centralFamily (scale (444 + t)) (cap (444 + t)))
  have hsum : ∑ t ∈ Finset.range N, (1 - p t) ≤
      ENNReal.ofReal (∑ t ∈ Finset.range N, fcLateSurvivalBound t) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun t _ => fcLateSurvivalBound_nonneg t]
    exact Finset.sum_le_sum fun t _ => fcLateSurvival_deficit_le t
  have hlt := fcLateSurvival_sum_lt N
  calc (5 / 9 : ℝ≥0∞) = ENNReal.ofReal (5 / 9) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]; simp
    _ < ENNReal.ofReal (1 - ∑ t ∈ Finset.range N, fcLateSurvivalBound t) :=
        (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    _ = 1 - ENNReal.ofReal (∑ t ∈ Finset.range N, fcLateSurvivalBound t) := by
        rw [ENNReal.ofReal_sub _ (Finset.sum_nonneg fun t _ => fcLateSurvivalBound_nonneg t),
          ENNReal.ofReal_one]
    _ ≤ 1 - ∑ t ∈ Finset.range N, (1 - p t) := tsub_le_tsub_left hsum _
    _ ≤ ∏ t ∈ Finset.range N, (1 - (1 - p t)) := one_sub_sum_le_prod_one_sub_ennreal _ _
    _ ≤ ∏ t ∈ Finset.range N, p t := Finset.prod_le_prod fun _ _ => tsub_tsub_le

end CollatzPosDens
