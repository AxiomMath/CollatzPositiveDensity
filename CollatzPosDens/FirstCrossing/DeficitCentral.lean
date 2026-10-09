/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Clog
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.DeficitWindow
public import CollatzPosDens.FirstCrossing.Width
public import Mathlib.Tactic.IntervalCases

/-!
# Geometric deficit of the central family

Let `u ≥ 16384` and `K ≥ 0` be integers and `L = lg u`. Then the central family `𝒞(u, K)`
misses little geometric mass:
$$1 - \mathbf p(\mathcal C(u,K)) \le 2\exp\bigl(-\min(L^2, 32L)/30\bigr) + 2^{-(K+1)}.$$

Put `m = min(L², 32L)` and `w = ⌈√(u m)⌉`. Since `u` is large compared with `L`, one has
`64 m + 14 ≤ u`, whence `1000 ≤ w ≤ u/8`; and since `m ≤ 32L`, also `w ≤ wd(u)`. So the
central window `𝒱_w` of words of `𝒲(u, r_u, K)` with length in `[u - w, u + w]` lies in
`𝒞(u, K)`, and the deficit bound for central windows gives
`1 - 𝐩(𝒞(u, K)) ≤ 2 exp(-2(207w/500)²/(9(u + w))) + 2^{-(K+1)}`. With `w² ≥ u m` and
`u + w ≤ 9u/8` the exponent is at least `c m` where `c = (16/81)(207/500)² > 1/30`.

## Main results

* `CollatzPosDens.one_sub_geomMass_centralFamily_le`: the bound above.

## Implementation notes

The proof in [mazur2026] splits into the cases `L ≤ 32` (window `⌈√u L⌉`) and `L ≥ 33`
(window `wd(u)`); these are the two values of the single window `⌈√(u·min(L², 32L))⌉` used
here. As in `CollatzPosDens.centralFamily`, `u` and `K` are natural numbers, and the bound is
stated in `ℝ≥0∞`, where `1 - 𝐩(𝒞(u, K))` is truncated subtraction.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open InformationTheory Real

namespace CollatzPosDens

/-- `2048 L + 13 ≤ 2^(L-1)` for `L ≥ 33`. -/
private lemma deficitCentral_pow_aux : ∀ L, 33 ≤ L → 2048 * L + 13 ≤ 2 ^ (L - 1) := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have : 2 ^ (n + 1 - 1) = 2 * 2 ^ (n - 1) := by
      rw [show n + 1 - 1 = (n - 1) + 1 by omega, pow_succ]; ring
    omega

/-- For `u ≥ 16384`, `64 min(L², 32L) + 14 ≤ u` where `L = lg u`. -/
private lemma deficitCentral_size {u : ℕ} (hu : 16384 ≤ u) :
    14 ≤ lg u ∧ 64 * min (lg u ^ 2) (32 * lg u) + 14 ≤ u := by
  have h14 : 14 ≤ lg u := by
    by_contra h
    have := lg_le_iff_le_two_pow.1 (show lg u ≤ 13 by omega)
    norm_num at this; omega
  refine ⟨h14, ?_⟩
  have hlt : 2 ^ (lg u - 1) < u := by
    by_contra h
    have := lg_le_iff_le_two_pow.2 (not_lt.1 h)
    omega
  set L := lg u
  rcases le_or_gt L 15 with h | h
  · have : min (L ^ 2) (32 * L) ≤ 225 :=
      (min_le_left _ _).trans (by nlinarith)
    omega
  rcases le_or_gt L 32 with h' | h'
  · have key : 64 * min (L ^ 2) (32 * L) + 14 ≤ 2 ^ (L - 1) + 1 := by
      interval_cases L <;> norm_num
    omega
  · have := deficitCentral_pow_aux L (by omega)
    have : min (L ^ 2) (32 * L) ≤ 32 * L := min_le_right _ _
    omega

/-- **Deficit of the central family.** For `u ≥ 16384`, any `K`, and `L = lg u`,
`1 - 𝐩(𝒞(u, K)) ≤ 2 exp(-min(L², 32L)/30) + 2^{-(K+1)}`. -/
@[collatz_pos_dens "lem_deficit_central"]
theorem one_sub_geomMass_centralFamily_le {u : ℕ} (hu : 16384 ≤ u) (K : ℕ) :
    1 - geomMass (centralFamily u K) ≤
      2 * ENNReal.ofReal (exp (-min ((lg u : ℝ) ^ 2) (32 * (lg u : ℝ)) / 30)) +
        2⁻¹ ^ (K + 1) := by
  obtain ⟨h14, hsize⟩ := deficitCentral_size hu
  set L := lg u with hL
  set m : ℕ := min (L ^ 2) (32 * L) with hm
  have hm196 : 196 ≤ m := by
    rw [hm]; refine le_min (by nlinarith) (by omega)
  set w : ℕ := ⌈√((u : ℝ) * m)⌉₊ with hw
  have hum0 : (0 : ℝ) ≤ (u : ℝ) * m := by positivity
  have hsq : (u : ℝ) * m ≤ (w : ℝ) ^ 2 := by
    have h1 : √((u : ℝ) * m) ≤ w := Nat.le_ceil _
    have h2 := Real.sq_sqrt hum0
    nlinarith [Real.sqrt_nonneg ((u : ℝ) * m)]
  have hw8 : w ≤ u / 8 := by
    rw [hw, Nat.ceil_le]
    rw [Real.sqrt_le_left (by positivity)]
    have hq : u ≤ 8 * (u / 8) + 7 := by omega
    have hnat : u * m ≤ (u / 8) * (u / 8) := by
      set q := u / 8
      nlinarith
    rw [sq]; exact_mod_cast hnat
  have hwu : 8 * w ≤ u := by omega
  have hw1000 : 1000 ≤ w := by
    have h1 : (1000 : ℝ) ≤ √((u : ℝ) * m) := by
      rw [Real.le_sqrt (by norm_num) hum0]
      have : (16384 * 196 : ℝ) ≤ (u : ℝ) * m := by
        have : (16384 : ℝ) ≤ u := by exact_mod_cast hu
        have : (196 : ℝ) ≤ m := by exact_mod_cast hm196
        nlinarith
      linarith
    have h2 := h1.trans (Nat.le_ceil (√((u : ℝ) * m)))
    rw [← hw] at h2
    exact_mod_cast h2
  have hwd : w ≤ wd u := by
    refine le_wd_iff.2 ⟨Nat.ceil_mono (Real.sqrt_le_sqrt ?_), by omega⟩
    have : (m : ℝ) ≤ 32 * L := by exact_mod_cast min_le_right _ _
    have : (0 : ℝ) ≤ u := by positivity
    nlinarith
  have hsub : {v ∈ firstCrossing u (rb u) K | u - w ≤ v.length ∧ v.length ≤ u + w} ⊆
      centralFamily u K := by
    rintro v ⟨hv, h1, h2⟩
    exact (mem_centralFamily_of_large (by omega)).2 ⟨hv, by omega, by omega⟩
  refine (tsub_le_tsub_left (geomMass_mono hsub) 1).trans
    ((one_sub_geomMass_deficitWindow_le hw1000 hwu).trans ?_)
  refine add_le_add_left (mul_le_mul_right
    (ENNReal.ofReal_le_ofReal (exp_le_exp.2 ?_)) 2) _
  have hmR : min ((L : ℝ) ^ 2) (32 * (L : ℝ)) = m := by rw [hm]; push_cast; rfl
  rw [hmR]
  have hw0 : (0 : ℝ) < w := by exact_mod_cast (show 0 < w by omega)
  have hu8 : 8 * (w : ℝ) ≤ u := by exact_mod_cast hwu
  rw [neg_div, neg_mul, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
  have : (m : ℝ) * (u + w) ≤ 9 / 8 * ((u : ℝ) * m) := by
    have : (0 : ℝ) ≤ m := by positivity
    nlinarith
  nlinarith

end CollatzPosDens
