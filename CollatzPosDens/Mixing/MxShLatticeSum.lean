/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# A Lorentzian lattice sum against its integral

For real `c`, real `a > 0` and `N ∈ ℕ`,
$$\sum_{i=0}^N \frac{1}{1 + (i - c)^2 / a^2} \le 2 + \pi a .$$

Write `f(t) = 1 / (1 + (t - c)^2 / a^2)`, which is nondecreasing on `(-∞, c]` and nonincreasing on
`[c, ∞)`, with antiderivative `a · arctan ((t - c) / a)`. An index `i` with `i + 1 ≤ c` has
`f(i) ≤ a (arctan ((i + 1 - c)/a) - arctan ((i - c)/a))`, an index with `i - 1 ≥ c` has
`f(i) ≤ a (arctan ((i - c)/a) - arctan ((i - 1 - c)/a))`, and the at most two indices in the
open interval `(c - 1, c + 1)` contribute at most `1` each. The arctangent increments telescope
to at most `a (π/2 + π/2) = π a`.

## Main results

* `CollatzPosDens.sum_range_one_div_one_add_sq_div_sq_le`: the lattice sum bound
  `∑_{i=0}^N 1 / (1 + (i - c)^2 / a^2) ≤ 2 + π a`.

## Implementation notes

Instead of comparing with the improper integral `∫_ℝ f = π a`, the proof compares each term with an
increment of the arctangent (by the mean value theorem), and telescopes the increments of the
monotone function `Φ(t) = a arctan ((min t c - c)/a) + a arctan ((max (t - 1) c - c)/a)`, whose
total increase is less than `π a`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- On `u ≤ v ≤ 0` the derivative of `arctan` is at least its value at `u`, so
`(v - u) / (1 + u ^ 2) ≤ arctan v - arctan u`. -/
theorem div_one_add_sq_le_arctan_sub_of_nonpos {u v : ℝ} (huv : u ≤ v) (hv : v ≤ 0) :
    (v - u) / (1 + u ^ 2) ≤ arctan v - arctan u := by
  rcases huv.eq_or_lt with rfl | huv
  · simp
  obtain ⟨ξ, hξ, hd⟩ := exists_hasDerivAt_eq_slope arctan (fun t => 1 / (1 + t ^ 2)) huv
    continuous_arctan.continuousOn (fun t _ => hasDerivAt_arctan t)
  have hvu : 0 < v - u := sub_pos.2 huv
  have hξ2 : ξ ^ 2 ≤ u ^ 2 := by nlinarith [hξ.1, hξ.2]
  have h1 : 1 / (1 + u ^ 2) ≤ 1 / (1 + ξ ^ 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [hd, le_div_iff₀ hvu] at h1
  rw [div_eq_mul_one_div, mul_comm]
  exact h1

/-- On `0 ≤ u ≤ v` the derivative of `arctan` is at least its value at `v`, so
`(v - u) / (1 + v ^ 2) ≤ arctan v - arctan u`. -/
theorem div_one_add_sq_le_arctan_sub_of_nonneg {u v : ℝ} (huv : u ≤ v) (hu : 0 ≤ u) :
    (v - u) / (1 + v ^ 2) ≤ arctan v - arctan u := by
  have := div_one_add_sq_le_arctan_sub_of_nonpos (neg_le_neg huv) (neg_nonpos.2 hu)
  rw [arctan_neg, arctan_neg, neg_sq, show -u - -v = v - u by ring] at this
  linarith

/-- The lattice sum of the Lorentzian profile `1 / (1 + (t - c)^2 / a^2)` over `0, 1, …, N` is at
most `2 + π a`. -/
@[collatz_pos_dens "lem_mx_sh_lattice_sum"]
theorem sum_range_one_div_one_add_sq_div_sq_le (c : ℝ) {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∑ i ∈ range (N + 1), 1 / (1 + ((i : ℝ) - c) ^ 2 / a ^ 2) ≤ 2 + π * a := by
  set f : ℝ → ℝ := fun t => 1 / (1 + (t - c) ^ 2 / a ^ 2) with hf
  set Φ : ℝ → ℝ := fun t => a * arctan ((min t c - c) / a) + a * arctan ((max (t - 1) c - c) / a)
    with hΦ
  set B : Finset ℕ := (range (N + 1)).filter (fun i => c - 1 < (i : ℝ) ∧ (i : ℝ) < c + 1) with hB
  have hfle : ∀ t, f t ≤ 1 := fun t => by
    simp only [hf]
    rw [div_le_one (by positivity)]
    linarith [show 0 ≤ (t - c) ^ 2 / a ^ 2 by positivity]
  have hfa : ∀ t, f t = a * ((1 / a) / (1 + ((t - c) / a) ^ 2)) := fun t => by
    simp only [hf, div_pow]
    field_simp
  have harc_mono : ∀ x y : ℝ, x ≤ y → a * arctan ((x - c) / a) ≤ a * arctan ((y - c) / a) :=
    fun x y h => mul_le_mul_of_nonneg_left
      (arctan_strictMono.monotone (div_le_div_of_nonneg_right (by linarith) ha.le)) ha.le
  have hΦmono : ∀ t, Φ t ≤ Φ (t + 1) := fun t => by
    simp only [hΦ]
    exact add_le_add (harc_mono _ _ (min_le_min_right _ (by linarith)))
      (harc_mono _ _ (max_le_max_right _ (by linarith)))
  -- each term is bounded by the increment of `Φ` plus the indicator of `B`
  have hterm : ∀ i ∈ range (N + 1),
      f i ≤ (Φ ((i : ℝ) + 1) - Φ i) + (if i ∈ B then 1 else 0) := by
    intro i hi
    by_cases hiB : i ∈ B
    · simp only [hiB, ite_true]
      linarith [hfle i, hΦmono i]
    simp only [hiB, ite_false, add_zero]
    simp only [hB, mem_filter, not_and, not_lt] at hiB
    rcases le_or_gt ((i : ℝ) + 1) c with hA | hA
    · -- `i + 1 ≤ c`
      have h1 : min ((i : ℝ) + 1) c = i + 1 := min_eq_left hA
      have h2 : min (i : ℝ) c = i := min_eq_left (by linarith)
      have h3 : max ((i : ℝ) + 1 - 1) c = c := max_eq_right (by linarith)
      have h4 : max ((i : ℝ) - 1) c = c := max_eq_right (by linarith)
      simp only [hΦ, h1, h2, h3, h4, sub_self, zero_div, arctan_zero, mul_zero, add_zero]
      rw [hfa, ← mul_sub]
      refine mul_le_mul_of_nonneg_left ?_ ha.le
      have := div_one_add_sq_le_arctan_sub_of_nonpos
        (show ((i : ℝ) - c) / a ≤ ((i : ℝ) + 1 - c) / a from
          div_le_div_of_nonneg_right (by linarith) ha.le)
        (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)
      convert this using 2
      field_simp
      ring
    · -- `i ≥ c + 1`
      have hC : c + 1 ≤ (i : ℝ) := hiB hi (by linarith)
      have h1 : min ((i : ℝ) + 1) c = c := min_eq_right (by linarith)
      have h2 : min (i : ℝ) c = c := min_eq_right (by linarith)
      have h3 : max ((i : ℝ) + 1 - 1) c = i := by
        rw [add_sub_cancel_right]; exact max_eq_left (by linarith)
      have h4 : max ((i : ℝ) - 1) c = i - 1 := max_eq_left (by linarith)
      simp only [hΦ, h1, h2, h3, h4, sub_self, zero_div, arctan_zero, mul_zero, zero_add]
      rw [hfa, ← mul_sub]
      refine mul_le_mul_of_nonneg_left ?_ ha.le
      have := div_one_add_sq_le_arctan_sub_of_nonneg
        (show ((i : ℝ) - 1 - c) / a ≤ ((i : ℝ) - c) / a from
          div_le_div_of_nonneg_right (by linarith) ha.le)
        (div_nonneg (by linarith) ha.le)
      convert this using 2
      field_simp
      ring
  -- the set `B` has at most two elements
  have hBcard : (B.card : ℝ) ≤ 2 := by
    set m : ℤ := ⌊c - 1⌋
    have hmaps : ∀ i ∈ B, ((i : ℤ)) ∈ Finset.Icc (m + 1) (m + 2) := by
      intro i hi
      simp only [hB, mem_filter] at hi
      obtain ⟨-, h1, h2⟩ := hi
      have hm1 : (m : ℝ) ≤ c - 1 := Int.floor_le _
      have hm2 : c - 1 < (m : ℝ) + 1 := Int.lt_floor_add_one _
      rw [Finset.mem_Icc]
      constructor
      · have : (m : ℝ) < (i : ℤ) := by push_cast; linarith
        exact_mod_cast this
      · have : ((i : ℤ) : ℝ) < m + 3 := by push_cast; linarith
        have : (i : ℤ) < m + 3 := by exact_mod_cast this
        omega
    have := Finset.card_le_card_of_injOn (fun i : ℕ => (i : ℤ)) hmaps
      (fun x _ y _ h => by simpa using h)
    rw [Int.card_Icc] at this
    have h2 : B.card ≤ 2 := by omega
    exact_mod_cast h2
  -- the total increase of `Φ` is less than `π a`
  have hΦtot : Φ ((N : ℝ) + 1) - Φ 0 ≤ π * a := by
    simp only [hΦ]
    have e1 : a * arctan ((min ((N : ℝ) + 1) c - c) / a) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ha.le (arctan_zero ▸ arctan_strictMono.monotone
        (div_nonpos_of_nonpos_of_nonneg (by linarith [min_le_right ((N : ℝ) + 1) c]) ha.le))
    have e2 : a * arctan ((max ((N : ℝ) + 1 - 1) c - c) / a) ≤ a * (π / 2) :=
      mul_le_mul_of_nonneg_left (arctan_lt_pi_div_two _).le ha.le
    have e3 : -(a * (π / 2)) ≤ a * arctan ((min (0 : ℝ) c - c) / a) := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left (neg_pi_div_two_lt_arctan _).le ha.le
    have e4 : 0 ≤ a * arctan ((max ((0 : ℝ) - 1) c - c) / a) :=
      mul_nonneg ha.le (arctan_nonneg.2 (div_nonneg (by linarith [le_max_right ((0 : ℝ) - 1) c])
        ha.le))
    nlinarith
  calc ∑ i ∈ range (N + 1), 1 / (1 + ((i : ℝ) - c) ^ 2 / a ^ 2)
      = ∑ i ∈ range (N + 1), f i := rfl
    _ ≤ ∑ i ∈ range (N + 1), ((Φ ((i : ℝ) + 1) - Φ i) + (if i ∈ B then 1 else 0)) :=
        sum_le_sum hterm
    _ = (Φ ((N : ℝ) + 1) - Φ 0) + B.card := by
        rw [sum_add_distrib, sum_boole]
        congr 1
        · have := sum_range_sub (fun n : ℕ => Φ (n : ℝ)) (N + 1)
          simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at this
          exact this
        · rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 (filter_subset _ _)]
    _ ≤ 2 + π * a := by linarith

end CollatzPosDens
