/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Mixing.MxShBinomVariance
public import CollatzPosDens.Mixing.MxShLatticeSum
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.BigOperators.Field

/-!
# The sum of square roots of binomial probabilities

For every integer `N ≥ 1`,
$$\Bigl(\sum_{i=0}^N \sqrt{\tbinom Ni 2^{-N}}\Bigr)^2 \le 4 + \pi \sqrt N .$$

Put `π_i = C(N, i) 2^{-N}` and `w_i = 1 + (2i - N)^2 / N ≥ 1`. The Cauchy–Schwarz inequality
applied to `√π_i = √(π_i w_i) · w_i^{-1/2}` gives
`(∑ √π_i)^2 ≤ (∑ π_i w_i) (∑ w_i⁻¹)`. The binomial theorem and the second moment of the
binomial coefficients (`sum_range_choose_mul_two_mul_sub_sq`) give
`∑ π_i w_i = 1 + N 2^N / (N 2^N) = 2`. Since `(2i - N)^2 / N = (i - N/2)^2 / (√N / 2)^2`, the
Lorentzian lattice sum bound `sum_range_one_div_one_add_sq_div_sq_le` with centre `N/2` and width
`√N / 2` gives `∑ w_i⁻¹ ≤ 2 + (π/2) √N`. Multiplying gives the claim.

## Main results

* `CollatzPosDens.sq_sum_range_sqrt_choose_div_two_pow_le`: the bound
  `(∑_{i=0}^N √(C(N, i) / 2^N))^2 ≤ 4 + π √N` for `N ≥ 1`.

## References

* [Mazur, *Collatz positive density*], §12.11.
-/

@[expose] public section

namespace CollatzPosDens

open Real Finset

/-- **Square-root binomial sum**: for `N ≥ 1`,
`(∑_{i=0}^N √(C(N, i) 2^{-N}))^2 ≤ 4 + π √N`. -/
@[collatz_pos_dens "lem_mx_sh_sqrt_binom"]
theorem sq_sum_range_sqrt_choose_div_two_pow_le {N : ℕ} (hN : 1 ≤ N) :
    (∑ i ∈ range (N + 1), √((N.choose i : ℝ) / 2 ^ N)) ^ 2 ≤ 4 + π * √N := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set p : ℕ → ℝ := fun i => (N.choose i : ℝ) / 2 ^ N with hp
  set w : ℕ → ℝ := fun i => 1 + (2 * (i : ℝ) - N) ^ 2 / N with hw
  have hp0 : ∀ i, 0 ≤ p i := fun i => by positivity
  have hw1 : ∀ i, 1 ≤ w i := fun i => by
    simp only [hw]; linarith [show 0 ≤ (2 * (i : ℝ) - N) ^ 2 / N by positivity]
  have hw0 : ∀ i, 0 < w i := fun i => by linarith [hw1 i]
  have hcs : (∑ i ∈ range (N + 1), √(p i)) ^ 2 ≤
      (∑ i ∈ range (N + 1), p i * w i) * ∑ i ∈ range (N + 1), 1 / w i := by
    have := sum_mul_sq_le_sq_mul_sq (range (N + 1)) (fun i => √(p i * w i))
      (fun i => 1 / √(w i))
    have e1 : ∀ i, √(p i * w i) * (1 / √(w i)) = √(p i) := fun i => by
      rw [sqrt_mul (hp0 i), mul_one_div, mul_div_assoc, div_self (sqrt_pos.2 (hw0 i)).ne',
        mul_one]
    have e2 : ∀ i, √(p i * w i) ^ 2 = p i * w i := fun i =>
      sq_sqrt (mul_nonneg (hp0 i) (hw0 i).le)
    have e3 : ∀ i, (1 / √(w i)) ^ 2 = 1 / w i := fun i => by
      rw [div_pow, one_pow, sq_sqrt (hw0 i).le]
    simpa only [e1, e2, e3] using this
  have hmass : ∑ i ∈ range (N + 1), p i * w i = 2 := by
    have hvar := sum_range_choose_mul_two_mul_sub_sq ℝ N
    have hsum : ∑ i ∈ range (N + 1), (N.choose i : ℝ) = 2 ^ N := by
      exact_mod_cast Nat.sum_range_choose N
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    have : ∀ i ∈ range (N + 1), p i * w i =
        (N.choose i : ℝ) / 2 ^ N + (N.choose i : ℝ) * (2 * (i : ℝ) - N) ^ 2 / (N * 2 ^ N) :=
      fun i _ => by simp only [hp, hw]; field_simp
    rw [sum_congr rfl this, sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, hsum, hvar,
      div_self h2N.ne', div_self (by positivity)]
    norm_num
  have hrec : ∑ i ∈ range (N + 1), 1 / w i ≤ 2 + π / 2 * √N := by
    have hsq : (√N / 2 : ℝ) ^ 2 = N / 4 := by rw [div_pow, sq_sqrt hNpos.le]; norm_num
    have := sum_range_one_div_one_add_sq_div_sq_le ((N : ℝ) / 2)
      (show (0 : ℝ) < √N / 2 by positivity) N
    have e : ∀ i : ℕ, 1 / (1 + ((i : ℝ) - N / 2) ^ 2 / (√N / 2) ^ 2) = 1 / w i := fun i => by
      rw [hsq]
      simp only [hw]
      congr 2
      field_simp
      ring
    simp only [e] at this
    linarith
  calc (∑ i ∈ range (N + 1), √((N.choose i : ℝ) / 2 ^ N)) ^ 2
      = (∑ i ∈ range (N + 1), √(p i)) ^ 2 := rfl
    _ ≤ 2 * (2 + π / 2 * √N) := by
        rw [hmass] at hcs
        linarith
    _ = 4 + π * √N := by ring

end CollatzPosDens
