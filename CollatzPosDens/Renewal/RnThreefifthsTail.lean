/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnHorTail

/-!
# The first-passage law beyond the window `|r - s/4| < s^{3/5}`

For an integer `s ≥ 1`, the mass of the first-passage law `F_s` on the columns `r` with
`|r - s/4| ≥ s^{3/5}` satisfies
$$\sum_{|r - s/4| \ge s^{3/5}}\ \sum_{\ell \in \mathbb{Z}} \mathsf F_s(r, \ell)
  \le 2^{55} \exp\bigl(-s^{1/5}/65536\bigr).$$

This is `CollatzPosDens.tsum_firstPassageLaw_hor_tail_le` at `u = s^{3/5}`: since `1 + s ≤ 2s`,
one has `u² / (2^{15}(1 + s)) ≥ s^{6/5} / (2^{16} s) = s^{1/5} / 65536`, and
`u / 256 ≥ s^{1/5} / 65536` because `s ≥ 1`; so both exponentials are at most
`exp(-s^{1/5}/65536)`.

## Main results

* `CollatzPosDens.tsum_firstPassageLaw_threeFifths_tail_le`: the tail bound at scale
  `s^{3/5}`.

## Implementation notes

The sum over `r` with `|r - s/4| ≥ s^{3/5}` is the unconditional sum over the subtype of such
`r`; its summability is `CollatzPosDens.summable_firstPassageLaw_hor_tail`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Real

/-- **Tail of the first-passage law at scale `s^{3/5}`.** For `s ≥ 1`,
`∑_{|r - s/4| ≥ s^{3/5}} ∑_{ℓ ∈ ℤ} F_s(r, ℓ) ≤ 2^{55} exp(-s^{1/5} / 65536)`. -/
@[collatz_pos_dens "lem_rn_threefifths_tail"]
theorem tsum_firstPassageLaw_threeFifths_tail_le (s : ℕ) (hs : 1 ≤ s) :
    ∑' r : {r : ℤ // (s : ℝ) ^ (3 / 5 : ℝ) ≤ |(r : ℝ) - s / 4|}, ∑' ℓ : ℤ,
        firstPassageLaw s ((r : ℤ), ℓ) ≤
      2 ^ 55 * exp (-((s : ℝ) ^ (1 / 5 : ℝ) / 65536)) := by
  have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < s := by linarith
  set u : ℝ := (s : ℝ) ^ (1 / 5 : ℝ) with hu
  have hu1 : 1 ≤ u := one_le_rpow hs1 (by norm_num)
  have ht : (s : ℝ) ^ (3 / 5 : ℝ) = u ^ 3 := by
    rw [hu, ← rpow_natCast, ← rpow_mul hs0.le]; norm_num
  have ht2 : ((s : ℝ) ^ (3 / 5 : ℝ)) ^ 2 = s * u := by
    rw [hu, ← rpow_natCast, ← rpow_mul hs0.le, ← rpow_one_add' hs0.le (by norm_num)]
    norm_num
  refine (tsum_firstPassageLaw_hor_tail_le s _).trans ?_
  have h1 : exp (-(((s : ℝ) ^ (3 / 5 : ℝ)) ^ 2 / (2 ^ 15 * (1 + s)))) ≤
      exp (-(u / 65536)) := by
    rw [exp_le_exp, neg_le_neg_iff, ht2, div_le_div_iff₀ (by norm_num) (by positivity)]
    nlinarith
  have h2 : exp (-((s : ℝ) ^ (3 / 5 : ℝ) / 256)) ≤ exp (-(u / 65536)) := by
    rw [exp_le_exp, neg_le_neg_iff, ht]
    nlinarith [mul_le_mul hu1 hu1 zero_le_one (by linarith : (0 : ℝ) ≤ u)]
  linarith

end CollatzPosDens
