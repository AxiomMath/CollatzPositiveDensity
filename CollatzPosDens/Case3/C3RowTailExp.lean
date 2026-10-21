/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnRawMassFormula
public import CollatzPosDens.Renewal.RnHoeffding

/-!
# Exponential tail of the raw-prefix rows

Let `ω ≥ 680` and `l` be integers with `ω - 127 ≤ l ≤ ω`. Then the raw-prefix masses
`𝖱(r - 1, l)` with `r > ⌊9ω/32⌋` sum to at most `exp(-2ω/289)`.

Put `g = ⌊9ω/32⌋ ≥ 1` and `N = l - 1`, so `1 ≤ N ≤ ω - 1`. For `r > g`,
`𝖱(r - 1, l) = binom(N, 2r - 3) 2^{-l}`, and distinct `r` give distinct indices
`i = 2r - 3 ≥ 2g - 1`.
Such an index satisfies `i - N/2 ≥ 9ω/16 - 3 - (ω - 1)/2 = ω/16 - 5/2 ≥ ω/17`, so Hoeffding's
inequality bounds the binomial weight `∑ binom(N, i) 2^{-N}` of these indices by
`2 exp(-2ω²/(289 N)) ≤ 2 exp(-2ω/289)`, and the tail is at most half of it.

## Main results

* `CollatzPosDens.sum_rawMass_late_tail_le_exp`: the exponential tail bound, for every finite set
  of indices `r > ⌊9ω/32⌋`.

## Implementation notes

The sum over all integers `r > ⌊9ω/32⌋` has only finitely many nonzero terms, all of them
nonnegative, and `r - 1 ≥ 1` is a natural number. The bound is therefore stated for the sum over an
arbitrary finite set of natural numbers `r > ⌊9ω/32⌋`, which is equivalent to the bound on the
whole tail.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset Real

/-- **Exponential tail of the raw-prefix rows.** For integers `ω ≥ 680` and `l` with
`ω - 127 ≤ l ≤ ω`, and every finite set `s` of indices `r > ⌊9ω/32⌋`,
`∑_{r ∈ s} 𝖱(r - 1, l) ≤ exp(-2ω/289)`. -/
@[collatz_pos_dens "lem_c3_row_tail_exp"]
theorem sum_rawMass_late_tail_le_exp {ω l : ℤ} (hω : 680 ≤ ω) (hl : ω - 127 ≤ l)
    (hlω : l ≤ ω) (s : Finset ℕ) (hs : ∀ r ∈ s, ⌊9 * (ω : ℝ) / 32⌋₊ < r) :
    ∑ r ∈ s, rawMass (r - 1) l ≤ exp (-(2 * (ω : ℝ) / 289)) := by
  set w : ℝ := (ω : ℝ) with hw
  have hw0 : (680 : ℝ) ≤ w := by rw [hw]; exact_mod_cast hω
  set g : ℕ := ⌊9 * w / 32⌋₊ with hg
  have hg_lt : 9 * w / 32 < g + 1 := Nat.lt_floor_add_one _
  have hg1 : 1 ≤ g := by
    rw [hg]; exact Nat.le_floor (by push_cast; linarith)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, l = n + 2 := ⟨(l - 2).toNat, by omega⟩
  subst hn
  have hnω : (n : ℝ) + 2 ≤ w := by
    rw [hw]; exact_mod_cast hlω
  set N : ℕ := n + 1 with hN
  have hform : ∀ r ∈ s, rawMass (r - 1) ((n : ℤ) + 2) =
      (N.choose (2 * r - 3) : ℝ) * (2 : ℝ) ^ (-((n : ℤ) + 2)) := by
    intro r hr
    have := hs r hr
    rw [rawMass_eq_choose (by omega), show (((n : ℤ) + 2 - 1).toNat) = N by omega,
      show 2 * (r - 1) - 1 = 2 * r - 3 by omega]
  rw [sum_congr rfl hform, ← sum_mul]
  set u : ℝ := w / 17 with hu
  have hT_le : ∑ r ∈ s, (N.choose (2 * r - 3) : ℝ) ≤ ∑ i ∈ (range (N + 1)).filter
      (fun i : ℕ => u ≤ |(i : ℝ) - (N : ℝ) / 2|), (N.choose i : ℝ) := by
    have h1 : ∑ r ∈ s, N.choose (2 * r - 3) =
        ∑ r ∈ s.filter (fun r => 2 * r - 3 ≤ N), N.choose (2 * r - 3) := by
      rw [sum_filter_of_ne]
      intro r _ hr
      by_contra h
      exact hr (Nat.choose_eq_zero_of_lt (by omega))
    have h2 : (s.filter (fun r => 2 * r - 3 ≤ N)).image (fun r => 2 * r - 3) ⊆
        (range (N + 1)).filter (fun i : ℕ => u ≤ |(i : ℝ) - (N : ℝ) / 2|) := by
      intro i hi
      simp only [mem_image, mem_filter] at hi
      obtain ⟨r, ⟨hr, hr3⟩, rfl⟩ := hi
      refine mem_filter.2 ⟨mem_range.2 (by omega), ?_⟩
      have hgr := hs r hr
      have hcast : ((2 * r - 3 : ℕ) : ℝ) = 2 * (r : ℝ) - 3 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hr' : (g : ℝ) + 1 ≤ r := by exact_mod_cast hgr
      refine le_trans ?_ (le_abs_self _)
      rw [hcast, hu, hN]
      push_cast
      linarith
    have hinj : Set.InjOn (fun r : ℕ => 2 * r - 3) (s.filter (fun r => 2 * r - 3 ≤ N)) := by
      intro a ha b hb h
      have ha' := hs a (mem_filter.1 ha).1
      have hb' := hs b (mem_filter.1 hb).1
      simp only at h
      omega
    have hnat : ∑ r ∈ s, N.choose (2 * r - 3) ≤ ∑ i ∈ (range (N + 1)).filter
        (fun i : ℕ => u ≤ |(i : ℝ) - (N : ℝ) / 2|), N.choose i := by
      rw [h1, ← sum_image (f := fun i => N.choose i) hinj]
      exact sum_le_sum_of_subset h2
    exact_mod_cast hnat
  have hH := binomial_tail_hoeffding N (by omega) u (by rw [hu]; positivity)
  rw [← sum_div] at hH
  have hpos : (0 : ℝ) < 2 ^ N := by positivity
  have hTH : (∑ r ∈ s, (N.choose (2 * r - 3) : ℝ)) / 2 ^ N ≤ 2 * exp (-(2 * w / 289)) := by
    refine (div_le_div_of_nonneg_right hT_le hpos.le).trans (hH.trans ?_)
    refine mul_le_mul_of_nonneg_left (exp_le_exp.2 (neg_le_neg ?_)) (by norm_num)
    rw [hu]
    have hN0 : (0 : ℝ) < (N : ℝ) := by positivity
    rw [div_le_div_iff₀ (by norm_num) hN0]
    have : (N : ℝ) ≤ w := by rw [hN]; push_cast; linarith
    nlinarith
  rw [zpow_neg, show ((n : ℤ) + 2) = ((N + 1 : ℕ) : ℤ) by rw [hN]; push_cast; ring,
    zpow_natCast, pow_succ, ← div_eq_mul_inv]
  rw [div_le_iff₀ hpos] at hTH
  rw [div_le_iff₀ (by positivity)]
  nlinarith [exp_pos (-(2 * w / 289))]

end CollatzPosDens
