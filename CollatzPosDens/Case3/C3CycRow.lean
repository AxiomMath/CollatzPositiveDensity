/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CycInterval
public import CollatzPosDens.Case3.C3RowPack

/-!
# A periodic cost against a renewal row

Let `g : ℕ → ℝ` be `L`-periodic (of any sign), with mean `μ` over a period and with `D` the range
(maximum minus minimum over `0 ≤ k ≤ L`) of its centred partial sums. Then for `l ≥ 2` and
`a ≥ 0` the row `r ↦ 𝖱(r - 1, l)` of raw-prefix masses satisfies
$$\sum_{r \ge 1} 𝖱(r - 1, l)\, g(r + a) \ge \frac{\mu}{4} - \frac{D}{\sqrt{2(3l - 1)}}.$$

The row `b(r) = 𝖱(r - 1, l)` vanishes at `r ≤ 1` and for `r ≥ l + 2`, sums to `1/4`, has maximum
at most `(2(3l - 1))^{-1/2}`, and is quasi-concave (its superlevel sets are intervals), by
unimodality of the binomial coefficients. Writing `b` as a positive combination
`∑ (λ_i - λ_{i-1}) 𝟙_{I_i}` of indicators of its superlevel intervals, each interval sum of
`g(· + a)` over `I_i` is at least `|I_i| μ - D` by the interval-sum bound for periodic sequences;
summing, `∑ b(r) g(r + a) ≥ μ ∑ b - D max b`.

## Main results

* `CollatzPosDens.tsum_rawMass_mul_periodic_ge`: the lower bound above, together with the
  summability of the row against `g`.

## Implementation notes

The sum over `r ≥ 1` is written over `r' = r - 1 ∈ ℕ`, as `∑' r', 𝖱(r', l) g(r' + 1 + a)`; it has
only finitely many nonzero terms. The layer-cake decomposition is the one of
`CollatzPosDens.sum_Ico_mul_le_of_quasiConcave`, applied to `-g`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- **A periodic cost against a renewal row.** Let `l ≥ 2`, `L ≥ 1`, `a ≥ 0`, let `g : ℕ → ℝ` be
`L`-periodic with mean `μ` over a period and with `D` the maximum minus the minimum over
`0 ≤ k ≤ L` of `∑_{j < k} (g j - μ)`. Then `r ↦ 𝖱(r - 1, l) g(r + a)` over `r ≥ 1` (written with
`r - 1 ∈ ℕ` as the summation variable) is summable, and
`∑_{r ≥ 1} 𝖱(r - 1, l) g(r + a) ≥ μ / 4 - D / √(2(3l - 1))`. -/
@[collatz_pos_dens "lem_c3_cyc_row"]
theorem tsum_rawMass_mul_periodic_ge {l L : ℕ} (hl : 2 ≤ l) (hL : 1 ≤ L) (a : ℕ)
    {g : ℕ → ℝ} (hg : ∀ k, g (k + L) = g k) {μ D : ℝ}
    (hμ : μ = (1 / L) * ∑ k ∈ range L, g k)
    (hD : D = (range (L + 1)).sup' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)) -
      (range (L + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ))) :
    Summable (fun r : ℕ => rawMass r l * g (r + 1 + a)) ∧
      μ / 4 - D / √(2 * (3 * l - 1)) ≤ ∑' r : ℕ, rawMass r l * g (r + 1 + a) := by
  have hl0 : (l : ℤ) ≠ 0 := by omega
  have hD0 : 0 ≤ D := by
    rw [hD, sub_nonneg]
    exact (inf'_le (fun k => ∑ j ∈ range k, (g j - μ)) (mem_range.2 (Nat.succ_pos L))).trans
      (le_sup' (fun k => ∑ j ∈ range k, (g j - μ)) (mem_range.2 (Nat.succ_pos L)))
  have hzero : ∀ r, l + 1 ≤ r → rawMass r l = 0 := fun r hr => by
    simpa using rawMass_pred_eq_zero (l := l) (k := r + 1) (by omega)
  have hfin : ∀ r ∉ range (l + 1), rawMass r l * g (r + 1 + a) = 0 := fun r hr => by
    rw [hzero r (by simpa using hr), zero_mul]
  set b : ℕ → ℝ := fun k => rawMass (k - 1) l with hb
  have hbsum : ∑ k ∈ Ico 0 (0 + (l + 2)), b k = 1 / 4 := by
    rw [zero_add, ← range_eq_Ico, sum_range_succ', sum_range_succ']
    simp only [hb, Nat.add_sub_cancel, Nat.zero_sub, rawMass_zero, ite_eq_right hl0, add_zero]
    refine (hasSum_sum_of_ne_finset_zero fun k hk => ?_).unique
      (hasSum_rawMass_succ (show (2 : ℤ) ≤ l by omega))
    exact hzero (k + 1) (by simpa using hk)
  have hlayer := sum_Ico_mul_le_of_quasiConcave (A := D) (B := -μ) (w := fun k => -g (k + a))
    hD0 (l + 2) 0 b (√(2 * (3 * l - 1)))⁻¹ (by positivity)
    (fun u t _ _ => by
      rw [sum_neg_distrib, sum_Ico_add', show u + t + a = u + a + t by omega]
      have := sub_le_sum_Ico_of_periodic hL hg hμ hD (u + a) t
      linarith)
    (fun i j k _ hij hjk _ => min_rawMass_pred_le (by omega) hij hjk)
    (fun k _ _ => ⟨rawMass_nonneg _ _, rawMass_pred_le_inv_sqrt (by omega) k⟩)
  rw [hbsum] at hlayer
  have hshift : ∑ k ∈ Ico 0 (0 + (l + 2)), b k * -g (k + a) =
      -∑ r ∈ range (l + 1), rawMass r l * g (r + 1 + a) := by
    rw [zero_add, ← range_eq_Ico, sum_range_succ', ← sum_neg_distrib]
    simp only [hb, Nat.add_sub_cancel, Nat.zero_sub, rawMass_zero, ite_eq_right hl0, zero_mul,
      neg_zero, add_zero, mul_neg]
  rw [hshift] at hlayer
  refine ⟨summable_of_ne_finset_zero hfin, ?_⟩
  rw [tsum_eq_sum hfin, div_eq_mul_inv D]
  linarith

end CollatzPosDens
