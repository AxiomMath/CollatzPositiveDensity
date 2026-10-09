/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnRawMassFormula
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The odd-binomial sum of raw-prefix masses

For every integer `t ≥ 2`, the raw-prefix masses `𝖱(k, t)` over all lengths `k ≥ 1` sum to `1/4`:
`∑_{k ≥ 1} 𝖱(k, t) = 1/4`.

By the closed form `𝖱(k, t) = binom(t - 1, 2k - 1) 2^{-t}`, the sum is `2^{-t}` times the sum of
the odd-index binomial coefficients of row `t - 1 ≥ 1`. By Pascal's rule
`binom(m + 1, 2k + 1) = binom(m, 2k) + binom(m, 2k + 1)`, this odd-index sum of row `m + 1` is the
full sum `2^m` of row `m`, so the total is `2^{-t} 2^{t-2} = 1/4`.

## Main results

* `CollatzPosDens.hasSum_rawMass_succ`: for `t ≥ 2`, `∑_{k ≥ 0} 𝖱(k + 1, t) = 1/4`, as a
  `HasSum` statement.
* `CollatzPosDens.tsum_rawMass_succ`: the same identity for the `tsum`.
* `CollatzPosDens.summable_rawMass_succ`: the series is summable.
* `CollatzPosDens.sum_range_choose_succ_odd`: Pascal's rule in blocks,
  `∑_{k < N} binom(m + 1, 2k + 1) = ∑_{i < 2N} binom(m, i)`.

## Implementation notes

The sum over `k ≥ 1` is indexed by `k : ℕ` through the shift `k ↦ k + 1`. Only finitely many terms
are nonzero (those with `2k - 1 ≤ t - 1`), so the series converges unconditionally; the statement
is given as `HasSum`, which records both summability and the value.

## References

* [Mazur, *Collatz positive density*], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The odd-index binomial coefficients of row `m + 1` sum, in blocks, to the coefficients of row
`m`: `∑_{k < N} binom(m + 1, 2k + 1) = ∑_{i < 2N} binom(m, i)` (Pascal's rule). -/
theorem sum_range_choose_succ_odd (m N : ℕ) :
    ∑ k ∈ range N, (m + 1).choose (2 * k + 1) = ∑ i ∈ range (2 * N), m.choose i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, show 2 * (N + 1) = 2 * N + 1 + 1 by ring, sum_range_succ,
      sum_range_succ, Nat.choose_succ_succ, add_assoc]

/-- For `t ≥ 2`, the raw-prefix masses of all lengths `k ≥ 1` sum to `1/4`:
`∑_{k ≥ 1} 𝖱(k, t) = 1/4`. -/
@[collatz_pos_dens "lem_rn_raw_odd_sum"]
theorem hasSum_rawMass_succ {t : ℤ} (ht : 2 ≤ t) :
    HasSum (fun k : ℕ ↦ rawMass (k + 1) t) (1 / 4) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, t = n + 2 := ⟨(t - 2).toNat, by omega⟩
  have hform : ∀ k : ℕ, rawMass (k + 1) ((n : ℤ) + 2) =
      ((n + 1).choose (2 * k + 1) : ℝ) * (2 : ℝ) ^ (-((n : ℤ) + 2)) := by
    intro k
    rw [rawMass_eq_choose (by omega), show ((n : ℤ) + 2 - 1).toNat = n + 1 by omega,
      show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  have hzero : ∀ k ∉ range (n + 1), rawMass (k + 1) ((n : ℤ) + 2) = 0 := by
    intro k hk
    rw [mem_range, not_lt] at hk
    rw [hform, Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
  have hval : ∑ k ∈ range (n + 1), rawMass (k + 1) ((n : ℤ) + 2) = 1 / 4 := by
    simp_rw [hform, ← sum_mul]
    rw [← Nat.cast_sum, sum_range_choose_succ_odd,
      ← sum_subset (range_mono (by omega : n + 1 ≤ 2 * (n + 1)))
        (fun i _ hi ↦ Nat.choose_eq_zero_of_lt (by simpa using hi)), Nat.sum_range_choose,
      zpow_neg, show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_add]
    push_cast
    field_simp
    norm_num
  rw [← hval]
  exact hasSum_sum_of_ne_finset_zero hzero

/-- For `t ≥ 2`, `∑' k, 𝖱(k + 1, t) = 1/4`. -/
theorem tsum_rawMass_succ {t : ℤ} (ht : 2 ≤ t) : ∑' k : ℕ, rawMass (k + 1) t = 1 / 4 :=
  (hasSum_rawMass_succ ht).tsum_eq

/-- For `t ≥ 2`, the series `∑_{k ≥ 1} 𝖱(k, t)` is summable. -/
theorem summable_rawMass_succ {t : ℤ} (ht : 2 ≤ t) : Summable fun k : ℕ ↦ rawMass (k + 1) t :=
  (hasSum_rawMass_succ ht).summable

end CollatzPosDens
