/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.H
public import CollatzPosDens.Transfer.K
public import CollatzPosDens.Transfer.Beta
public import CollatzPosDens.Transfer.Bitlength
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The window-weighted block sum

For every `p ∈ ℕ` the series of positive terms
`∑_{k ≥ 0} 136 (min(p, 2^{k+1} - 2) + 1) / β_*(2^k - 1)` converges and its sum is strictly less
than `272 (H_* + 1) / K_*`.

Since `bl(2^k) = k + 1`, the weight is `β_*(2^k - 1) = K_* 2^k 2^{m_k}` with
`m_k = max(0, k + 1 - H_*)`. As `136 (min(p, 2^{k+1} - 2) + 1) ≤ 136 (2^{k+1} - 1) < 272 · 2^k`,
the `k`-th term is strictly below `(272 / K_*) 2^{-m_k}`, and
`∑_{k ≥ 0} 2^{-m_k} = H_* + ∑_{i ≥ 1} 2^{-i} = H_* + 1`.

## Main results

* `CollatzPosDens.betaStar_two_pow_sub_one_summable_window`: summability of the series and
  the strict bound `∑' k, 136 (min(p, 2^{k+1} - 2) + 1) / β_*(2^k - 1) < 272 (H_* + 1) / K_*`.
* `CollatzPosDens.betaStar_two_pow_sub_one_eq`: `β_*(2^k - 1) = K_* 2^k 2^{k + 1 - H_*}`.

## Implementation notes

The sum is taken in `ℝ`. Since a non-summable series has `tsum` equal to `0` there, the statement
records summability together with the bound; for a series of positive terms this is the same as
the bound on its sum in `[0, ∞]`. The subtractions `2^{k+1} - 2` and `2^k - 1` are truncated
subtractions in `ℕ`, which agree with the integer ones since `2 ≤ 2^{k+1}` and `1 ≤ 2^k`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The scale schedule at `2^k - 1`: `β_*(2^k - 1) = K_* 2^k 2^{k + 1 - H_*}` (truncated
subtraction in the exponent). -/
theorem betaStar_two_pow_sub_one_eq (k : ℕ) :
    betaStar (2 ^ k - 1) = Kstar * 2 ^ k * 2 ^ (k + 1 - Hstar) := by
  rw [betaStar_def, Nat.sub_add_cancel Nat.one_le_two_pow, bitLength, Nat.size_pow]

/-- Termwise comparison: the `k`-th term is strictly below `(272 / K_*) (1/2)^{k + 1 - H_*}`. -/
private theorem term_lt (p k : ℕ) :
    ((136 * (min p (2 ^ (k + 1) - 2) + 1) : ℕ) : ℝ) / betaStar (2 ^ k - 1) <
      272 / Kstar * (1 / 2) ^ (k + 1 - Hstar) := by
  have hN : 136 * (min p (2 ^ (k + 1) - 2) + 1) < 272 * 2 ^ k := by
    have h1 : min p (2 ^ (k + 1) - 2) ≤ 2 ^ (k + 1) - 2 := min_le_right _ _
    have h2 : 2 ≤ 2 ^ (k + 1) := Nat.le_self_pow (by omega) 2
    rw [pow_succ] at h1 h2
    omega
  have hN' : ((136 * (min p (2 ^ (k + 1) - 2) + 1) : ℕ) : ℝ) < 272 * 2 ^ k :=
    mod_cast hN
  rw [betaStar_two_pow_sub_one_eq]
  have hK : (0 : ℝ) < Kstar := mod_cast Kstar_pos
  generalize ((136 * (min p (2 ^ (k + 1) - 2) + 1) : ℕ) : ℝ) = N at hN' ⊢
  push_cast
  rw [div_lt_iff₀ (by positivity), one_div_pow]
  calc N < 272 * 2 ^ k := hN'
    _ = 272 / Kstar * (1 / 2 ^ (k + 1 - Hstar)) * (Kstar * 2 ^ k * 2 ^ (k + 1 - Hstar)) := by
      field_simp

/-- `∑_{k ≥ 0} (1/2)^{k + 1 - H} = H + 1` (truncated subtraction in the exponent). -/
private theorem hasSum_half_pow_sub (H : ℕ) :
    HasSum (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 1 - H)) (H + 1) := by
  have hshift : (fun i : ℕ => ((1 : ℝ) / 2) ^ (i + H + 1 - H)) =
      fun i => (1 / 2) ^ i * (1 / 2) := by
    funext i
    rw [show i + H + 1 - H = i + 1 by omega, pow_succ]
  have hs : Summable (fun i : ℕ => ((1 : ℝ) / 2) ^ (i + H + 1 - H)) := by
    rw [hshift]
    exact summable_geometric_two.mul_right _
  have hs' : Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ (k + 1 - H)) :=
    (summable_nat_add_iff H).1 hs
  refine hs'.hasSum_iff.2 ?_
  rw [← hs'.sum_add_tsum_nat_add H]
  have hfin : ∑ i ∈ Finset.range H, ((1 : ℝ) / 2) ^ (i + 1 - H) = H := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    intro i hi
    rw [Finset.mem_range] at hi
    rw [Nat.sub_eq_zero_of_le (by omega), pow_zero]
  have htail : ∑' i : ℕ, ((1 : ℝ) / 2) ^ (i + H + 1 - H) = 1 := by
    rw [hshift, tsum_mul_right, tsum_geometric_two]
    norm_num
  rw [hfin, htail]

/-- **Window-weighted block sum.** For every `p ∈ ℕ`, the series of positive terms
`∑_{k ≥ 0} 136 (min(p, 2^{k+1} - 2) + 1) / β_*(2^k - 1)` converges and its sum is strictly less
than `272 (H_* + 1) / K_*`. -/
@[collatz_pos_dens "lem_s02_block_sum_X"]
theorem betaStar_two_pow_sub_one_summable_window (p : ℕ) :
    Summable (fun k : ℕ =>
        ((136 * (min p (2 ^ (k + 1) - 2) + 1) : ℕ) : ℝ) / betaStar (2 ^ k - 1)) ∧
      ∑' k : ℕ, ((136 * (min p (2 ^ (k + 1) - 2) + 1) : ℕ) : ℝ) / betaStar (2 ^ k - 1) <
        272 * (Hstar + 1) / Kstar := by
  have hg := (hasSum_half_pow_sub Hstar).mul_left (272 / (Kstar : ℝ))
  have hs := hg.summable.of_nonneg_of_le (fun k => by positivity) (fun k => (term_lt p k).le)
  refine ⟨hs, ?_⟩
  calc _ < ∑' k : ℕ, 272 / (Kstar : ℝ) * (1 / 2) ^ (k + 1 - Hstar) :=
        hs.tsum_lt_tsum (fun k => (term_lt p k).le) (term_lt p 0) hg.summable
    _ = 272 * (Hstar + 1) / Kstar := by rw [hg.tsum_eq]; ring

end CollatzPosDens
