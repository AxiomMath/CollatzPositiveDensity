/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.K
public import CollatzPosDens.Transfer.Beta
public import CollatzPosDens.Transfer.Bitlength
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The unweighted block sum

The series of positive terms `∑_{k ≥ 0} 1 / β_*(2^k - 1)` converges and its sum is at most
`2 / K_*`. Indeed `β_*(2^k - 1) = K_* 2^k 2^{max(0, k + 1 - H_*)} ≥ K_* 2^k`, so the series is
dominated termwise by the geometric series `∑_{k ≥ 0} K_*⁻¹ 2^{-k} = 2 / K_*`.

## Main results

* `CollatzPosDens.betaStar_two_pow_sub_one_summable_inv`: summability of the series and the
  bound `∑' k, 1 / β_*(2^k - 1) ≤ 2 / K_*`.

## Implementation notes

The sum is taken in `ℝ`. Since a non-summable series has `tsum` equal to `0` there, the statement
records summability together with the bound; for a series of positive terms this is the same as
the bound on its sum in `[0, ∞]`. The lower bound `K_* 2^k ≤ β_*(2^k - 1)` used is
`Kstar_mul_le_betaStar`, which does not need the exact value of the bit length of `2^k`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `1 / β_*(2^k - 1) ≤ K_*⁻¹ (1/2)^k`. -/
theorem betaStar_two_pow_sub_one_summable_inv_le (k : ℕ) :
    (1 : ℝ) / betaStar (2 ^ k - 1) ≤ (Kstar : ℝ)⁻¹ * (1 / 2) ^ k := by
  have h := Kstar_mul_le_betaStar (2 ^ k - 1)
  rw [Nat.sub_add_cancel Nat.one_le_two_pow] at h
  rw [one_div_pow, one_div, one_div, ← mul_inv]
  exact inv_anti₀ (mul_pos (by exact_mod_cast Kstar_pos) (by positivity)) (by exact_mod_cast h)

/-- The series `∑_{k ≥ 0} 1 / β_*(2^k - 1)` converges and its sum is at most `2 / K_*`. -/
@[collatz_pos_dens "lem_s02_block_sum_one"]
theorem betaStar_two_pow_sub_one_summable_inv :
    Summable (fun k : ℕ => (1 : ℝ) / betaStar (2 ^ k - 1)) ∧
      ∑' k : ℕ, (1 : ℝ) / betaStar (2 ^ k - 1) ≤ 2 / Kstar := by
  have hg : Summable (fun k : ℕ => (Kstar : ℝ)⁻¹ * (1 / 2) ^ k) :=
    summable_geometric_two.mul_left _
  have hs := hg.of_nonneg_of_le (fun _ => by positivity) betaStar_two_pow_sub_one_summable_inv_le
  refine ⟨hs, (hs.tsum_le_tsum betaStar_two_pow_sub_one_summable_inv_le hg).trans_eq ?_⟩
  rw [tsum_mul_left, tsum_geometric_two, inv_mul_eq_div]

end CollatzPosDens
