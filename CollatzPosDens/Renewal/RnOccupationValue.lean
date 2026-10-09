/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnGreenClosed
public import CollatzPosDens.Renewal.RnOccupation
public import CollatzPosDens.Renewal.RnGreenFormula
public import CollatzPosDens.Renewal.RnRawOddSum

/-!
# The value of the renewal occupation

The renewal occupation `𝗎(m) = ∑_{j ∈ ℤ} 𝒢(j, m)` has the explicit value
`𝗎(m) = [m = 0] + 3/16 [m = 4] + 1/8 [m = 5] + 3/64 [m ≥ 6] + 1/32 [m ≥ 7]`.

By the closed form of the Green's function, the terms with `j ≤ 0` contribute `[m = 0]`, and the
terms with `j ≥ 1` contribute `ϖ(4) a(m - 4) + ϖ(5) a(m - 5)`, where
`a(t) = ∑_{k ≥ 0} 𝖱(k, t)` is the total raw-prefix mass at letter sum `t`. Since all letters are
at least `2`, `a(t) = 0` for `t < 0` and for `t = 1`, `a(0) = 1` (the empty word), and
`a(t) = 1/4` for `t ≥ 2` by the odd-sum identity for raw masses. With `ϖ(4) = 3/16` and
`ϖ(5) = 1/8` this gives the formula.

## Main results

* `CollatzPosDens.renewalOccupation_eq`: the closed-form value of `𝗎(m)`.
* `CollatzPosDens.renewalOccupation_eq_tsum_rawMass`: `𝗎(m) = [m = 0] + ϖ(4) a(m - 4) +
  ϖ(5) a(m - 5)` with `a(t) = ∑_k 𝖱(k, t)`.
* `CollatzPosDens.renewalOccupation_tsum_rawMass`: the value of `a(t)`.

## Implementation notes

The formula is stated for all `m ∈ ℤ` rather than only `m ∈ ℕ`: for `m < 0` both sides vanish.
As `𝗎` is valued in `[0, ∞]`, the right-hand side (a nonnegative real) is embedded by
`ENNReal.ofReal`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The total raw-prefix mass `a(t) = ∑_{k ≥ 0} 𝖱(k, t)` equals `[t = 0] + 1/4 [t ≥ 2]`. -/
theorem renewalOccupation_tsum_rawMass (t : ℤ) :
    ∑' k : ℕ, ENNReal.ofReal (rawMass k t) =
      ENNReal.ofReal ((if t = 0 then 1 else 0) + if 2 ≤ t then 1 / 4 else 0) := by
  rw [tsum_eq_zero_add' ENNReal.summable, rawMass_zero]
  rcases lt_or_ge t 2 with ht | ht
  · simp [rawMass_succ_of_lt_two _ ht, show ¬ 2 ≤ t by omega]
  · rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ rawMass_nonneg _ _) (summable_rawMass_succ ht),
      tsum_rawMass_succ ht]
    simp [show t ≠ 0 by omega, ht]

/-- The renewal occupation in terms of the total raw-prefix mass:
`𝗎(m) = [m = 0] + ϖ(4) a(m - 4) + ϖ(5) a(m - 5)` with `a(t) = ∑_{k ≥ 0} 𝖱(k, t)`. -/
theorem renewalOccupation_eq_tsum_rawMass (m : ℤ) :
    renewalOccupation m = (if m = 0 then 1 else 0) +
      (ENNReal.ofReal (varpi 4) * ∑' k : ℕ, ENNReal.ofReal (rawMass k (m - 4)) +
        ENNReal.ofReal (varpi 5) * ∑' k : ℕ, ENNReal.ofReal (rawMass k (m - 5))) := by
  rw [renewalOccupation_def, tsum_of_nat_of_neg_add_one ENNReal.summable ENNReal.summable,
    tsum_eq_zero_add' ENNReal.summable]
  have hneg : ∀ n : ℕ, ENNReal.ofReal (green (-((n : ℤ) + 1)) m) = 0 := fun n ↦ by
    rw [green_eq_greenClosed, greenClosed_of_neg (by omega), ENNReal.ofReal_zero]
  rw [tsum_congr hneg, tsum_zero, add_zero]
  simp only [green_eq_greenClosed, Nat.cast_zero, greenClosed_zero,
    Nat.cast_add, Nat.cast_one, greenClosed_succ]
  congr 1
  · split_ifs <;> simp
  · rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun k ↦ ?_
    rw [ENNReal.ofReal_add (mul_nonneg (varpi_nonneg _) (rawMass_nonneg _ _))
        (mul_nonneg (varpi_nonneg _) (rawMass_nonneg _ _)),
      ENNReal.ofReal_mul (varpi_nonneg _), ENNReal.ofReal_mul (varpi_nonneg _)]

/-- **The value of the renewal occupation.** For every `m`,
`𝗎(m) = [m = 0] + 3/16 [m = 4] + 1/8 [m = 5] + 3/64 [m ≥ 6] + 1/32 [m ≥ 7]`. -/
@[collatz_pos_dens "lem_rn_occupation_value"]
theorem renewalOccupation_eq (m : ℤ) :
    renewalOccupation m = ENNReal.ofReal ((if m = 0 then 1 else 0) +
      3 / 16 * (if m = 4 then 1 else 0) + 1 / 8 * (if m = 5 then 1 else 0) +
      3 / 64 * (if 6 ≤ m then 1 else 0) + 1 / 32 * (if 7 ≤ m then 1 else 0)) := by
  rw [renewalOccupation_eq_tsum_rawMass, renewalOccupation_tsum_rawMass,
    renewalOccupation_tsum_rawMass, varpi_four, varpi_five, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  rcases (show m < 0 ∨ 7 ≤ m ∨ m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 by omega)
    with h | h | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [show m - 4 ≠ 0 by omega, show ¬ 2 ≤ m - 4 by omega, show m - 5 ≠ 0 by omega,
      show ¬ 2 ≤ m - 5 by omega, show m ≠ 0 by omega, show m ≠ 4 by omega, show m ≠ 5 by omega,
      show ¬ 6 ≤ m by omega, show ¬ 7 ≤ m by omega, ite_false]
    norm_num
  · simp only [show m - 4 ≠ 0 by omega, show 2 ≤ m - 4 by omega, show m - 5 ≠ 0 by omega,
      show 2 ≤ m - 5 by omega, show m ≠ 0 by omega, show m ≠ 4 by omega, show m ≠ 5 by omega,
      show 6 ≤ m by omega, show 7 ≤ m by omega, ite_true]
    norm_num
  all_goals norm_num

end CollatzPosDens
