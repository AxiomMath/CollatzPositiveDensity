/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnPascalTotal

/-!
# Tails of the Pascal weights

For the Pascal weights `ϖ = CollatzPosDens.varpi` on `ℤ`, given by `ϖ(b) = (b - 1) 2^{-b}` for
`b ≥ 2` and `ϖ(b) = 0` for `b ≤ 1`, the tail beyond any `m ∈ ℕ` is explicit:
`∑_{b ∈ ℤ, b > m} ϖ(b) = (m + 1) 2^{-m}`.

## Main results

* `CollatzPosDens.hasSum_varpi_indicator_Ioi`: `∑_{b > m} ϖ(b) = (m + 1) 2^{-m}`, as an
  unconditionally convergent series over `ℤ` of the weights restricted to `b > m`.
* `CollatzPosDens.hasSum_varpi_Ioi`: the same series indexed by the subtype `{b : ℤ // m < b}`.
* `CollatzPosDens.tsum_varpi_Ioi`: the value of the tail as a `tsum`.

## Implementation notes

The restricted sum `∑_{b ∈ ℤ, b > m}` is formalized as the series of `Set.indicator (Set.Ioi m) ϖ`
over `ℤ`, in the strong (`HasSum`, unconditional) form; the subtype and `tsum` forms follow.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Tails of the Pascal weights: `∑_{b ∈ ℤ, b > m} ϖ(b) = (m + 1) 2^{-m}` for every `m ∈ ℕ`. -/
@[collatz_pos_dens "lem_rn_pascal_tail"]
theorem hasSum_varpi_indicator_Ioi (m : ℕ) :
    HasSum ((Set.Ioi (m : ℤ)).indicator varpi) (((m : ℝ) + 1) * (2 : ℝ) ^ (-(m : ℤ))) := by
  induction m with
  | zero =>
    convert hasSum_varpi using 1
    · ext b
      by_cases hb : (0 : ℤ) < b
      · simp [hb]
      · simp [hb, varpi_of_le_one (by omega : b ≤ 1)]
    · simp
  | succ m ih =>
    convert ih.sub (hasSum_pi_single ((m : ℤ) + 1) (varpi ((m : ℤ) + 1))) using 1
    · ext b
      by_cases hb : b = (m : ℤ) + 1
      · simp [hb]
      · simp only [Set.indicator, Set.mem_Ioi, Pi.single_apply, hb, ite_false, sub_zero]
        grind
    · rcases Nat.eq_zero_or_pos m with rfl | hm
      · norm_num [varpi_of_le_one]
      · rw [varpi_of_two_le (by omega), show -(((m + 1 : ℕ) : ℤ)) = -(m : ℤ) - 1 by push_cast; ring,
          show -((m : ℤ) + 1) = -(m : ℤ) - 1 by ring, zpow_sub₀ two_ne_zero]
        push_cast
        field_simp
        ring

/-- Tails of the Pascal weights, indexed by the subtype `{b : ℤ // m < b}`. -/
theorem hasSum_varpi_Ioi (m : ℕ) :
    HasSum (fun b : Set.Ioi (m : ℤ) ↦ varpi b) (((m : ℝ) + 1) * (2 : ℝ) ^ (-(m : ℤ))) :=
  hasSum_subtype_iff_indicator.mpr (hasSum_varpi_indicator_Ioi m)

/-- `∑_{b > m} ϖ(b) = (m + 1) 2^{-m}`, as a `tsum`. -/
theorem tsum_varpi_Ioi (m : ℕ) :
    ∑' b : Set.Ioi (m : ℤ), varpi b = ((m : ℝ) + 1) * (2 : ℝ) ^ (-(m : ℤ)) :=
  (hasSum_varpi_Ioi m).tsum_eq

end CollatzPosDens
