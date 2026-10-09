/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrMuValue

/-!
# The guard inequality `5 (1 - d_*) > 16 μ_∘`

The single-passage loss `d_* = CollatzPosDens.dStar` and the adjacent surplus
`μ_∘ = CollatzPosDens.trMu` satisfy `5 (1 - d_*) > 16 μ_∘`. Both constants have exact rational
values, and
`5 (1 - d_*) - 16 μ_∘ = 1167029826633114832349512820403490031 / (256 · 10^33)`.

## Main results

* `CollatzPosDens.sixteen_mul_trMu_lt_five_mul_one_sub_dStar`: `16 μ_∘ < 5 (1 - d_*)`.
* `CollatzPosDens.five_mul_one_sub_dStar_sub_sixteen_mul_trMu_eq`: the exact value of the
  difference `5 (1 - d_*) - 16 μ_∘`.

## Implementation notes

The constant `d_*` lives in `ℚ` and `μ_∘` in `ℝ`, so the inequality is stated in `ℝ` with `d_*`
cast.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.4
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value of the guard margin `5 (1 - d_*) - 16 μ_∘`. -/
theorem five_mul_one_sub_dStar_sub_sixteen_mul_trMu_eq :
    5 * (1 - (dStar : ℝ)) - 16 * trMu =
      1167029826633114832349512820403490031 / 256000000000000000000000000000000000 := by
  rw [trMu_value, dStar_eq]
  push_cast
  norm_num

/-- The guard inequality `16 μ_∘ < 5 (1 - d_*)`, with `μ_∘ = trMu` and `d_* = dStar`. -/
@[collatz_pos_dens "lem_tr_guard_out"]
theorem sixteen_mul_trMu_lt_five_mul_one_sub_dStar : 16 * trMu < 5 * (1 - (dStar : ℝ)) := by
  linarith [five_mul_one_sub_dStar_sub_sixteen_mul_trMu_eq]

end CollatzPosDens
