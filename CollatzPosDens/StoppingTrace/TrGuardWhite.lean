/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrE8
public import CollatzPosDens.StoppingTrace.TrMu
public import CollatzPosDens.StoppingTrace.TrMuValue
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa

/-!
# The guard for a white branch

The single-passage survival `1 - d_*`, weighted by the eighth-order exponential defect
`E₈(γ_*)` at the trace tilt, dominates eight times the adjacent surplus:
`8 μ_∘ < (1 - d_*) E₈(γ_*)`. All quantities are explicit rationals, and the gap is
`(1 - d_*) E₈(γ_*) - 8 μ_∘ =
14230387209563524366669589804709992932620634881359169963 /
45875200000000000000000000000000000000000000000000000000`.

## Main results

* `CollatzPosDens.one_sub_dStar_mul_E8_sub_eight_mul_trMu`: the exact value of
  `(1 - d_*) E₈(γ_*) - 8 μ_∘`.
* `CollatzPosDens.eight_mul_trMu_lt_one_sub_dStar_mul_E8`: `8 μ_∘ < (1 - d_*) E₈(γ_*)`.

## Implementation notes

The rational constants `d_*` and `γ_*` are cast to `ℝ`, where `E₈` and `μ_∘` live. The proof
evaluates `E₈(γ_*)` through its rational form and `μ_∘` through its exact value.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact gap in the white-branch guard. -/
theorem one_sub_dStar_mul_E8_sub_eight_mul_trMu :
    (1 - (dStar : ℝ)) * E8 gammaStar - 8 * trMu =
      14230387209563524366669589804709992932620634881359169963 /
        45875200000000000000000000000000000000000000000000000000 := by
  rw [E8_ratCast, trMu_value, dStar_eq, gammaStar_eq]
  push_cast
  norm_num

/-- **Guard for a white branch.** `8 μ_∘ < (1 - d_*) E₈(γ_*)`. -/
@[collatz_pos_dens "lem_tr_guard_white"]
theorem eight_mul_trMu_lt_one_sub_dStar_mul_E8 :
    8 * trMu < (1 - (dStar : ℝ)) * E8 gammaStar := by
  linarith [one_sub_dStar_mul_E8_sub_eight_mul_trMu]

end CollatzPosDens
