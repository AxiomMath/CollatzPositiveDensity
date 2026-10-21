/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Case3.C3H17Mean

/-!
# Aggregate deficit of a phase class

For `s ∈ {1, 3, 5, 7}` the aggregate deficit of the phase class of `s` is the rational
`Sʰ_s = ∑_{c=2}^{16} ϖ(c) ∑_{o=1}^{c} (1 - μʰ_{c,o,s})`,
where `ϖ` is the Pascal weight and `μʰ_{c,o,s}` the orbit mean of the height-seventeen cost
table. Every summand `1 - μʰ_{c,o,s}` is nonnegative, so `Sʰ_s ≥ 0`.

## Main definitions

* `CollatzPosDens.c3H17S`: the aggregate deficit `Sʰ_s`.

## Main results

* `CollatzPosDens.c3H17S_cast`: `Sʰ_s`, read in `ℝ`, is the sum with the Pascal weights `ϖ(c)`.
* `CollatzPosDens.c3H17S_nonneg`: `Sʰ_s ≥ 0`.

## Implementation notes

The deficit is computable and rational-valued. The Pascal weight `ϖ(c) = (c - 1) 2^{-c}` (for
`c ≥ 2`) is real-valued in `CollatzPosDens.varpi`, so the definition uses its rational form
`(c - 1) 2^{-c}` on the summation range, where `c ≥ 2`; `c3H17S_cast` restates the sum with
`varpi`. The index `s` ranges over all of `ℤ`; outside `{1, 3, 5, 7}` the same formula is used.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The aggregate deficit `Sʰ_s = ∑_{c=2}^{16} ϖ(c) ∑_{o=1}^{c} (1 - μʰ_{c,o,s})` of the phase
class of `s`; the Pascal weight is written as `ϖ(c) = (c - 1) 2^{-c}`. -/
@[collatz_pos_dens "def_c3_h17_S"]
def c3H17S (s : ℤ) : ℚ :=
  ∑ c ∈ Icc (2 : ℤ) 16, ((c : ℚ) - 1) * (2 : ℚ) ^ (-c) *
    ∑ o ∈ Icc (1 : ℤ) c, (1 - c3H17Mean c o s)

/-- The rational Pascal weight agrees with `ϖ` for `c ≥ 2`. -/
private theorem cast_pascal {c : ℤ} (hc : 2 ≤ c) :
    ((((c : ℚ) - 1) * (2 : ℚ) ^ (-c) : ℚ) : ℝ) = varpi c := by
  rw [varpi_of_two_le hc]
  push_cast
  rfl

/-- The aggregate deficit, read in `ℝ`, is the sum with the Pascal weights `ϖ(c)`. -/
theorem c3H17S_cast (s : ℤ) :
    ((c3H17S s : ℚ) : ℝ) =
      ∑ c ∈ Icc (2 : ℤ) 16, varpi c * ∑ o ∈ Icc (1 : ℤ) c, ((1 - c3H17Mean c o s : ℚ) : ℝ) := by
  rw [c3H17S, Rat.cast_sum]
  refine sum_congr rfl fun c hc => ?_
  rw [Rat.cast_mul, cast_pascal (mem_Icc.mp hc).1, Rat.cast_sum]

/-- The aggregate deficit is nonnegative, since every orbit mean is at most `1`. -/
theorem c3H17S_nonneg (s : ℤ) : 0 ≤ c3H17S s := by
  refine sum_nonneg fun c hc => mul_nonneg ?_ (sum_nonneg fun o _ => ?_)
  · have : (2 : ℚ) ≤ c := by exact_mod_cast (mem_Icc.mp hc).1
    have : (0 : ℚ) ≤ (c : ℚ) - 1 := by linarith
    positivity
  · exact sub_nonneg.mpr (c3H17Mean_le_one c o s)

end CollatzPosDens
