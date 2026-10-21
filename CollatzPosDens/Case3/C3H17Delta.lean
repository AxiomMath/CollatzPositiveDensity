/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Case3.C3H17Range

/-!
# Aggregate range of a phase class

For `s ∈ {1, 3, 5, 7}` the aggregate range is the rational number
`Dʰ_s = ∑_{c=2}^{16} ϖ(c) ∑_{o=1}^{c} rg_{c,o,s}`,
the orbit ranges `rg_{c,o,s}` of the height-seventeen cost table weighted by the Pascal law `ϖ`.

## Main definitions

* `CollatzPosDens.c3H17Delta`: the aggregate range `Dʰ_s`.

## Main results

* `CollatzPosDens.c3H17Delta_cast`: `Dʰ_s`, read in `ℝ`, is the sum written with the weights
  `ϖ(c)`.
* `CollatzPosDens.c3H17Delta_nonneg`: `0 ≤ Dʰ_s`.

## Implementation notes

The Pascal weight `ϖ(c) = (c - 1) 2^{-c}` (for `c ≥ 2`) is real-valued in `CollatzPosDens.varpi`,
so the definition uses its rational form `(c - 1) 2^{-c}` on the summation range, where `c ≥ 2`;
`c3H17Delta_cast` restates the sum with `varpi`. The index `s` ranges over all of `ℤ`, and the same
formula is used outside `{1, 3, 5, 7}`, where the aggregate range is not otherwise defined.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The aggregate range `Dʰ_s = ∑_{c=2}^{16} ϖ(c) ∑_{o=1}^{c} rg_{c,o,s}` of the phase class `s`;
the Pascal weight is written as `ϖ(c) = (c - 1) 2^{-c}`. -/
@[collatz_pos_dens "def_c3_h17_Delta"]
def c3H17Delta (s : ℤ) : ℚ :=
  ∑ c ∈ Icc (2 : ℤ) 16, ((c : ℚ) - 1) * (2 : ℚ) ^ (-c) * ∑ o ∈ Icc (1 : ℤ) c, c3H17Range c o s

/-- The rational Pascal weight agrees with `ϖ` for `c ≥ 2`. -/
private theorem cast_pascal {c : ℤ} (hc : 2 ≤ c) :
    ((((c : ℚ) - 1) * (2 : ℚ) ^ (-c) : ℚ) : ℝ) = varpi c := by
  rw [varpi_of_two_le hc]
  push_cast
  rfl

/-- The aggregate range read in `ℝ`: `Dʰ_s = ∑_{c=2}^{16} ϖ(c) ∑_{o=1}^{c} rg_{c,o,s}`. -/
theorem c3H17Delta_cast (s : ℤ) :
    (c3H17Delta s : ℝ) =
      ∑ c ∈ Icc (2 : ℤ) 16, varpi c * ∑ o ∈ Icc (1 : ℤ) c, (c3H17Range c o s : ℝ) := by
  rw [c3H17Delta]
  push_cast
  refine sum_congr rfl fun c hc => ?_
  rw [mem_Icc] at hc
  rw [← cast_pascal hc.1]
  push_cast
  rfl

/-- The aggregate range is nonnegative. -/
theorem c3H17Delta_nonneg (s : ℤ) : 0 ≤ c3H17Delta s := by
  refine sum_nonneg fun c hc => mul_nonneg ?_ (sum_nonneg fun o _ => c3H17Range_nonneg c o s)
  rw [mem_Icc] at hc
  have : (2 : ℚ) ≤ c := by exact_mod_cast hc.1
  have : (0 : ℚ) ≤ (c : ℚ) - 1 := by linarith
  positivity

end CollatzPosDens
