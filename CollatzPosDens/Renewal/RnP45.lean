/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnRawMass

/-!
# The closing exit mass `p₄₅(s)`

For `s ∈ ℕ`, the closing exit mass is
`p₄₅(s) = ∑_{c=4}^{5} ϖ(c) ∑_{O=1}^{4} ∑_{r=1}^{⌊(5s+16)/16⌋} 𝖱(r - 1, s + O - c)`,
where `ϖ` is the Pascal holding-time law `CollatzPosDens.varpi` and `𝖱` the raw-prefix mass
`CollatzPosDens.rawMass`.

## Main definitions

* `CollatzPosDens.p45`: the closing exit mass `p₄₅ : ℕ → ℝ`.

## Main results

* `CollatzPosDens.p45_nonneg`: `p₄₅(s) ≥ 0`.

## Implementation notes

The second argument `s + O - c` of `𝖱` is computed in `ℤ`, as `𝖱` takes an integer second
argument; it is at least `s - 4` and is negative only for `s ≤ 3`, where `𝖱` vanishes. The floor
`⌊(5s+16)/16⌋` of a nonnegative rational is natural-number division `(5 * s + 16) / 16`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The closing exit mass
`p₄₅(s) = ∑_{c=4}^{5} ϖ(c) ∑_{O=1}^{4} ∑_{r=1}^{⌊(5s+16)/16⌋} 𝖱(r - 1, s + O - c)`. -/
@[collatz_pos_dens "def_rn_p45"]
noncomputable def p45 (s : ℕ) : ℝ :=
  ∑ c ∈ Icc (4 : ℤ) 5, varpi c *
    ∑ O ∈ Icc (1 : ℤ) 4, ∑ r ∈ Icc 1 ((5 * s + 16) / 16), rawMass (r - 1) ((s : ℤ) + O - c)

/-- The closing exit mass is nonnegative. -/
theorem p45_nonneg (s : ℕ) : 0 ≤ p45 s :=
  sum_nonneg fun _ _ ↦ mul_nonneg (varpi_nonneg _) <|
    sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ rawMass_nonneg _ _

end CollatzPosDens
