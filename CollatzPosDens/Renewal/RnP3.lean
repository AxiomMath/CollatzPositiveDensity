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
# The raw-three exit mass `p₃(s)`

For `s ∈ ℕ`, the raw-three exit mass is
`p₃(s) = ϖ(3) ∑_{O=1}^{3} ∑_{r=1}^{⌊(5s+16)/16⌋} 𝖱(r - 1, s + O - 3)`,
where `ϖ` is the Pascal law and `𝖱` the raw-prefix mass. It is the mass of the first-passage
witnesses over level `s` whose first raw letter exceeding `s` is a `3`.

## Main definitions

* `CollatzPosDens.p3 s`: the raw-three exit mass `p₃(s)`.

## Main results

* `CollatzPosDens.p3_nonneg`: `p₃(s) ≥ 0`.

## Implementation notes

The floor `⌊(5s+16)/16⌋` of a nonnegative rational is natural-number division
`(5 * s + 16) / 16`. Since `r ≥ 1`, the first argument `r - 1` of `𝖱` is an honest natural
number. The second argument `s + O - 3` is formed in `ℤ`: it is negative for small `s`
(e.g. `s = 0`, `O = 1`), where truncated subtraction in `ℕ` would wrongly give `𝖱(0, 0) = 1`
instead of `𝖱(0, -2) = 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The raw-three exit mass
`p₃(s) = ϖ(3) ∑_{O=1}^{3} ∑_{r=1}^{⌊(5s+16)/16⌋} 𝖱(r - 1, s + O - 3)`. -/
@[collatz_pos_dens "def_rn_p3"]
noncomputable def p3 (s : ℕ) : ℝ :=
  varpi 3 * ∑ O ∈ Icc (1 : ℕ) 3, ∑ r ∈ Icc 1 ((5 * s + 16) / 16),
    rawMass (r - 1) ((s : ℤ) + O - 3)

/-- The raw-three exit mass is nonnegative. -/
theorem p3_nonneg (s : ℕ) : 0 ≤ p3 s :=
  mul_nonneg (varpi_nonneg _) <| sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ rawMass_nonneg _ _

end CollatzPosDens
