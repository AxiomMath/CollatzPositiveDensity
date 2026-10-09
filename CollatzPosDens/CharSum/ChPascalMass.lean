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
# Total mass of the Pascal product law

For every `k ≥ 0`, the series `∑_{b ∈ ℤ^k} ∏_{i=1}^k ϖ(b_i)` of nonnegative terms converges and
its sum is `1`. For `k = 1` this is the statement that the Pascal weights `ϖ(b) = (b - 1) 2^{-b}`,
`b ≥ 2`, form a probability distribution on `ℤ`; for general `k`, by Tonelli the sum of the
nonnegative product family is `(∑_b ϖ(b))^k = 1`.

## Main results

* `CollatzPosDens.hasSum_prod_varpi`: `∑_{b ∈ ℤ^k} ∏_i ϖ(b_i) = 1`.

## Implementation notes

`ℤ^k` is `Fin k → ℤ`, and the claim is stated as `HasSum` in `ℝ`, which for a nonnegative family
is exactly convergence together with the value of the sum. The case `k = 1` is the total mass
`hasSum_varpi` of the Pascal weights, and the general case is the product rule
`hasSum_pi_fin_prod_of_nonneg`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every `k ≥ 0`, the nonnegative series `∑_{b ∈ ℤ^k} ∏_{i=1}^k ϖ(b_i)` converges with sum
`1`. -/
@[collatz_pos_dens "lem_ch_pascal_mass"]
theorem hasSum_prod_varpi (k : ℕ) : HasSum (fun b : Fin k → ℤ ↦ ∏ i, varpi (b i)) 1 := by
  simpa using hasSum_pi_fin_prod_of_nonneg hasSum_varpi varpi_nonneg k

end CollatzPosDens
