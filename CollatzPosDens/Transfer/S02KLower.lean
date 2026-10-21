/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02K

/-!
# A lower bound for the size factors `K_{*,i}(ι)`

Every size factor `CollatzPosDens.Kstar` satisfies `K_{*,i}(ι) ≥ 268` for every Fourier parameter
index `ι ∈ {o, b}` and every `0 ≤ i ≤ r_*(ι)`: the eleven values at `ι = o` are
`4638, 1622, 1253, 971, 754, 587, 458, 359, 292, 2^30, 2^30`, each at least `292 ≥ 268`, and the
four values at `ι = b` are `718, 268, 1024, 2^30`, the smallest of which is `K_{*,1}(b) = 268`.

## Main results

* `CollatzPosDens.le_Kstar_of_le_rStar`: `268 ≤ K_{*,i}(ι)` for `i ≤ r_*(ι)`.

## Implementation notes

The bound holds for every index of the total function `CollatzPosDens.Kstar`, which is
`CollatzPosDens.le_Kstar`; the statement here keeps the range `i ≤ r_*(ι)` on which the size
factors are meaningful.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- For every index `ι` and every `0 ≤ i ≤ r_*(ι)`, the size factor satisfies
`K_{*,i}(ι) ≥ 268`. -/
@[collatz_pos_dens "lem_s02_K_lower"]
theorem le_Kstar_of_le_rStar (ι : FIndex) {i : ℕ} (_hi : i ≤ rStar ι) : 268 ≤ Kstar ι i :=
  le_Kstar ι i

end CollatzPosDens
