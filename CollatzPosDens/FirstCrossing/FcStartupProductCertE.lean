/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factors 33 to 35

Kernel-checked lower bounds for blocks of consecutive factors of the startup product of central
masses. Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, each result gives
an explicit natural number below `∏_{j₀ ≤ j < j₀ + n} N_j`: the exact value when `n = 1`, and
otherwise a `63`-bit mantissa times a power of two.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_33`: factors 33 to 35.

## Implementation notes

Each bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product. The kernel's memory use grows with the scales `b_j`, so the factors with the
largest small scales `b_j < 256` are checked in short blocks.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- Certificate block for the factors `33 ≤ j ≤ 35`. -/
theorem prodGo_block_33 : 7800452581008451538 * 2 ^ 129 ≤ prodGo 3 33 (scale 33) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
