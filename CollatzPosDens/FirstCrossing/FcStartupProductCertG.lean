/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factor 38

Kernel-checked lower bounds for blocks of consecutive factors of the startup product of central
masses. Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, each result gives
an explicit natural number below `∏_{j₀ ≤ j < j₀ + n} N_j`: the exact value when `n = 1`, and
otherwise a `63`-bit mantissa times a power of two.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_38`: factor 38.

## Implementation notes

Each bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product `prodGo`. The kernel's memory use grows with the scale `b_j`, so a factor
with a large scale `b_j < 256` is checked as a block of its own.
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- Certificate block for the factor `j = 38`. -/
theorem prodGo_block_38 : 17981953362750614438 ≤ prodGo 1 38 (scale 38) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
