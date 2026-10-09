/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factors 30 to 32

Kernel-checked lower bounds for blocks of consecutive factors of the startup product of central
masses. Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, each result gives
an explicit natural number below `∏_{j₀ ≤ j < j₀ + n} N_j`: the exact value when `n = 1`, and
otherwise a `63`-bit mantissa times a power of two.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_30`: factors 30 to 32.

## Implementation notes

Each bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product `prodGo`.
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- Certificate block for the factors `30 ≤ j ≤ 32`. -/
theorem prodGo_block_30 : 7032113881689408805 * 2 ^ 129 ≤ prodGo 3 30 (scale 30) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
