/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factors 24 to 29, 140 to 215, 216 to 291, 292 to 367, 368 to 443

Kernel-checked lower bounds for blocks of consecutive factors of the startup product of central
masses. Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, each result gives
an explicit natural number below `∏_{j₀ ≤ j < j₀ + n} N_j`: the exact value when `n = 1`, and
otherwise a `63`-bit mantissa times a power of two.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_24`: factors 24 to 29.
* `CollatzPosDens.fcStartupProduct.prodGo_block_140`: factors 140 to 215.
* `CollatzPosDens.fcStartupProduct.prodGo_block_216`: factors 216 to 291.
* `CollatzPosDens.fcStartupProduct.prodGo_block_292`: factors 292 to 367.
* `CollatzPosDens.fcStartupProduct.prodGo_block_368`: factors 368 to 443.

## Implementation notes

Each bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product `prodGo`.
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- Certificate block for the factors `24 ≤ j ≤ 29`. -/
theorem prodGo_block_24 : 7233221049146591544 * 2 ^ 320 ≤ prodGo 6 24 (scale 24) := by
  decide +kernel

/-- Certificate block for the factors `140 ≤ j ≤ 215`. -/
theorem prodGo_block_140 : 9176289218539186111 * 2 ^ 4801 ≤ prodGo 76 140 (scale 140) := by
  decide +kernel

/-- Certificate block for the factors `216 ≤ j ≤ 291`. -/
theorem prodGo_block_216 : 9219494101073213923 * 2 ^ 4801 ≤ prodGo 76 216 (scale 216) := by
  decide +kernel

/-- Certificate block for the factors `292 ≤ j ≤ 367`. -/
theorem prodGo_block_292 : 9222924817042451680 * 2 ^ 4801 ≤ prodGo 76 292 (scale 292) := by
  decide +kernel

/-- Certificate block for the factors `368 ≤ j ≤ 443`. -/
theorem prodGo_block_368 : 9223319781968729416 * 2 ^ 4801 ≤ prodGo 76 368 (scale 368) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
