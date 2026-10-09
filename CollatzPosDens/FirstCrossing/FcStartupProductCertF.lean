/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.FirstCrossing.FcStartupProductDefs

/-!
# Startup product certificate: factors 36, 37

Kernel-checked lower bounds for blocks of consecutive factors of the startup product of central
masses. Writing `N_j` for the `64`-bit lower bound for `2^64 𝐩(𝒞(b_j, K_j))`, each result gives
an explicit natural number below `∏_{j₀ ≤ j < j₀ + n} N_j`: the exact value when `n = 1`, and
otherwise a `63`-bit mantissa times a power of two.

## Main results

* `CollatzPosDens.fcStartupProduct.prodGo_block_36`: factor 36.
* `CollatzPosDens.fcStartupProduct.prodGo_block_37`: factor 37.

## Implementation notes

Each bound is a closed inequality between natural numbers, checked by kernel evaluation of the
computable product. The kernel's memory use grows with the scales `b_j`, so the blocks are
spread over several files, the factors with the largest small scales `b_j < 256` alone.
-/

@[expose] public section

namespace CollatzPosDens.fcStartupProduct

/-- Certificate block for the factor `j = 36`. -/
theorem prodGo_block_36 : 17759866906952949420 ≤ prodGo 1 36 (scale 36) := by
  decide +kernel

/-- Certificate block for the factor `j = 37`. -/
theorem prodGo_block_37 : 17882708551686697400 ≤ prodGo 1 37 (scale 37) := by
  decide +kernel

end CollatzPosDens.fcStartupProduct
