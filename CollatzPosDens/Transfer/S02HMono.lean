/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Beta
public import CollatzPosDens.Transfer.S02HDef

/-!
# Monotonicity of the window length `h_*`

For every Fourier index `ι`, the window length `h_*(ι, u) = ⌈α_sc(ι) β_*(ι, u)⌉ + H_*(ι)` is
nondecreasing in `u`: the oversize threshold `β_*` is monotone, the slope `α_sc(ι)` of the trace
schedule is positive, the ceiling is nondecreasing, and adding the constant `H_*` preserves the
order.

## Main results

* `CollatzPosDens.windowLength_le_of_le`: `h_*(ι, u) ≤ h_*(ι, u')` whenever `u ≤ u'`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The window length is nondecreasing: for every index `ι`, `h_*(ι, u) ≤ h_*(ι, u')` whenever
`u ≤ u'`. -/
@[collatz_pos_dens "lem_s02_h_mono"]
theorem windowLength_le_of_le (ι : FIndex) {u u' : ℕ} (h : u ≤ u') :
    windowLength ι u ≤ windowLength ι u' := by
  rw [windowLength_def, windowLength_def]
  have hα : (0 : ℝ) ≤ traceSlope ι := by exact_mod_cast (traceSlope_pos ι).le
  gcongr
  exact_mod_cast betaStar_monotone ι h

end CollatzPosDens
