/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Dsc
public import CollatzPosDens.Transfer.S02Split
public import Mathlib.Basic.Real.Basic

/-!
# Far scales dominate the far-gap threshold

At every Fourier parameter index `ι`, for every real `m ≥ D_sc(ι)` the split level satisfies
`ς(ι, m) ≥ Ω_far(ι)`, where `Ω_far(ι)` is the far-gap threshold `omegaFar`, `D_sc(ι)` the scale
threshold `Dsc` and `ς(ι, m)` the split level `gapSplit`. At `o`,
`D_sc(o) = 2 + P_*(o) + ⌈2 Ω_far(o) / 3⌉ ≥ 2 Ω_far(o) / 3`, so `ς(o, m) = 3m/2 ≥ Ω_far(o)`. At
`b`, `D_sc(b) = 2 + P_*(b) + ⌈Ω_far(b) / 2⌉ ≥ Ω_far(b) / 2`, so `ς(b, m) = 2m ≥ Ω_far(b)`.

## Main results

* `CollatzPosDens.omegaFar_le_gapSplit_of_Dsc_le`: for every real `m ≥ D_sc(ι)`,
  `Ω_far(ι) ≤ ς(ι, m)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Far scales dominate the far-gap threshold.** For every index `ι` and every real
`m ≥ D_sc(ι)`, `ς(ι, m) ≥ Ω_far(ι)`. -/
@[collatz_pos_dens "lem_s02_far_S"]
theorem omegaFar_le_gapSplit_of_Dsc_le (ι : FIndex) {m : ℝ} (hm : (Dsc ι : ℝ) ≤ m) :
    (omegaFar ι : ℝ) ≤ gapSplit ι m := by
  cases ι
  · have h : (2 * omegaFar .o : ℝ) ≤ 3 * Dsc .o := by
      exact_mod_cast two_mul_omegaFar_le_three_mul_Dsc_o
    rw [gapSplit_o, le_div_iff₀ (by norm_num)]
    linarith
  · have h : (omegaFar .b : ℝ) ≤ 2 * Dsc .b := by exact_mod_cast omegaFar_le_two_mul_Dsc .b
    rw [gapSplit_b]
    linarith

end CollatzPosDens
