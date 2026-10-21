/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.Nstar
public import CollatzPosDens.Recipe.PhQstarValue
public import CollatzPosDens.FirstCrossing.PhRatio

/-!
# Room below the conductor

With the growth ratio `𝗀 = 101/100` and the generation threshold `N_* = 9853`, we have
`1668728 · 𝗀 ^ N_* < q_*`.

Indeed `1668728 · 𝗀 ^ N_* = 1668728 · 101 ^ 9853 / 100 ^ 9853`, and `q_* = d` for the explicit
49-digit integer `d` of `CollatzPosDens.conductor_value`. The exact integer comparison
`1668728 · 101 ^ 9853 < d · 100 ^ 9853` proves the claim.

## Main results

* `CollatzPosDens.logb_two_seedBound_gt`: `1668728 · 𝗀 ^ N_* < q_*`.

## Implementation notes

The integer comparison is checked once by kernel evaluation in `ℕ` (GMP-accelerated); it is
strict because `5` does not divide `1668728 · 101 ^ 9853`, so the product is not an integer
multiple of `100 ^ 9853` and the ceiling `q_*` is never attained.
-/

@[expose] public section

namespace CollatzPosDens

/-- The bound `1668728 · 𝗀 ^ N_* < q_*`, where `𝗀` is the growth ratio, `N_*` the generation
threshold and `q_*` the conductor. -/
@[collatz_pos_dens "lem_ph_h0_large"]
theorem logb_two_seedBound_gt :
    (1668728 : ℝ) * (growthRatio : ℝ) ^ generationThreshold < conductor := by
  rw [conductor_value, growthRatio_cast, generationThreshold_def, div_pow, ← mul_div_assoc,
    div_lt_iff₀ (by positivity)]
  exact_mod_cast (by decide +kernel : 1668728 * 101 ^ 9853 <
      (632239220553191787820523 * 10 ^ 25 +
        3964253799528824016493120) * 100 ^ 9853)

end CollatzPosDens
