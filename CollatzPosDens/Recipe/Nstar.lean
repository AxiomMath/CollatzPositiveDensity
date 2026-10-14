/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Recipe.PhBphys
public import CollatzPosDens.FirstCrossing.PhDelta

/-!
# The generation threshold `N_*`

The generation threshold of the recipe is the natural number
$$N_* := \left\lceil \frac{B_{\mathrm{ph}} + 535/8}{\delta} \right\rceil,$$
where `B_ph = 23 + log₂ F` is the physical exponent and `δ = log₂ (101/100)` is the logarithmic
growth rate. Since both `B_ph` and `δ` are positive, the quantity inside the ceiling is positive.

## Main definitions

* `CollatzPosDens.generationThreshold`: the threshold `N_* ∈ ℕ`.

## Main results

* `CollatzPosDens.generationThreshold_def`: the defining formula of `N_*`.
* `CollatzPosDens.le_generationThreshold`: `(B_ph + 535/8) / δ ≤ N_*`.
* `CollatzPosDens.generationThreshold_lt`: `N_* < (B_ph + 535/8) / δ + 1`.
* `CollatzPosDens.generationThreshold_pos`: `0 < N_*`.

## Implementation notes

The ceiling is the natural-number ceiling `⌈·⌉₊`. Its argument is positive, so it agrees with
the integer ceiling (`generationThreshold_cast_eq_ceil`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

private theorem generationThreshold_arg_pos :
    0 < (physicalExponent + 535 / 8) / logGrowthRate :=
  div_pos (by linarith [physicalExponent_pos]) logGrowthRate_pos

/-- The generation threshold `N_* := ⌈(B_ph + 535/8) / δ⌉ ∈ ℕ`. -/
@[collatz_pos_dens "def_Nstar"]
noncomputable def generationThreshold : ℕ :=
  ⌈(physicalExponent + 535 / 8) / logGrowthRate⌉₊

/-- The defining formula of the generation threshold. -/
theorem generationThreshold_def :
    generationThreshold = ⌈(physicalExponent + 535 / 8) / logGrowthRate⌉₊ := rfl

/-- `(B_ph + 535/8) / δ ≤ N_*`. -/
theorem le_generationThreshold :
    (physicalExponent + 535 / 8) / logGrowthRate ≤ generationThreshold :=
  Nat.le_ceil _

/-- `N_* < (B_ph + 535/8) / δ + 1`. -/
theorem generationThreshold_lt :
    (generationThreshold : ℝ) < (physicalExponent + 535 / 8) / logGrowthRate + 1 :=
  Nat.ceil_lt_add_one generationThreshold_arg_pos.le

/-- The generation threshold is positive. -/
theorem generationThreshold_pos : 0 < generationThreshold :=
  Nat.ceil_pos.mpr generationThreshold_arg_pos

/-- `N_*` is the integer ceiling `⌈8 (B_ph + 535/8) / (5δ)⌉`. -/
theorem generationThreshold_cast_eq_ceil :
    (generationThreshold : ℤ) = ⌈(physicalExponent + 535 / 8) / logGrowthRate⌉ :=
  Int.natCast_ceil_eq_ceil generationThreshold_arg_pos.le

end CollatzPosDens
