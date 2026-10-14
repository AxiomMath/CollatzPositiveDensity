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
# The terminal threshold `N_t`

The terminal threshold of the recipe is the natural number
$$N_{\mathrm t} := \left\lceil \frac{B_{\mathrm{ph}} + 121}{\delta} \right\rceil,$$
where `B_ph = 23 + log₂ F` is the physical exponent and `δ = log₂ (101/100)` is the logarithmic
growth rate. Since both `B_ph` and `δ` are positive, the quantity inside the ceiling is positive.

## Main definitions

* `CollatzPosDens.terminalThreshold`: the threshold `N_t ∈ ℕ`.

## Main results

* `CollatzPosDens.terminalThreshold_def`: the defining formula of `N_t`.
* `CollatzPosDens.le_terminalThreshold`: `(B_ph + 121) / δ ≤ N_t`.
* `CollatzPosDens.terminalThreshold_lt`: `N_t < (B_ph + 121) / δ + 1`.
* `CollatzPosDens.terminalThreshold_pos`: `0 < N_t`.

## Implementation notes

The ceiling is the natural-number ceiling `⌈·⌉₊`. Its argument is positive, so it agrees with
the integer ceiling (`terminalThreshold_cast_eq_ceil`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §16.1.
-/

@[expose] public section

namespace CollatzPosDens

private theorem terminalThreshold_arg_pos :
    0 < (physicalExponent + 121) / logGrowthRate := by
  have := physicalExponent_pos
  have := logGrowthRate_pos
  positivity

/-- The terminal threshold `N_t := ⌈(B_ph + 121) / δ⌉ ∈ ℕ`. -/
@[collatz_pos_dens "def_Nt"]
noncomputable def terminalThreshold : ℕ :=
  ⌈(physicalExponent + 121) / logGrowthRate⌉₊

/-- The defining formula of the terminal threshold. -/
theorem terminalThreshold_def :
    terminalThreshold = ⌈(physicalExponent + 121) / logGrowthRate⌉₊ := rfl

/-- `(B_ph + 121) / δ ≤ N_t`. -/
theorem le_terminalThreshold :
    (physicalExponent + 121) / logGrowthRate ≤ terminalThreshold :=
  Nat.le_ceil _

/-- `N_t < (B_ph + 121) / δ + 1`. -/
theorem terminalThreshold_lt :
    (terminalThreshold : ℝ) < (physicalExponent + 121) / logGrowthRate + 1 :=
  Nat.ceil_lt_add_one terminalThreshold_arg_pos.le

/-- The terminal threshold is positive. -/
theorem terminalThreshold_pos : 0 < terminalThreshold :=
  Nat.ceil_pos.mpr terminalThreshold_arg_pos

/-- Since its argument is positive, `N_t` is also the integer ceiling. -/
theorem terminalThreshold_cast_eq_ceil :
    (terminalThreshold : ℤ) = ⌈(physicalExponent + 121) / logGrowthRate⌉ :=
  Int.natCast_ceil_eq_ceil terminalThreshold_arg_pos.le

end CollatzPosDens
