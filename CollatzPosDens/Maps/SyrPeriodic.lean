/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Definitions
public import Mathlib.Logic.Function.Iterate

/-!
# Syracuse-periodic integers

A positive odd integer `M` is *Syracuse-periodic* if `S^j(M) = M` for some `j ≥ 1`, where `S` is
the Syracuse map, the accelerated Collatz map `collatzAccel`.

## Main definitions

* `CollatzPosDens.SyrPeriodic M`: `M` is Syracuse-periodic.

## Implementation notes

The predicate is stated for every natural number `M`; it is only applied to positive
odd integers, on which `collatzAccel` is the Syracuse map.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `M` is *Syracuse-periodic*: `S^j(M) = M` for some `j ≥ 1`, where `S = collatzAccel` is the
Syracuse map. -/
@[collatz_pos_dens "def_syr_periodic"]
def SyrPeriodic (M : ℕ) : Prop :=
  ∃ j, 1 ≤ j ∧ collatzAccel^[j] M = M

end CollatzPosDens
