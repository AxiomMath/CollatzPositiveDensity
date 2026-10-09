/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rho
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Rat.Cast.Order

/-!
# The two-passage rate lies in the open unit interval

The two-passage rate `ϱ_* = (1 - d_*)^2 - Ω_*` is an explicit rational number, built from the
single-passage loss `d_* ≈ 0.0829461616…` and the two-passage correction `Ω_* ≈ 0.0012548…`.
Exact evaluation gives `ϱ_* ≈ 0.8397328926…`, so `0 < ϱ_* < 1`.

## Main results

* `CollatzPosDens.rhoStar_pos_and_lt_one`: `0 < ϱ_* ∧ ϱ_* < 1`.
* `CollatzPosDens.rhoStar_pos_and_lt_one_cast`: the same bounds for the image of `ϱ_*` in
  any ordered field, e.g. `ℝ`.

## Implementation notes

The constant `ϱ_*` is defined in `ℚ`; the bounds follow from its closed-form value. Since the
cast `ℚ → K` into an ordered field is strictly monotone, the bounds transfer to `K`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The two-passage rate lies strictly between `0` and `1`: `0 < ϱ_* < 1`. -/
@[collatz_pos_dens "lem_s02_rho_unit"]
theorem rhoStar_pos_and_lt_one : 0 < rhoStar ∧ rhoStar < 1 :=
  ⟨rhoStar_pos, rhoStar_lt_one⟩

/-- The bounds `0 < ϱ_* < 1` hold for the image of `ϱ_*` in any ordered field. -/
theorem rhoStar_pos_and_lt_one_cast {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    0 < (rhoStar : K) ∧ (rhoStar : K) < 1 :=
  ⟨Rat.cast_pos.mpr rhoStar_pos, by exact_mod_cast rhoStar_lt_one⟩

end CollatzPosDens
