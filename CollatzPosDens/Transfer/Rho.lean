/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Omega
public import CollatzPosDens.Transfer.D

/-!
# The two-passage rate `ϱ_*`

The two-passage rate is the rational constant `ϱ_* = (1 - d_*)^2 - Ω_*`, where `d_*` is the
single-passage loss and `Ω_*` the two-passage correction. Numerically `ϱ_* ≈ 0.8397328…`.
It enters the pair score `b_* = ∑_{j=1}^{12} (1 - ϱ_*)^j / j`.

## Main definitions

* `CollatzPosDens.rhoStar`: the two-passage rate `ϱ_* ∈ ℚ`.

## Main results

* `CollatzPosDens.rhoStar_eq`: the exact value of `ϱ_*`.
* `CollatzPosDens.rhoStar_pos`, `CollatzPosDens.rhoStar_lt_one`: `0 < ϱ_* < 1`.

## Implementation notes

The constant is defined in `ℚ`, so that inequalities involving it can be decided by `norm_num`
from the closed-form value `rhoStar_eq`; it is cast to `ℝ` where it is used analytically.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The two-passage rate `ϱ_* := (1 - d_*)^2 - Ω_*` in `ℚ`. -/
@[collatz_pos_dens "def_s02_rho"]
def rhoStar : ℚ := (1 - dStar) ^ 2 - omegaStar

/-- The defining formula of the two-passage rate. -/
theorem rhoStar_def : rhoStar = (1 - dStar) ^ 2 - omegaStar := rfl

/-- The exact value of the two-passage rate. -/
@[simp]
theorem rhoStar_eq :
    rhoStar =
      146226396865330841441006996169475586133169771748943233545640893008664541329 /
        174134416000000000000000000000000000000000000000000000000000000000000000000 := by
  rw [rhoStar_def, dStar_eq, omegaStar_eq]; norm_num

/-- The two-passage rate is positive. -/
theorem rhoStar_pos : 0 < rhoStar := by
  rw [rhoStar_eq]; norm_num

/-- The two-passage rate is less than one. -/
theorem rhoStar_lt_one : rhoStar < 1 := by
  rw [rhoStar_eq]; norm_num

end CollatzPosDens
