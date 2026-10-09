/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrMuValue
public import CollatzPosDens.StoppingTrace.TrTheta
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Omega

/-!
# The two-passage correction as a multiple of the white-bridge floor

The two-passage correction `Ω_*` is exactly the product
`(1 - γ_*) θ_∘ (3/16 + 6701/26392)`. Indeed, from the exact value of the adjacent surplus `μ_∘`
and `θ_∘ = (10000/3299) μ_∘` one gets
`θ_∘ = 6799086470348268519226291189141329 / 1351270400000000000000000000000000000`; with
`1 - γ_* = 113/200` and `3/16 + 6701/26392 = 23299/52784`, exact multiplication gives the defining
value of `Ω_*`.

## Main results

* `CollatzPosDens.trTheta_value`: the exact value of `θ_∘`.
* `CollatzPosDens.omegaStar_eq_trTheta`: `(1 - γ_*) θ_∘ (3/16 + 6701/26392) = Ω_*`.

## Implementation notes

The identity is stated in `ℝ`, where `θ_∘` lives; the rational constants `γ_*` and `Ω_*` are
cast to `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The exact value of the white-bridge floor:
`θ_∘ = 6799086470348268519226291189141329 / 1351270400000000000000000000000000000`. -/
theorem trTheta_value :
    trTheta = 6799086470348268519226291189141329 / 1351270400000000000000000000000000000 := by
  rw [trTheta_def, trMu_value]
  norm_num

/-- The two-passage correction is a multiple of the white-bridge floor:
`(1 - γ_*) θ_∘ (3/16 + 6701/26392) = Ω_*`. -/
@[collatz_pos_dens "lem_tr_Omega_value"]
theorem omegaStar_eq_trTheta :
    (1 - (gammaStar : ℝ)) * trTheta * (3 / 16 + 6701 / 26392) = (omegaStar : ℝ) := by
  rw [trTheta_value, gammaStar_cast, omegaStar_cast]
  norm_num

end CollatzPosDens
