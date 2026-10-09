/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnP3
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.StoppingTrace.TrE8
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa

/-!
# The passage surplus `δ_tr(s)`

For `s ∈ ℕ`, the *passage surplus* is
`δ_tr(s) = E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s) - d_*`,
where `E₈` is the eighth-order exponential defect, `p₄₅` and `p₃` are the closing and raw-three
exit masses, `γ_*` the trace tilt, `κ_*` the second-letter tilt ratio and `d_*` the
single-passage loss. It measures by how much one passage from a black point at gap `s` beats the
nominal loss `d_*`: the tilted mass of the passage is at most `1 - d_* - δ_tr(s)`.

## Main definitions

* `CollatzPosDens.trDelta`: the passage surplus `δ_tr : ℕ → ℝ`.

## Main results

* `CollatzPosDens.one_sub_dStar_sub_trDelta`: the rearrangement
  `1 - d_* - δ_tr(s) = 1 - E₈(γ_*) p₄₅(s) - E₈(κ_* γ_*) p₃(s)`.
* `CollatzPosDens.one_sub_dStar_pos`: positivity of `1 - d_*`.

## Implementation notes

The rational constants `γ_*`, `κ_*` and `d_*` are cast to `ℝ`, where `E₈`, `p₄₅` and `p₃` live.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The passage surplus `δ_tr(s) = E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s) - d_*`. -/
@[collatz_pos_dens "def_tr_delta"]
noncomputable def trDelta (s : ℕ) : ℝ :=
  E8 (gammaStar : ℝ) * p45 s + E8 ((kappaStar * gammaStar : ℚ) : ℝ) * p3 s - (dStar : ℝ)

/-- The rearrangement `1 - d_* - δ_tr(s) = 1 - E₈(γ_*) p₄₅(s) - E₈(κ_* γ_*) p₃(s)`. -/
theorem one_sub_dStar_sub_trDelta (s : ℕ) :
    1 - (dStar : ℝ) - trDelta s =
      1 - E8 (gammaStar : ℝ) * p45 s - E8 ((kappaStar * gammaStar : ℚ) : ℝ) * p3 s := by
  rw [trDelta]; ring

/-- The complement `1 - d_*` of the single-passage loss is positive. -/
theorem one_sub_dStar_pos : (0 : ℝ) < 1 - (dStar : ℝ) := by
  have : (dStar : ℝ) < 1 := by exact_mod_cast dStar_lt_one
  linarith

end CollatzPosDens
