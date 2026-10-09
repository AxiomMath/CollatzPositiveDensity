/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGreen
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# The renewal occupation

For `m : ℤ` the renewal occupation `renewalOccupation m` is the sum `∑' j : ℤ, green j m`
in `[0, ∞]` of the Green's function `green` over the line of second coordinate `m`: the expected
number of renewal epochs whose accumulated letter sum equals `m`.

## Main definitions

* `CollatzPosDens.renewalOccupation`: the renewal occupation.

## Main results

* `CollatzPosDens.renewalOccupation_def`: the defining sum.
* `CollatzPosDens.ofReal_green_le_renewalOccupation`: each term is bounded by the sum.

## Implementation notes

The Green's function `green` is real-valued and nonnegative (`green_nonneg`). The occupation
is valued in `ℝ≥0∞` by summing `ENNReal.ofReal (green j m)`; since `green j m ≥ 0` this
embedding is faithful, and the `tsum` in `ℝ≥0∞` is an unconditional sum, which always exists
(possibly `∞`).

## References

* [Mazur, *Collatz positive density*], §6.4.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The renewal occupation at `m`: the sum over `j : ℤ` of `green j m`, valued in `[0, ∞]`. -/
@[collatz_pos_dens "def_rn_occupation"]
noncomputable def renewalOccupation (m : ℤ) : ℝ≥0∞ :=
  ∑' j : ℤ, ENNReal.ofReal (green j m)

/-- Unfolding lemma for `renewalOccupation`. -/
theorem renewalOccupation_def (m : ℤ) :
    renewalOccupation m = ∑' j : ℤ, ENNReal.ofReal (green j m) :=
  rfl

/-- Each value `green j m` of the Green's function is at most `renewalOccupation m`. -/
theorem ofReal_green_le_renewalOccupation (j m : ℤ) :
    ENNReal.ofReal (green j m) ≤ renewalOccupation m :=
  ENNReal.le_tsum (f := fun j : ℤ ↦ ENNReal.ofReal (green j m)) j

end CollatzPosDens
