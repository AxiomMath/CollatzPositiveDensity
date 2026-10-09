/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.Beta
public import CollatzPosDens.Transfer.Schedule

/-!
# The largest used scale `B_*`

This file defines the natural number `B_* := β_*(p_{r_*})`, the scale function `β_*` (`betaStar`)
evaluated at the last schedule position `p_{r_*}` (`schedule rStar`). Since `β_*` is monotone and
the schedule is increasing, `B_*` dominates every scale `β_*(q)` with `q ≤ p_{r_*}`, in particular
every `β_*(p_i)` with `i ≤ r_*`.

## Main definitions

* `CollatzPosDens.Bstar`: the largest used scale `B_* = β_*(p_{r_*})`.

## Main results

* `CollatzPosDens.Bstar_def`: the defining formula `B_* = β_*(p_{r_*})`.
* `CollatzPosDens.Bstar_pos`: `0 < B_*`.
* `CollatzPosDens.betaStar_le_Bstar`: `β_*(q) ≤ B_*` for `q ≤ p_{r_*}`.
* `CollatzPosDens.betaStar_schedule_le_Bstar`: `β_*(p_i) ≤ B_*` for `i ≤ r_*`.

## Implementation notes

`B_*` is a closed natural number of more than seventeen thousand bits. It is declared
irreducible so that no tactic attempts to evaluate it; its value is accessed through `Bstar_def`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The largest used scale `B_* := β_*(p_{r_*}) ∈ ℕ`. -/
@[collatz_pos_dens "def_s02_B", irreducible]
noncomputable def Bstar : ℕ := betaStar (schedule rStar)

/-- The defining formula of `B_*`. -/
theorem Bstar_def : Bstar = betaStar (schedule rStar) := by
  delta Bstar; rfl

/-- `B_*` is positive. -/
theorem Bstar_pos : 0 < Bstar := by
  rw [Bstar_def]; exact betaStar_pos _

/-- `1 ≤ B_*`. -/
theorem one_le_Bstar : 1 ≤ Bstar := Bstar_pos

/-- `K_* (p_{r_*} + 1) ≤ B_*`. -/
theorem Kstar_mul_le_Bstar : Kstar * (schedule rStar + 1) ≤ Bstar := by
  rw [Bstar_def]; exact Kstar_mul_le_betaStar _

/-- `B_*` dominates every scale `β_*(q)` with `q ≤ p_{r_*}`. -/
theorem betaStar_le_Bstar {q : ℕ} (hq : q ≤ schedule rStar) : betaStar q ≤ Bstar := by
  rw [Bstar_def]; exact betaStar_monotone hq

/-- `B_*` dominates the scale `β_*(p_i)` of every schedule position with `i ≤ r_*`. -/
theorem betaStar_schedule_le_Bstar {i : ℕ} (hi : i ≤ rStar) :
    betaStar (schedule i) ≤ Bstar :=
  betaStar_le_Bstar (schedule_monotone hi)

end CollatzPosDens
