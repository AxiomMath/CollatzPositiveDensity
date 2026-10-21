/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Recipe.TargetFloor

/-!
# Endpoints of every generation are large

Let `t ≥ targetFloor` be an odd integer, let `j ∈ ℕ` and let `h ∈ centralHistories t j`. Then the
endpoint `historyEndpoint t h` is an odd integer that is at least `16 ^ scale j`.

## Main results

* `CollatzPosDens.historyEndpoint_large`: the endpoint of a central history of length `j` is an
  odd integer at least `16 ^ scale j`.

## Implementation notes

The endpoint `historyEndpoint t h` is a rational number; that it is an odd integer is stated as
the existence of an odd `m : ℤ` with `historyEndpoint t h = m`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- Let `t ≥ targetFloor` be an odd integer and `h ∈ centralHistories t j`. Then the endpoint
`historyEndpoint t h` is an odd integer `m` with `16 ^ scale j ≤ m`. -/
@[collatz_pos_dens "lem_s06_endpoint_floor"]
theorem historyEndpoint_large {t : ℤ} (hodd : Odd t) (ht : (targetFloor : ℤ) ≤ t)
    {j : ℕ} {h : Fin j → Word} (hh : h ∈ centralHistories t j) :
    ∃ m : ℤ, historyEndpoint t h = m ∧ Odd m ∧ 16 ^ scale j ≤ m :=
  historyEndpointAt_large hodd ht hh le_rfl

end CollatzPosDens
