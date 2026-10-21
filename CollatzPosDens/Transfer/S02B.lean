/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Schedule

/-!
# The active packing bound `V_*`

At each Fourier parameter index `ι ∈ {o, b}` the active packing bound is the natural number
`V_*(ι) := p_{r_*(ι) - 1}(ι) + 1`, one more than the last schedule position `p_{r_*(ι) - 1}(ι)` at
which a packing step is performed. Since the schedule `i ↦ p_i(ι)` is increasing, every active
packing time `p_i(ι)` with `i < r_*(ι)` is strictly below `V_*(ι)`.

## Main definitions

* `CollatzPosDens.Vstar`: the active packing bound `V_*(ι) = p_{r_*(ι) - 1}(ι) + 1`.

## Main results

* `CollatzPosDens.Vstar_def`: the defining formula `V_*(ι) = p_{r_*(ι) - 1}(ι) + 1`.
* `CollatzPosDens.Vstar_o_eq`, `CollatzPosDens.Vstar_b_eq`: `V_*(o) = p_9(o) + 1` and
  `V_*(b) = p_2(b) + 1`, since `r_*(o) = 10` and `r_*(b) = 3`.
* `CollatzPosDens.Vstar_pos`: `0 < V_*(ι)`.
* `CollatzPosDens.schedule_lt_Vstar`: `p_i(ι) < V_*(ι)` for every `i < r_*(ι)`.
* `CollatzPosDens.lt_Vstar_of_le_schedule`: `u < V_*(ι)` whenever `u ≤ p_i(ι)` with
  `i < r_*(ι)`.

## Implementation notes

`V_*(ι)` is a closed natural number whose definition unfolds through several steps of the
schedule recurrence from `p_0(ι) = p_init(ι)`; `Vstar_def` and the lemmas above express it in
terms of `schedule` without evaluating it.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The active packing bound `V_*(ι) := p_{r_*(ι) - 1}(ι) + 1 ∈ ℕ`; every active packing time is
strictly below `V_*(ι)`. -/
@[collatz_pos_dens "def_s02_B"]
def Vstar (ι : FIndex) : ℕ := schedule ι (rStar ι - 1) + 1

/-- The defining formula of `V_*(ι)`. -/
theorem Vstar_def (ι : FIndex) : Vstar ι = schedule ι (rStar ι - 1) + 1 := by
  unfold Vstar
  rfl

/-- `V_*(o) = p_9(o) + 1`, since `r_*(o) = 10`. -/
theorem Vstar_o_eq : Vstar .o = schedule .o 9 + 1 := by
  rw [Vstar_def, rStar_o_sub_one]

/-- `V_*(b) = p_2(b) + 1`, since `r_*(b) = 3`. -/
theorem Vstar_b_eq : Vstar .b = schedule .b 2 + 1 := by
  rw [Vstar_def, rStar_b_sub_one]

/-- `V_*(ι)` is positive. -/
theorem Vstar_pos (ι : FIndex) : 0 < Vstar ι := by
  rw [Vstar_def]
  exact Nat.add_pos_right _ Nat.one_pos

/-- Every active packing time `p_i(ι)`, `i < r_*(ι)`, is strictly below `V_*(ι)`. -/
theorem schedule_lt_Vstar (ι : FIndex) {i : ℕ} (hi : i < rStar ι) :
    schedule ι i < Vstar ι := by
  rw [Vstar_def]
  exact Nat.lt_add_one_of_le (schedule_monotone ι (Nat.le_sub_one_of_lt hi))

/-- Every time `u ≤ p_i(ι)` with `i < r_*(ι)` is strictly below `V_*(ι)`. -/
theorem lt_Vstar_of_le_schedule (ι : FIndex) {u i : ℕ} (hi : i < rStar ι)
    (hu : u ≤ schedule ι i) : u < Vstar ι :=
  lt_of_le_of_lt hu (schedule_lt_Vstar ι hi)

end CollatzPosDens
