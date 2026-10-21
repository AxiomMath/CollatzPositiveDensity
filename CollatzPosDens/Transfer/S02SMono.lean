/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02S
public import CollatzPosDens.Transfer.S02Schedule
public import CollatzPosDens.Transfer.S02KLower
public import CollatzPosDens.Transfer.Rstar

/-!
# Monotonicity of the interval sizes `S_i`

For each Fourier index `ι`, the interval sizes `S_i(ι) = K_{*,i}(ι) (p_i(ι) + 1)`,
`0 ≤ i ≤ r_*(ι)`, form a nondecreasing sequence: `S_i(ι) ≤ S_{i+1}(ι)` for `0 ≤ i < r_*(ι)`.

Suppressing `ι` and writing `α = α_sc(ι)` for the slope of the trace schedule, the schedule
recurrence gives `p_{i+1} ≥ ⌈α K_{*,i} (p_i + 1)⌉ ≥ α S_i`, and every size factor satisfies
`K_{*,i+1} ≥ 268`, so `S_{i+1} = K_{*,i+1} (p_{i+1} + 1) ≥ 268 α S_i ≥ S_i`, since
`268 α_sc(o) = 268 · 113/1000 = 7571/250 ≥ 1` and `268 α_sc(b) = 268 · 3/25 = 804/25 ≥ 1`.

## Main results

* `CollatzPosDens.sStar_le_sStar_succ`: `S_i(ι) ≤ S_{i+1}(ι)` for every `i < r_*(ι)`.

## Implementation notes

The argument uses only the shape of the recurrence, the value of the slope and the lower bound
`K_{*,i} ≥ 268`, never the numerical values of the schedule; it is carried out in `ℕ`, with the
ceiling written as the exact division `(a S_i + d - 1) / d`, where `α_sc(ι) = a / d`
(`schedule_succ_eq_div`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The interval sizes are nondecreasing on the schedule: `S_i(ι) ≤ S_{i+1}(ι)` for every
index `ι` and `0 ≤ i < r_*(ι)`. -/
@[collatz_pos_dens "lem_s02_S_mono"]
theorem sStar_le_sStar_succ (ι : FIndex) {i : ℕ} (hi : i < rStar ι) :
    sStar ι i ≤ sStar ι (i + 1) := by
  -- `S_{i+1} ≥ 268 (p_{i+1} + 1)`, from `K_{*,i+1} ≥ 268`.
  have hK : 268 * (schedule ι (i + 1) + 1) ≤ sStar ι (i + 1) :=
    Nat.mul_le_mul_right _ (le_Kstar_of_le_rStar ι (i := i + 1) hi)
  -- `p_{i+1} ≥ ⌈α_sc S_i⌉`, from the schedule recurrence, with `α_sc = a / d`.
  have hp := schedule_succ_eq_div ι i
  have hS : traceSlopeNum ι * Kstar ι i * (schedule ι i + 1) = traceSlopeNum ι * sStar ι i := by
    rw [sStar_def, Nat.mul_assoc]
  rw [hS] at hp
  -- `268 α_sc(ι) ≥ 1` at both indices closes the linear arithmetic.
  cases ι <;> simp only [traceSlopeNum_o, traceSlopeDen_o, traceSlopeNum_b, traceSlopeDen_b] at hp
    <;> omega

end CollatzPosDens
