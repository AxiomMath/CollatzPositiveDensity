/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Pinit
public import CollatzPosDens.Transfer.S02Alpha
public import CollatzPosDens.Transfer.S02K
public import CollatzPosDens.Transfer.S02H
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.Tstar
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Monotone.Basic

/-!
# The schedule positions `p_i(ι)`

At the Fourier parameter index `ι ∈ {o, b}` the schedule positions of the transfer argument are
the natural numbers defined by `p_0(ι) := p_init(ι)` and, for `i ≥ 0`,
`p_{i+1}(ι) := p_i(ι) + ⌈α_sc(ι) K_{*,i}(ι) (p_i(ι) + 1)⌉ + H_*(ι) + T_*(ι) + 1`,
where `α_sc(ι)` is the slope of the trace schedule (`113/1000` at `o`, `3/25` at `b`),
`K_{*,i}(ι)` are the size factors, `H_*(ι)` is the window height and `T_*(ι)` is the low-count
threshold. Every increment is at least `H_*(ι) + T_*(ι) + 1 ≥ 1`, so the schedule is strictly
increasing.

## Main definitions

* `CollatzPosDens.schedule`: the schedule position `p_i(ι)`.
* `CollatzPosDens.traceSlopeNum`, `CollatzPosDens.traceSlopeDen`: the numerator and denominator
  of the slope, `α_sc(ι) = traceSlopeNum ι / traceSlopeDen ι` (`113/1000` and `3/25`).

## Main results

* `CollatzPosDens.schedule_zero`: `p_0(ι) = p_init(ι)`.
* `CollatzPosDens.schedule_succ`: the defining recurrence for `p_{i+1}(ι)`.
* `CollatzPosDens.schedule_succ_eq_div`: the recurrence with the ceiling written as an exact
  natural-number division by the denominator of `α_sc(ι)`.
* `CollatzPosDens.schedule_o_succ_eq_div`, `CollatzPosDens.schedule_b_succ_eq_div`: the same with
  the constants evaluated, `H_*(o) + T_*(o) + 1 = 10293` and `H_*(b) + T_*(b) + 1 = 669`.
* `CollatzPosDens.schedule_o_zero_add_one`, `CollatzPosDens.schedule_b_zero_add_one`:
  `p_0(o) + 1 = 194` and `p_0(b) + 1 = 170`.
* `CollatzPosDens.schedule_lt_schedule_succ`: `p_i(ι) < p_{i+1}(ι)`.
* `CollatzPosDens.schedule_strictMono`, `CollatzPosDens.schedule_monotone`: `i ↦ p_i(ι)` is
  strictly increasing, hence monotone.
* `CollatzPosDens.pInit_le_schedule`: `p_init(ι) ≤ p_i(ι)`.

## Implementation notes

The positions are only used for `0 ≤ i ≤ r_*(ι)` (`CollatzPosDens.rStar`). The recurrence is
stated for every `i : ℕ`, so `schedule ι` is a total function on `ℕ` whose values at
`i > r_*(ι)` are never used.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §3.6.
-/

@[expose] public section

namespace CollatzPosDens

/-- The schedule positions at the index `ι`: `p_0(ι) := p_init(ι)` and
`p_{i+1}(ι) := p_i(ι) + ⌈α_sc(ι) K_{*,i}(ι) (p_i(ι) + 1)⌉ + H_*(ι) + T_*(ι) + 1`. -/
@[collatz_pos_dens "def_s02_schedule"]
def schedule (ι : FIndex) : ℕ → ℕ
  | 0 => pInit ι
  | i + 1 =>
    schedule ι i + ⌈traceSlope ι * Kstar ι i * (schedule ι i + 1)⌉₊ + Hstar ι + tStar ι + 1

/-- The initial schedule position is `p_0(ι) = p_init(ι)`. -/
@[simp]
theorem schedule_zero (ι : FIndex) : schedule ι 0 = pInit ι := rfl

/-- The defining recurrence
`p_{i+1}(ι) = p_i(ι) + ⌈α_sc(ι) K_{*,i}(ι) (p_i(ι) + 1)⌉ + H_*(ι) + T_*(ι) + 1`. -/
theorem schedule_succ (ι : FIndex) (i : ℕ) :
    schedule ι (i + 1) =
      schedule ι i + ⌈traceSlope ι * Kstar ι i * (schedule ι i + 1)⌉₊ + Hstar ι + tStar ι + 1 :=
  rfl

/-- The numerator of the slope of the trace schedule: `113` at `o` and `3` at `b`. -/
def traceSlopeNum : FIndex → ℕ
  | .o => 113
  | .b => 3

/-- The denominator of the slope of the trace schedule: `1000` at `o` and `25` at `b`. -/
def traceSlopeDen : FIndex → ℕ
  | .o => 1000
  | .b => 25

/-- The numerator of the slope at `o` is `113`. -/
@[simp] theorem traceSlopeNum_o : traceSlopeNum .o = 113 := rfl
/-- The numerator of the slope at `b` is `3`. -/
@[simp] theorem traceSlopeNum_b : traceSlopeNum .b = 3 := rfl
/-- The denominator of the slope at `o` is `1000`. -/
@[simp] theorem traceSlopeDen_o : traceSlopeDen .o = 1000 := rfl
/-- The denominator of the slope at `b` is `25`. -/
@[simp] theorem traceSlopeDen_b : traceSlopeDen .b = 25 := rfl

/-- The denominator of the slope is positive. -/
theorem traceSlopeDen_pos (ι : FIndex) : 0 < traceSlopeDen ι := by
  cases ι <;> decide

/-- The slope of the trace schedule as a quotient of natural numbers:
`α_sc(ι) = traceSlopeNum ι / traceSlopeDen ι`. -/
theorem traceSlope_eq_div (ι : FIndex) :
    traceSlope ι = (traceSlopeNum ι : ℚ) / traceSlopeDen ι := by
  cases ι <;> norm_num [traceSlope_o, traceSlope_b]

/-- The ceiling of a quotient of natural numbers, as a natural-number division. -/
private lemma natCeil_div_eq_add_pred_div (a : ℕ) {d : ℕ} (hd : 0 < d) :
    ⌈(a : ℚ) / d⌉₊ = (a + d - 1) / d := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  apply le_antisymm
  · rw [Nat.ceil_le, div_le_iff₀ hdq]
    have : a ≤ (a + d - 1) / d * d := by
      have h1 := Nat.div_add_mod (a + d - 1) d
      have h2 := Nat.mod_lt (a + d - 1) hd
      rw [Nat.mul_comm] at h1
      omega
    exact_mod_cast this
  · rw [Nat.div_le_iff_le_mul_add_pred hd]
    have h := Nat.le_ceil ((a : ℚ) / d)
    rw [div_le_iff₀ hdq] at h
    have : a ≤ ⌈(a : ℚ) / d⌉₊ * d := by exact_mod_cast h
    rw [Nat.mul_comm] at this
    omega

/-- The recurrence with an exact integer ceiling: writing `α_sc(ι) = a / d`,
`p_{i+1}(ι) = p_i(ι) + (a K_{*,i}(ι) (p_i(ι) + 1) + d - 1) / d + H_*(ι) + T_*(ι) + 1`. -/
theorem schedule_succ_eq_div (ι : FIndex) (i : ℕ) :
    schedule ι (i + 1) =
      schedule ι i +
          (traceSlopeNum ι * Kstar ι i * (schedule ι i + 1) + traceSlopeDen ι - 1) /
            traceSlopeDen ι + Hstar ι + tStar ι + 1 := by
  have hc : ⌈traceSlope ι * Kstar ι i * (schedule ι i + 1)⌉₊ =
      (traceSlopeNum ι * Kstar ι i * (schedule ι i + 1) + traceSlopeDen ι - 1) /
        traceSlopeDen ι := by
    rw [← natCeil_div_eq_add_pred_div _ (traceSlopeDen_pos ι), traceSlope_eq_div]
    push_cast
    ring_nf
  rw [schedule_succ, hc]

/-- The recurrence at the original index with the constants evaluated:
`p_{i+1}(o) = p_i(o) + (113 K_{*,i}(o) (p_i(o) + 1) + 999) / 1000 + 10293`. -/
theorem schedule_o_succ_eq_div (i : ℕ) :
    schedule .o (i + 1) =
      schedule .o i + (113 * Kstar .o i * (schedule .o i + 1) + 999) / 1000 + 10293 := by
  rw [schedule_succ_eq_div, traceSlopeNum_o, traceSlopeDen_o, Hstar_o, tStar_o]
  generalize 113 * Kstar .o i * (schedule .o i + 1) = y
  omega

/-- The recurrence at the bootstrap index with the constants evaluated:
`p_{i+1}(b) = p_i(b) + (3 K_{*,i}(b) (p_i(b) + 1) + 24) / 25 + 669`. -/
theorem schedule_b_succ_eq_div (i : ℕ) :
    schedule .b (i + 1) =
      schedule .b i + (3 * Kstar .b i * (schedule .b i + 1) + 24) / 25 + 669 := by
  rw [schedule_succ_eq_div, traceSlopeNum_b, traceSlopeDen_b, Hstar_b, tStar_b]
  generalize 3 * Kstar .b i * (schedule .b i + 1) = y
  omega

/-- `p_0(o) + 1 = 194`, since `p_init(o) = 193`. -/
theorem schedule_o_zero_add_one : schedule .o 0 + 1 = 194 := rfl

/-- `p_0(b) + 1 = 170`, since `p_init(b) = 169`. -/
theorem schedule_b_zero_add_one : schedule .b 0 + 1 = 170 := rfl

/-- Consecutive schedule positions strictly increase: `p_i(ι) < p_{i+1}(ι)`. -/
theorem schedule_lt_schedule_succ (ι : FIndex) (i : ℕ) : schedule ι i < schedule ι (i + 1) := by
  rw [schedule_succ]
  omega

/-- The schedule `i ↦ p_i(ι)` is strictly increasing. -/
theorem schedule_strictMono (ι : FIndex) : StrictMono (schedule ι) :=
  strictMono_nat_of_lt_succ (schedule_lt_schedule_succ ι)

/-- The schedule `i ↦ p_i(ι)` is monotone. -/
theorem schedule_monotone (ι : FIndex) : Monotone (schedule ι) :=
  (schedule_strictMono ι).monotone

/-- Every schedule position is at least the initial time: `p_init(ι) ≤ p_i(ι)`. -/
theorem pInit_le_schedule (ι : FIndex) (i : ℕ) : pInit ι ≤ schedule ι i :=
  schedule_zero ι ▸ schedule_monotone ι (Nat.zero_le i)

end CollatzPosDens
