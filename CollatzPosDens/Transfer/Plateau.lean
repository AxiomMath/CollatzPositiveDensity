/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.Tstar
public import CollatzPosDens.Transfer.RecipeMap
public import CollatzPosDens.Transfer.K
public import CollatzPosDens.Transfer.AK
public import CollatzPosDens.Transfer.Beta
public import CollatzPosDens.Transfer.Bitlength
public import CollatzPosDens.Transfer.HDef
public import CollatzPosDens.Transfer.Pinit
public import CollatzPosDens.Transfer.Schedule
public import CollatzPosDens.Transfer.Envelope

/-!
# The scale schedule is on its plateau along the recipe schedule

Write `p_i = 𝔤^i(p_init)` for the recipe schedule and `y_i = p_i + 1`. As long as the bit length
of `y_i` does not exceed the plateau height `H_*`, the scale schedule is linear:
`β_*(p_i) = K_* y_i`. We show that this holds for every `0 ≤ i ≤ r_*`.

The proof is an induction showing `1025 ≤ y_i ≤ 1025 a_*^i` for `i ≤ r_*`: in the linear regime
`y_{i+1} = y_i + ⌈4 K_* y_i / 35⌉ + 8294 ≤ a_* y_i`, using `8294 < 10 · 1025 ≤ 10 y_i` and
`a_* = ⌈4 K_* / 35⌉ + 11`. The envelope bound `1025 a_*^{580} < 2^{H_*}` then keeps every `y_i`
below `2^{H_*}`.

## Main results

* `CollatzPosDens.schedule_succ_le_envelope`: `p_i + 1 ≤ 1025 a_*^i` for `i ≤ r_*`.
* `CollatzPosDens.betaStar_schedule`: `β_*(p_i) = K_*(p_i + 1)` for every `0 ≤ i ≤ r_*`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- One step of the linear regime: if `y ≥ 1025` then
`y + ⌈4 K_* y / 35⌉ + 8294 ≤ a_* y`. -/
private theorem plateau_step (y : ℕ) (hy : 1025 ≤ y) :
    y + (4 * Kstar * y + 34) / 35 + 8294 ≤ aK * y := by
  rw [aK_def]
  generalize Kstar = K
  set c := (4 * K + 34) / 35 with hc
  have hc35 : 4 * K ≤ 35 * c := by omega
  have := (Nat.mul_le_mul_right y hc35).trans_eq (Nat.mul_assoc 35 c y)
  have : (c + 11) * y = c * y + 11 * y := by ring
  omega

/-- The envelope `1025 a_*^i` stays below `2^{H_*}` for `i ≤ r_*`. -/
private theorem plateau_envelope_lt {i : ℕ} (hi : i ≤ rStar) : 1025 * aK ^ i < 2 ^ Hstar := by
  refine lt_of_le_of_lt (Nat.mul_le_mul_left 1025 (Nat.pow_le_pow_right aK_pos hi)) ?_
  have h := envelope_lt_two_pow_Hstar
  generalize hn : 580 = n at h
  rw [rStar_def, hn]
  exact h

/-- Along the recipe schedule, `p_i + 1 ≤ 1025 a_*^i` for every `i ≤ r_*`. -/
theorem schedule_succ_le_envelope {i : ℕ} (hi : i ≤ rStar) :
    schedule i + 1 ≤ 1025 * aK ^ i := by
  induction i with
  | zero => rw [pow_zero, mul_one, schedule_zero_add_one]
  | succ i ih =>
    have ih := ih (by omega)
    have hβ : betaStar (schedule i) = Kstar * (schedule i + 1) :=
      betaStar_of_bitLength_le
        (bitLength_le_iff.2 (ih.trans_lt (plateau_envelope_lt (Nat.le_of_succ_le hi))))
    have hy : 1025 ≤ schedule i + 1 := by
      have := pInit_le_schedule i
      rw [pInit_def] at this
      omega
    have hrec : schedule (i + 1) + 1 =
        (schedule i + 1) + (4 * Kstar * (schedule i + 1) + 34) / 35 + 8294 := by
      rw [schedule_succ, recipeMap_eq, windowLength_eq_div, hβ, mul_assoc]
      omega
    rw [hrec, pow_succ]
    calc _ ≤ aK * (schedule i + 1) := plateau_step _ hy
      _ ≤ aK * (1025 * aK ^ i) := Nat.mul_le_mul_left aK ih
      _ = 1025 * (aK ^ i * aK) := by ring

/-- **Plateau lemma.** For every `0 ≤ i ≤ r_*`, `β_*(p_i) = K_*(p_i + 1)`. -/
@[collatz_pos_dens "lem_s02_plateau"]
theorem betaStar_schedule {i : ℕ} (hi : i ≤ rStar) :
    betaStar (schedule i) = Kstar * (schedule i + 1) :=
  betaStar_of_bitLength_le
    (bitLength_le_iff.2 ((schedule_succ_le_envelope hi).trans_lt (plateau_envelope_lt hi)))

end CollatzPosDens
