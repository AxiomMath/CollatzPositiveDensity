/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The packet function `Φ_t`

For an integer `t ≥ 1` and a real number `θ`, the packet function is the normalised
exponential sum
`Φ_t(θ) = (1 / t) |∑_{a=0}^{t-1} exp(2πi (2^a - 1) θ)|`.
Each summand has modulus `1`, so `0 ≤ Φ_t(θ) ≤ 1`, with `Φ_t(0) = 1`.

## Main definitions

* `CollatzPosDens.chPacketFn`: the packet function `Φ_t(θ)`.

## Main results

* `CollatzPosDens.chPacketFn_nonneg`: `0 ≤ Φ_t(θ)`.
* `CollatzPosDens.chPacketFn_le_one`: `Φ_t(θ) ≤ 1`.
* `CollatzPosDens.chPacketFn_zero`: `Φ_t(0) = 1` for `t ≥ 1`.
* `CollatzPosDens.chPacketFn_add_intCast`: `Φ_t` has period `1`.

## Implementation notes

The definition is stated for every natural number `t`; at `t = 0` it takes the value `0`
(the empty sum, with `1 / 0 = 0`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Complex Real

/-- The packet function `Φ_t(θ) = (1 / t) |∑_{a=0}^{t-1} exp(2πi (2^a - 1) θ)|`. -/
@[collatz_pos_dens "def_ch_packet_fn"]
noncomputable def chPacketFn (t : ℕ) (θ : ℝ) : ℝ :=
  (1 / (t : ℝ)) *
    ‖∑ a ∈ Finset.range t, Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * θ : ℝ))‖

/-- `chPacketFn t θ` equals `(1 / t) * ‖∑_{a < t} exp(2πi (2^a - 1) θ)‖`. -/
theorem chPacketFn_def (t : ℕ) (θ : ℝ) :
    chPacketFn t θ = (1 / (t : ℝ)) *
      ‖∑ a ∈ Finset.range t, Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * θ : ℝ))‖ :=
  rfl

/-- Each summand of the packet sum has modulus `1`. -/
theorem norm_exp_chPacket_summand (a : ℕ) (θ : ℝ) :
    ‖Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * θ : ℝ))‖ = 1 := by
  have : 2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * θ : ℝ) =
      ((2 * π * (((2 : ℝ) ^ a - 1) * θ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- The packet function is nonnegative. -/
theorem chPacketFn_nonneg (t : ℕ) (θ : ℝ) : 0 ≤ chPacketFn t θ :=
  mul_nonneg (by positivity) (norm_nonneg _)

/-- The packet function is at most `1`. -/
theorem chPacketFn_le_one (t : ℕ) (θ : ℝ) : chPacketFn t θ ≤ 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [chPacketFn]
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hle : ‖∑ a ∈ Finset.range t,
      Complex.exp (2 * π * Complex.I * (((2 : ℝ) ^ a - 1) * θ : ℝ))‖ ≤ t := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_congr rfl fun a _ => norm_exp_chPacket_summand a θ]
    simp
  rw [chPacketFn, one_div, inv_mul_le_iff₀ htR, mul_one]
  exact hle

/-- At `θ = 0` the packet function equals `1`. -/
theorem chPacketFn_zero {t : ℕ} (ht : 1 ≤ t) : chPacketFn t 0 = 1 := by
  have htR : (t : ℝ) ≠ 0 := by positivity
  simp [chPacketFn, htR]

/-- The packet function `Φ_t` has period `1`. -/
theorem chPacketFn_add_intCast (t : ℕ) (θ : ℝ) (k : ℤ) :
    chPacketFn t (θ + k) = chPacketFn t θ := by
  simp only [chPacketFn_def]
  congr 2
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : 2 * π * Complex.I * ((((2 : ℝ) ^ a - 1) * (θ + k) : ℝ) : ℂ) =
      2 * π * Complex.I * ((((2 : ℝ) ^ a - 1) * θ : ℝ) : ℂ) +
        (((2 ^ a - 1 : ℤ) * k : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

end CollatzPosDens
