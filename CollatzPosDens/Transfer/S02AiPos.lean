/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Ai

/-!
# Positivity of the adaptive denominators `A_i(ι)`

For both Fourier indices every adaptive denominator of the trace schedule is positive:
`A_i(o) = b_an S_i(o) - 1698 - (6579/500) p_i(o)` and
`A_i(b) = b_an S_i(b) - 1357 - (1653/125) p_i(b)`. On the schedule range
(`r_*(o) = 10`, `r_*(b) = 3`) the thirteen values are explicit rationals, the smallest being
`A_0(o) = 1293859.108…` and `A_0(b) = 172503.500…`
(then `A_1(b) = 5781784.986…`, `A_2(b) = 752863030.132…`).

The proof here does not evaluate them one by one. Since `S_i(ι) = K_{*,i}(ι) (p_i(ι) + 1)`,
`K_{*,i}(ι) ≥ 268` and `b_an > 1`, one has `b_an S_i(ι) ≥ 268 (p_i(ι) + 1)`, which exceeds
`1698 + (6579/500) p` as soon as `p ≥ 6`, and `1357 + (1653/125) p` as soon as `p ≥ 5`; every
schedule position satisfies `p_i(ι) ≥ p_init(ι) ≥ 169`.

## Main results

* `CollatzPosDens.aStar_pos`: `0 < A_i(ι)` for every `ι` and every `i`, in particular for
  `0 ≤ i < r_*(ι)`.

## Implementation notes

The statement is proved for every index `i : ℕ`, not only for `i < r_*(ι)`: the lower bounds
`K_{*,i}(ι) ≥ 268` and `p_i(ι) ≥ p_init(ι)` used in the proof hold for all `i`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Every adaptive denominator of the trace schedule is positive: `0 < A_i(ι)`. In particular
this holds for every `ι` and every `0 ≤ i < r_*(ι)`. -/
@[collatz_pos_dens "lem_s02_Ai_pos"]
theorem aStar_pos (ι : FIndex) (i : ℕ) : 0 < aStar ι i := by
  have hK : (268 : ℚ) ≤ Kstar ι i := by exact_mod_cast le_Kstar ι i
  have hp : (pInit ι : ℚ) ≤ schedule ι i := by exact_mod_cast pInit_le_schedule ι i
  have hS : (268 : ℚ) * ((schedule ι i : ℚ) + 1) ≤ sStar ι i := by
    rw [sStar_cast]
    exact mul_le_mul_of_nonneg_right hK (by positivity)
  have hb : (1 : ℚ) < bAn := by rw [bAn_eq]; norm_num
  have hS0 : (0 : ℚ) ≤ sStar ι i := by positivity
  cases ι
  · rw [pInit_o, Nat.cast_ofNat] at hp
    rw [aStar_apply_o]
    nlinarith
  · rw [pInit_b, Nat.cast_ofNat] at hp
    rw [aStar_apply_b]
    nlinarith

end CollatzPosDens
