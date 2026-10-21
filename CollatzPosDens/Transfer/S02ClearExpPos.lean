/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02H
public import CollatzPosDens.Transfer.S02S
public import CollatzPosDens.Transfer.S02Ycl
public import CollatzPosDens.Transfer.S02Vcl
public import CollatzPosDens.Transfer.S02ClearExp
public import CollatzPosDens.Transfer.S02HSchedule

/-!
# Positivity of the clearing exponents

For every Fourier index `ι ∈ {o, b}` and every `0 ≤ i ≤ r_*(ι)` the clearing exponent
`t^cl_i(ι) = (1 - y_cl(ι)) (v_cl(ι) h_*(ι, p_i(ι)) - 13/9 · S_i(ι))` is positive. Fixing `ι` and
suppressing it, write `α = α_sc`, `v = v_cl` and `y = y_cl`. At a schedule position
`h_*(p_i) = ⌈α S_i⌉ + H_* ≥ α S_i + H_*`, and `v > 0`, so
$$v\,h_*(p_i) - \frac{13}{9}\mathsf S_i
  \ge \Bigl(v\alpha - \frac{13}{9}\Bigr)\mathsf S_i + v\,H_* > 0,$$
because `v α - 13/9` equals `743/900000` at `o` and `1/18` at `b`, `S_i ≥ 0`, and
`H_* ∈ {10100, 500}` is positive. Finally `1 - y ∈ {1/8192, 1/256}` is positive.

## Main results

* `CollatzPosDens.clearingExponent_pos`: `0 < t^cl_i(ι)` for every `i ≤ r_*(ι)`.
-/

@[expose] public section

namespace CollatzPosDens

/-- At a schedule position the window length dominates the linear form:
`α_sc(ι) S_i(ι) + H_*(ι) ≤ h_*(ι, p_i(ι))` for `0 ≤ i ≤ r_*(ι)`. -/
theorem traceSlope_mul_sStar_add_Hstar_le_windowLength (ι : FIndex) {i : ℕ}
    (hi : i ≤ rStar ι) :
    traceSlope ι * (sStar ι i : ℚ) + (Hstar ι : ℚ) ≤ (windowLength ι (schedule ι i) : ℚ) := by
  have hW : traceSlopeNum ι * sStar ι i + traceSlopeDen ι * Hstar ι ≤
      traceSlopeDen ι * windowLength ι (schedule ι i) := by
    rw [windowLength_schedule_eq_div ι hi]
    cases ι <;> simp only [traceSlopeNum_o, traceSlopeDen_o, traceSlopeNum_b, traceSlopeDen_b]
      <;> omega
  have hd : (0 : ℚ) < traceSlopeDen ι := by exact_mod_cast traceSlopeDen_pos ι
  have hWq : (traceSlopeNum ι : ℚ) * sStar ι i + traceSlopeDen ι * Hstar ι ≤
      traceSlopeDen ι * (windowLength ι (schedule ι i) : ℚ) := by
    exact_mod_cast hW
  rw [traceSlope_eq_div, ← mul_le_mul_iff_of_pos_left hd, mul_add, ← mul_assoc,
    mul_div_cancel₀ _ hd.ne']
  exact hWq

/-- The clearing exponents are positive: `0 < t^cl_i(ι)` for every `ι` and every
`0 ≤ i ≤ r_*(ι)`. -/
@[collatz_pos_dens "lem_s02_clear_exp_pos"]
theorem clearingExponent_pos {ι : FIndex} {i : ℕ} (hi : i ≤ rStar ι) :
    0 < clearingExponent ι i := by
  have hW := traceSlope_mul_sStar_add_Hstar_le_windowLength ι hi
  have hv := clearingPower_pos ι
  have hm := clearingPower_mul_traceSlope_sub_pos ι
  have hS : (0 : ℚ) ≤ sStar ι i := Nat.cast_nonneg _
  have hH : (0 : ℚ) < Hstar ι := by exact_mod_cast Hstar_pos ι
  have hy : 0 < 1 - clearingPoint ι := sub_pos.mpr (clearingPoint_lt_one ι)
  have hvW := mul_le_mul_of_nonneg_left hW hv.le
  rw [clearingExponent_def]
  apply mul_pos hy
  nlinarith [mul_nonneg hm.le hS, mul_pos hv hH]

end CollatzPosDens
