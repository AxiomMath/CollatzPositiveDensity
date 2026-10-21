/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCrossing
public import CollatzPosDens.StoppingTrace.TrRowFloor
public import CollatzPosDens.StoppingTrace.TrPacketRange
public import CollatzPosDens.StoppingTrace.TrRaw3CapRay
public import CollatzPosDens.StoppingTrace.TrDSmall

/-!
# A floor for the direct first-crossing decrement at large gaps

For every `s ≥ 512`, the direct first-crossing decrement satisfies
`D_cr(s) ≥ 3927606451461 / 16777216000000`.

For `3 ≤ c ≤ 16` and `1 ≤ o ≤ c` the row index `l = s + o - c` lies in `[s - 15, s]`, so each
row of raw-prefix masses carries mass at least `231/1024`. Since `s ∉ {12, 19}`, the replaced
coefficient `δ^{rep}_{s,c,o}` is the packet deficit `δ^{pk}_{c,o} ≥ 0` for `(c, o) ≠ (3, 1)`, and
`δ^{rep}_{s,3,1} ≥ 1 - ς_s > 49/50`. As the Pascal weights are nonnegative,
`D_cr(s) ≥ (231/1024) (∑_{c=3}^{16} ϖ(c) ∑_{o=1}^{c} δ^{pk}_{c,o} + ϖ(3) (49/50 - δ^{pk}_{3,1}))`,
where the double sum is the explicit rational `15036545331 / 16384000000`, `δ^{pk}_{3,1} = 1/2`
and `ϖ(3) = 1/4`.

## Main results

* `CollatzPosDens.sum_varpi_mul_sum_trPacketDeficit`: the exact value
  `∑_{c=3}^{16} ϖ(c) ∑_{o=1}^{c} δ^{pk}_{c,o} = 15036545331 / 16384000000`.
* `CollatzPosDens.trDirectCrossing_ge`: `D_cr(s) ≥ 3927606451461 / 16777216000000` for `s ≥ 512`.

## Implementation notes

The double sums are evaluated in `ℚ`, using `ϖ(c) = (c - 1) / 2^c` for `c ≥ 2`, and then cast to
`ℝ`. The sum of the packet deficits is regrouped by `c - o` into the weights `W_j` of
`CollatzPosDens.weightQ_eq`, so the packet deficits are not evaluated individually.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.5
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- On `3 ≤ c ≤ 16` the Pascal weight is the rational `(c - 1) / 2^c`. -/
private theorem varpi_eq_cast {c : ℕ} (hc : c ∈ Icc (3 : ℕ) 16) :
    varpi c = ((((c : ℚ) - 1) / 2 ^ c : ℚ) : ℝ) := by
  have hc2 : (2 : ℤ) ≤ c := by simp only [mem_Icc] at hc; omega
  rw [varpi_of_two_le hc2, zpow_neg, zpow_natCast]
  push_cast
  ring

/-- Evaluate `∑_{c=3}^{16} ϖ(c) ∑_{o=1}^{c} g(c, o)` in `ℝ` from its value in `ℚ`. -/
private theorem sum_varpi_mul_sum_cast {g : ℕ → ℕ → ℚ} {q : ℚ}
    (hq : ∑ c ∈ Icc (3 : ℕ) 16, (((c : ℚ) - 1) / 2 ^ c) * ∑ o ∈ Icc 1 c, g c o = q) :
    ∑ c ∈ Icc (3 : ℕ) 16, varpi c * ∑ o ∈ Icc 1 c, (g c o : ℝ) = q := by
  rw [sum_congr rfl fun c hc ↦ by rw [varpi_eq_cast hc], ← hq, Rat.cast_sum]
  refine sum_congr rfl fun c _ ↦ ?_
  rw [Rat.cast_mul, Rat.cast_sum]

/-- The weighted sum of the packet deficits over `3 ≤ c ≤ 16`, `1 ≤ o ≤ c`:
`∑_{c=3}^{16} ϖ(c) ∑_{o=1}^{c} δ^{pk}_{c,o} = 15036545331 / 16384000000`. -/
theorem sum_varpi_mul_sum_trPacketDeficit :
    ∑ c ∈ Icc (3 : ℕ) 16, varpi c * ∑ o ∈ Icc 1 c, (trPacketDeficit c o : ℝ) =
      15036545331 / 16384000000 := by
  rw [sum_varpi_mul_sum_cast (g := trPacketDeficit) (q := 15036545331 / 16384000000) ?_]
  · norm_num
  have h := sum_sum_mul_eq_sum_range (fun c o ↦ ((c : ℚ) - 1) / 2 ^ c * trPacketDeficit c o)
    (fun _ ↦ 1) 0
  simp only [mul_one] at h
  simp only [Finset.mul_sum]
  rw [h]
  change ∑ j ∈ range 16, weightQ j = _
  rw [sum_congr rfl weightQ_eq]
  simp only [sum_range_succ, sum_range_zero]
  norm_num [weightTable]

/-- The packet deficits with the `(3, 1)` entry raised to `49/50`. -/
private def trDTailCoeff (c o : ℕ) : ℚ :=
  if c = 3 ∧ o = 1 then 49 / 50 else trPacketDeficit c o

/-- The weighted sum of the raised packet deficits is
`15036545331 / 16384000000 + ϖ(3) (49/50 - δ^{pk}_{3,1}) = 17002625331 / 16384000000`. -/
private theorem sum_varpi_mul_sum_trDTailCoeff :
    ∑ c ∈ Icc (3 : ℕ) 16, varpi c * ∑ o ∈ Icc 1 c, (trDTailCoeff c o : ℝ) =
      17002625331 / 16384000000 := by
  have hsplit : ∀ c o, (trDTailCoeff c o : ℝ) = (trPacketDeficit c o : ℝ) +
      ((if c = 3 ∧ o = 1 then 49 / 50 - trPacketDeficit 3 1 else 0 : ℚ) : ℝ) := by
    intro c o
    unfold trDTailCoeff
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h; push_cast; ring
    · simp
  simp only [hsplit, sum_add_distrib, mul_add]
  have hq : ∑ c ∈ Icc (3 : ℕ) 16, (((c : ℚ) - 1) / 2 ^ c) * ∑ o ∈ Icc 1 c,
      (if c = 3 ∧ o = 1 then 49 / 50 - trPacketDeficit 3 1 else 0) = 12 / 100 := by
    rw [sum_eq_single 3 (fun c _ hc ↦ by simp [hc]) (by simp),
      sum_eq_single 1 (fun o _ ho ↦ by simp [ho]) (by simp), trPacketDeficit_three_one]
    norm_num
  rw [sum_varpi_mul_sum_trPacketDeficit, sum_varpi_mul_sum_cast hq]
  norm_num

/-- For `s ≥ 512` the raised packet deficits are below the replaced coefficients. -/
private theorem trDTailCoeff_le_trRepCoeff {s : ℕ} (hs : 512 ≤ s) (c o : ℕ) :
    trDTailCoeff c o ≤ trRepCoeff s c o := by
  unfold trDTailCoeff
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    rw [trRepCoeff_three_one]
    have := trRaw3Cap_lt_one_div_fifty hs
    exact le_max_of_le_right (by linarith)
  · rw [trRepCoeff_of_ne h (by omega)]

/-- **The direct first-crossing decrement at large gaps.** For every `s ≥ 512`,
`D_cr(s) ≥ 3927606451461 / 16777216000000`. -/
@[collatz_pos_dens "lem_tr_D_tail"]
theorem trDirectCrossing_ge {s : ℕ} (hs : 512 ≤ s) :
    (3927606451461 / 16777216000000 : ℝ) ≤ trDirectCrossing s := by
  have hlow : ∑ c ∈ Icc (3 : ℕ) 16, varpi c * ∑ o ∈ Icc 1 c,
      (trDTailCoeff c o : ℝ) * (231 / 1024) ≤ trDirectCrossing s := by
    rw [trDirectCrossing]
    refine sum_le_sum fun c hc ↦ mul_le_mul_of_nonneg_left ?_ (varpi_nonneg _)
    refine sum_le_sum fun o ho ↦ mul_le_mul ?_ ?_ (by norm_num) ?_
    · exact_mod_cast trDTailCoeff_le_trRepCoeff hs c o
    · simp only [mem_Icc] at hc ho
      exact rawMass_row_floor hs (by omega) (by omega)
    · exact_mod_cast trRepCoeff_nonneg s c o
  refine le_trans (le_of_eq ?_) hlow
  calc (3927606451461 / 16777216000000 : ℝ)
      = (∑ c ∈ Icc (3 : ℕ) 16, varpi c * ∑ o ∈ Icc 1 c, (trDTailCoeff c o : ℝ)) *
          (231 / 1024) := by
        rw [sum_varpi_mul_sum_trDTailCoeff]; norm_num
    _ = _ := by
        rw [sum_mul]
        refine sum_congr rfl fun c _ ↦ ?_
        rw [← sum_mul]
        ring

end CollatzPosDens
