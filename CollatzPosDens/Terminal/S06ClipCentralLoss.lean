/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.Concentration
public import CollatzPosDens.Terminal.S06ClipWidth

/-!
# Loss outside the central window

For integers `m ≥ 1` and `n ≥ 1`, the words of length `m` whose valuation sum lies outside the
central window `[2m - w, 2m + w]`, with `w = clipWidth m n`, have geometric mass at most
`2 n^{-8}`. Since `w ≥ √(256 m log n)` and `w ≥ 64 log n`, the concentration bound
`2 exp(-min {w²/(32m), w/8})` has exponent at least `8 log n`.

## Main results

* `CollatzPosDens.geomMass_valSum_not_mem_central_le`: the words of length `m` whose valuation
  sum lies outside `[2m - clipWidth m n, 2m + clipWidth m n]` have geometric mass at most
  `2 n^{-8}`.

## Implementation notes

The bound holds for every `n ≥ 1`. For `n = 1` the width is `0` and the bound `2` is trivial.
The valuation sum is compared with the window in `ℤ`, as in `CollatzPosDens.clipWindow`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.4.
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- For `m ≥ 1` and `n ≥ 1`, the words of length `m` whose valuation sum is below
`2m - clipWidth m n` or above `2m + clipWidth m n` have geometric mass at most `2 n^{-8}`. -/
@[collatz_pos_dens "lem_s06_clip_central_loss"]
theorem geomMass_valSum_not_mem_central_le {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    geomMass {u : Word | u.length = m ∧ ((u.valSum : ℤ) < 2 * m - clipWidth m n ∨
        2 * m + clipWidth m n < (u.valSum : ℤ))} ≤
      ENNReal.ofReal (2 * ((n : ℝ) ^ 8)⁻¹) := by
  set w : ℝ := (clipWidth m n : ℝ) with hw
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hw0 : 0 ≤ w := Nat.cast_nonneg _
  have hsub : {u : Word | u.length = m ∧ ((u.valSum : ℤ) < 2 * m - clipWidth m n ∨
      2 * m + clipWidth m n < (u.valSum : ℤ))} ⊆
      {u : Word | u.length = m ∧ w ≤ |(u.valSum : ℝ) - 2 * m|} := by
    rintro u ⟨hl, hu⟩
    refine ⟨hl, ?_⟩
    rcases hu with hu | hu
    · have : (u.valSum : ℝ) < 2 * m - w := by rw [hw]; exact_mod_cast hu
      rw [abs_sub_comm, abs_of_pos (by linarith)]
      linarith
    · have : 2 * m + w < (u.valSum : ℝ) := by rw [hw]; exact_mod_cast hu
      rw [abs_of_pos (by linarith)]
      linarith
  refine (geomMass_mono hsub).trans ((geomMass_abs_valSum_sub_ge_le m w hw0).trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : 256 * m * Real.log n ≤ w ^ 2 := by
    have h := sqrt_le_clipWidth m n
    rw [← hw] at h
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rwa [Real.sq_sqrt (by positivity)] at this
  have h64 : 64 * Real.log n ≤ w := log_le_clipWidth m n
  have hmin : 8 * Real.log n ≤ min (w ^ 2 / (32 * m)) (w / 8) := by
    refine le_min ?_ (by linarith)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hexp : Real.exp (-min (w ^ 2 / (32 * m)) (w / 8)) ≤ ((n : ℝ) ^ 8)⁻¹ := by
    calc Real.exp (-min (w ^ 2 / (32 * m)) (w / 8)) ≤ Real.exp (-(8 * Real.log n)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = ((n : ℝ) ^ 8)⁻¹ := by
        rw [Real.exp_neg, show (8 : ℝ) * Real.log n = ((8 : ℕ) : ℝ) * Real.log n by norm_num,
          Real.exp_nat_mul, Real.exp_log hnR]
  linarith

end CollatzPosDens
