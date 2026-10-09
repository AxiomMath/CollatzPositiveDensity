/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.FirstCrossing.FcGeomTail
public import CollatzPosDens.FirstCrossing.FcMaximal
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Maximum versus endpoint

Under the geometric mass `𝐩`, the letters of a word `x ∈ ℤ_{≥1}^H` behave like independent
geometric variables of mean `2`, so `S_i(x) = A_i(x) - 2i` is a centred random walk, where
`A_i(x)` is the valuation sum of the prefix `x_{≤ i}`. A reflection-type argument bounds the
probability that the maximum of the walk reaches a level by twice the probability that its
endpoint does:
`𝐩({x ∈ ℤ_{≥1}^H : max_{1 ≤ i ≤ H} S_i(x) ≥ v}) ≤ 2 𝐩({x ∈ ℤ_{≥1}^H : S_H(x) ≥ v})`.

The key input is that the walk is at least as likely to end nonnegative as not:
`𝐩({y ∈ ℤ_{≥1}^m : A(y) ≥ 2m}) ≥ 1/2` for every `m ≥ 0`, which follows from the binomial form
of geometric tails and the symmetry of binomial coefficients.

## Main results

* `CollatzPosDens.fcReflection_half_le_geomMass`: `𝐩({y ∈ ℤ_{≥1}^m : A(y) ≥ 2m}) ≥ 1/2`.
* `CollatzPosDens.fcReflection_geomMass_le`: the maximum-versus-endpoint inequality.

## Implementation notes

Words of length `H` stand for `ℤ_{≥1}^H`, and the condition `max_{1 ≤ i ≤ H} S_i(x) ≥ v` is
written as the existence of `1 ≤ i ≤ H` with `S_i(x) ≥ v`; for `H = 0` the left-hand set is then
empty, so the hypothesis `H ≥ 1` is dropped. Rather than grouping words by their first crossing
time and prefix, we argue by induction on `H`, conditioning on the first letter `a`: the word
`a y` crosses `v` within `H + 1` steps exactly when `a - 2 ≥ v` or `y` crosses `v - (a - 2)`
within `H` steps. In the first case all continuations `y` are counted on the left, and at least
half of them (by mass) end above `v` on the right; in the second case the induction hypothesis
applies at the shifted level.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- **The centred walk ends nonnegative with probability at least `1/2`.** For every `m ≥ 0`,
`𝐩({y ∈ ℤ_{≥1}^m : A(y) ≥ 2m}) ≥ 1/2`. -/
theorem fcReflection_half_le_geomMass (m : ℕ) :
    2⁻¹ ≤ geomMass {y : Word | y.length = m ∧ 2 * m ≤ y.valSum} := by
  rcases m with _ | k
  · simp only [mul_zero, zero_le, and_true]
    rw [geomMass_setOf_length_eq]
    exact ENNReal.inv_le_one.mpr one_le_two
  · rw [geomMass_setOf_length_eq_le_valSum _ _ (by omega)]
    have hs : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
    rw [hs]
    have hsum := Nat.sum_range_choose_halfway k
    have hc : ∑ t ∈ Finset.range (k + 1), ((2 * k + 1).choose t : ℝ≥0∞) = 4 ^ k := by
      exact_mod_cast hsum
    rw [hc, show (4 : ℝ≥0∞) = 2 ^ 2 by norm_num, ← pow_mul, pow_succ, mul_right_comm, ← mul_pow,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]

/-- **Maximum versus endpoint.** For every integer `H ≥ 0` and real `v`,
`𝐩({x ∈ ℤ_{≥1}^H : max_{1 ≤ i ≤ H} (A_i(x) - 2i) ≥ v}) ≤ 2 𝐩({x ∈ ℤ_{≥1}^H : A(x) - 2H ≥ v})`. -/
@[collatz_pos_dens "lem_fc_reflection"]
theorem fcReflection_geomMass_le (H : ℕ) (v : ℝ) :
    geomMass {x : Word | x.length = H ∧
        ∃ i, 1 ≤ i ∧ i ≤ H ∧ v ≤ (Word.valSum (x.take i) : ℝ) - 2 * i} ≤
      2 * geomMass {x : Word | x.length = H ∧ v ≤ (x.valSum : ℝ) - 2 * H} := by
  change geomMass {x : Word | x.length = H ∧ fcMaximalExceeds H v x} ≤ _
  induction H generalizing v with
  | zero =>
    have : {x : Word | x.length = 0 ∧ fcMaximalExceeds 0 v x} = ∅ := by
      ext x; simp [fcMaximalExceeds_zero]
    rw [this, geomMass_empty]
    exact bot_le
  | succ H ih =>
    rw [geomMass_setOf_length_succ_and, geomMass_setOf_length_succ_and, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun a => ?_
    have hR : {y : Word | y.length = H ∧
        v ≤ (Word.valSum (a :: y) : ℝ) - 2 * ((H + 1 : ℕ) : ℝ)} =
        {y : Word | y.length = H ∧ v - ((a : ℝ) - 2) ≤ (y.valSum : ℝ) - 2 * H} := by
      ext y
      simp only [Set.mem_ofPred_eq, Word.valSum_cons]
      push_cast
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    rw [hR, mul_left_comm]
    gcongr
    by_cases hav : v ≤ (a : ℝ) - 2
    · have hset : {x : Word | x.length = H ∧ fcMaximalExceeds (H + 1) v (a :: x)} =
          {x : Word | x.length = H} := by
        ext x; simp [fcMaximalExceeds_cons, hav]
      rw [hset, geomMass_setOf_length_eq]
      have hsub : {y : Word | y.length = H ∧ 2 * H ≤ y.valSum} ⊆
          {y : Word | y.length = H ∧ v - ((a : ℝ) - 2) ≤ (y.valSum : ℝ) - 2 * H} := by
        rintro y ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have : ((2 * H : ℕ) : ℝ) ≤ y.valSum := by exact_mod_cast h2
        push_cast at this
        linarith
      calc (1 : ℝ≥0∞) = 2 * 2⁻¹ := (ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top).symm
        _ ≤ 2 * geomMass {y : Word | y.length = H ∧ 2 * H ≤ y.valSum} := by
          gcongr; exact fcReflection_half_le_geomMass H
        _ ≤ _ := by gcongr; exact geomMass_mono hsub
    · have hset : {x : Word | x.length = H ∧ fcMaximalExceeds (H + 1) v (a :: x)} =
          {x : Word | x.length = H ∧ fcMaximalExceeds H (v - ((a : ℝ) - 2)) x} := by
        ext x; simp [fcMaximalExceeds_cons, hav]
      rw [hset]
      exact ih _

end CollatzPosDens
