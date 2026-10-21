/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Maps.Valsum

/-!
# A maximal inequality with an exact tilt

Under the geometric mass `𝐩`, the letters of a word `x ∈ ℤ_{≥1}^H` behave like independent
geometric variables of mean `2`, so `S_i(x) = A_i(x) - 2i` is a centred random walk, where
`A_i(x)` is the valuation sum of the prefix `x_{≤ i}`. For `0 ≤ δ < 1` and every integer `v`,
`𝐩({x ∈ ℤ_{≥1}^H : max_{1 ≤ i ≤ H} (A_i(x) - 2i) ≥ v}) ≤ (1 + δ)^{-v} (1 - δ²)^{-H}`.

With `y = 1 + δ`, one letter has tilted mass
`φ = ∑_{a ≥ 1} 2^{-a} y^{a-2} = 1/(y(2 - y)) = (1 - δ²)^{-1} ≥ 1`, and one shows
`y^v 𝐩(E_H(v)) ≤ φ^H`, where `E_H(v)` is the set above.

## Main results

* `CollatzPosDens.fcTiltMaximal_tsum_eq`: the one-letter tilted mass `φ = (1 - δ²)^{-1}`.
* `CollatzPosDens.fcTiltMaximal_geomMass_le`: the maximal inequality.

## Implementation notes

The bound is often proved by grouping the words of `E_H(v)` by their first crossing time and
prefix, an optional stopping argument. We instead argue by induction on `H`, conditioning on the
first letter `a`: a word `a x` lies in `E_{H+1}(v)` exactly when `a - 2 ≥ v` or
`x ∈ E_H(v - (a - 2))`. This gives the same bound without stopping times, and for arbitrary
`H : ℕ`, `v : ℤ` and `δ ≥ 0`, rather than only for `H ≥ 1`, `v ≥ 0` and `δ > 0`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- The predicate `max_{1 ≤ i ≤ H} (A_i(x) - 2i) ≥ v` on words, for an integer level `v`. -/
def fcTiltExceeds (H : ℕ) (v : ℤ) (x : Word) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ H ∧ v ≤ (Word.valSum (x.take i) : ℤ) - 2 * i

/-- No word exceeds any level within `0` steps. -/
theorem fcTiltExceeds_zero (v : ℤ) (x : Word) : ¬ fcTiltExceeds 0 v x := by
  rintro ⟨i, h1, h2, -⟩
  omega

/-- First-letter decomposition: `a x` exceeds `v` within `H + 1` steps iff `a - 2 ≥ v` or `x`
exceeds `v - (a - 2)` within `H` steps. -/
theorem fcTiltExceeds_cons (H : ℕ) (v : ℤ) (a : ℕ+) (x : Word) :
    fcTiltExceeds (H + 1) v (a :: x) ↔
      v ≤ ((a : ℕ) : ℤ) - 2 ∨ fcTiltExceeds H (v - (((a : ℕ) : ℤ) - 2)) x := by
  constructor
  · rintro ⟨i, h1, h2, h⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · left
      simpa using h
    · right
      refine ⟨j, hj, by omega, ?_⟩
      simp only [List.take_succ_cons, Word.valSum_cons] at h
      push_cast at h
      omega
  · rintro (h | ⟨j, h1, h2, h⟩)
    · exact ⟨1, le_rfl, by omega, by simpa using h⟩
    · refine ⟨j + 1, by omega, by omega, ?_⟩
      simp only [List.take_succ_cons, Word.valSum_cons]
      push_cast
      omega

/-- **Tilted maximal inequality, abstract form.** If `y ≥ 1` and the one-letter tilted mass
`Φ = ∑_{a ≥ 1} 2^{-a} y^{a-2}` is at least `1`, then for every integer `v`,
`y^v 𝐩({x ∈ ℤ_{≥1}^H : max_{i ≤ H} (A_i(x) - 2i) ≥ v}) ≤ Φ^H`. -/
theorem fcTiltMaximal_zpow_mul_geomMass_le {y : ℝ} (hy : 1 ≤ y)
    (hΦ : 1 ≤ ∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ENNReal.ofReal (y ^ (((a : ℕ) : ℤ) - 2)))
    (H : ℕ) (v : ℤ) :
    ENNReal.ofReal (y ^ v) * geomMass {x : Word | x.length = H ∧ fcTiltExceeds H v x} ≤
      (∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ENNReal.ofReal (y ^ (((a : ℕ) : ℤ) - 2))) ^ H := by
  set Φ := ∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ENNReal.ofReal (y ^ (((a : ℕ) : ℤ) - 2))
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  induction H generalizing v with
  | zero =>
    have : {x : Word | x.length = 0 ∧ fcTiltExceeds 0 v x} = ∅ := by
      ext x
      simp [fcTiltExceeds_zero]
    rw [this]
    simp
  | succ H ih =>
    rw [geomMass_setOf_length_succ_and, ← ENNReal.tsum_mul_left, pow_succ',
      ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun a => ?_
    have hzpow : ENNReal.ofReal (y ^ v) =
        ENNReal.ofReal (y ^ (((a : ℕ) : ℤ) - 2)) *
          ENNReal.ofReal (y ^ (v - (((a : ℕ) : ℤ) - 2))) := by
      rw [← ENNReal.ofReal_mul (zpow_pos hy0 _).le, ← zpow_add₀ hy0.ne']
      congr 2
      ring
    by_cases hav : v ≤ ((a : ℕ) : ℤ) - 2
    · have hset : {x : Word | x.length = H ∧ fcTiltExceeds (H + 1) v (a :: x)} =
          {x : Word | x.length = H} := by
        ext x
        simp [fcTiltExceeds_cons, hav]
      rw [hset, geomMass_setOf_length_eq, mul_one]
      calc ENNReal.ofReal (y ^ v) * 2⁻¹ ^ (a : ℕ)
          ≤ ENNReal.ofReal (y ^ (((a : ℕ) : ℤ) - 2)) * 2⁻¹ ^ (a : ℕ) := by
            gcongr
        _ = 2⁻¹ ^ (a : ℕ) * ENNReal.ofReal (y ^ (((a : ℕ) : ℤ) - 2)) * 1 := by ring
        _ ≤ 2⁻¹ ^ (a : ℕ) * ENNReal.ofReal (y ^ (((a : ℕ) : ℤ) - 2)) * Φ ^ H := by
            gcongr
            exact one_le_pow₀ hΦ
    · have hset : {x : Word | x.length = H ∧ fcTiltExceeds (H + 1) v (a :: x)} =
          {x : Word | x.length = H ∧ fcTiltExceeds H (v - (((a : ℕ) : ℤ) - 2)) x} := by
        ext x
        simp [fcTiltExceeds_cons, hav]
      rw [hset, hzpow]
      calc _ = 2⁻¹ ^ (a : ℕ) * ENNReal.ofReal (y ^ (((a : ℕ) : ℤ) - 2)) *
              (ENNReal.ofReal (y ^ (v - (((a : ℕ) : ℤ) - 2))) *
                geomMass {x : Word | x.length = H ∧
                  fcTiltExceeds H (v - (((a : ℕ) : ℤ) - 2)) x}) := by ring
        _ ≤ 2⁻¹ ^ (a : ℕ) * ENNReal.ofReal (y ^ (((a : ℕ) : ℤ) - 2)) * Φ ^ H := by
            gcongr
            exact ih _

/-- **One-letter tilted mass.** For `0 ≤ δ < 1`,
`∑_{a ≥ 1} 2^{-a} (1 + δ)^{a-2} = (1 - δ²)^{-1}`. -/
theorem fcTiltMaximal_tsum_eq {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    ∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ENNReal.ofReal ((1 + δ) ^ (((a : ℕ) : ℤ) - 2)) =
      ENNReal.ofReal (1 - δ ^ 2)⁻¹ := by
  set y := 1 + δ with hy_def
  have hy0 : 0 < y := by positivity
  have hs : HasSum (fun n : ℕ => (2 * y)⁻¹ * (y / 2) ^ n) (1 - δ ^ 2)⁻¹ := by
    convert (hasSum_geometric_of_lt_one (by positivity) (by linarith : y / 2 < 1)).mul_left
      (2 * y)⁻¹ using 1
    rw [← mul_inv, hy_def]
    congr 1
    ring
  have hterm : ∀ n : ℕ, (2⁻¹ : ℝ≥0∞) ^ (n + 1) * ENNReal.ofReal (y ^ (((n + 1 : ℕ) : ℤ) - 2)) =
      ENNReal.ofReal ((2 * y)⁻¹ * (y / 2) ^ n) := by
    intro n
    rw [show (2⁻¹ : ℝ≥0∞) = ENNReal.ofReal 2⁻¹ by
        rw [ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat],
      ← ENNReal.ofReal_pow (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [show (((n + 1 : ℕ) : ℤ) - 2) = (n : ℤ) + (-1 : ℤ) by push_cast; ring,
      zpow_add₀ hy0.ne', zpow_natCast, zpow_neg_one, div_pow, mul_inv, pow_succ]
    field_simp
    rw [← mul_pow]
    norm_num
  rw [tsum_pnat_eq_tsum_succ
      (f := fun n : ℕ => (2⁻¹ : ℝ≥0∞) ^ n * ENNReal.ofReal (y ^ ((n : ℤ) - 2))),
    tsum_congr hterm, ← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs.summable,
    hs.tsum_eq]

/-- **Maximal inequality with an exact tilt.** For integers `H ≥ 0` and `v`, and `0 ≤ δ < 1`,
`𝐩({x ∈ ℤ_{≥1}^H : max_{1 ≤ i ≤ H} (A_i(x) - 2i) ≥ v}) ≤ (1 + δ)^{-v} (1 - δ²)^{-H}`. -/
@[collatz_pos_dens "lem_fc_tilt_maximal"]
theorem fcTiltMaximal_geomMass_le (H : ℕ) (v : ℤ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    geomMass {x : Word | x.length = H ∧
        ∃ i, 1 ≤ i ∧ i ≤ H ∧ v ≤ (Word.valSum (x.take i) : ℤ) - 2 * i} ≤
      ENNReal.ofReal ((1 + δ) ^ (-v) * (1 - δ ^ 2) ^ (-(H : ℤ))) := by
  have hy : 1 ≤ 1 + δ := by linarith
  have hy0 : 0 < 1 + δ := by linarith
  have hd0 : 0 < 1 - δ ^ 2 := by nlinarith
  have hd1 : 1 - δ ^ 2 ≤ 1 := by nlinarith
  have hφ := fcTiltMaximal_tsum_eq hδ0 hδ1
  have hmain := fcTiltMaximal_zpow_mul_geomMass_le hy
    (by rw [hφ]; exact ENNReal.one_le_ofReal.mpr (one_le_inv₀ hd0 |>.mpr hd1)) H v
  rw [hφ] at hmain
  change ENNReal.ofReal ((1 + δ) ^ v) *
    geomMass {x : Word | x.length = H ∧ fcTiltExceeds H v x} ≤ _ at hmain
  calc geomMass {x : Word | x.length = H ∧ fcTiltExceeds H v x}
      = ENNReal.ofReal ((1 + δ) ^ (-v)) * (ENNReal.ofReal ((1 + δ) ^ v) *
          geomMass {x : Word | x.length = H ∧ fcTiltExceeds H v x}) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (zpow_pos hy0 _).le, ← zpow_add₀ hy0.ne',
          neg_add_cancel, zpow_zero, ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal ((1 + δ) ^ (-v)) * ENNReal.ofReal (1 - δ ^ 2)⁻¹ ^ H := by
        gcongr
    _ = ENNReal.ofReal ((1 + δ) ^ (-v) * (1 - δ ^ 2) ^ (-(H : ℤ))) := by
        rw [← ENNReal.ofReal_pow (inv_pos.2 hd0).le, ← ENNReal.ofReal_mul (zpow_pos hy0 _).le,
          zpow_neg (1 - δ ^ 2), zpow_natCast, inv_pow]

end CollatzPosDens
