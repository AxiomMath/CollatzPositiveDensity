/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Transfer.GeometricTotal
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.FirstCrossing.FcMgf
public import CollatzPosDens.Transfer.Concentration

/-!
# A maximal inequality for valuation sums

Under the geometric mass `𝐩`, the letters of a word `x ∈ ℤ_{≥1}^H` behave like independent
geometric variables of mean `2`, so `S_i(x) = A_i(x) - 2i` is a centred random walk, where
`A_i(x)` is the valuation sum of the prefix `x_{≤ i}`. We prove the exponential maximal
inequality
`𝐩({x ∈ ℤ_{≥1}^H : max_{1 ≤ i ≤ H} (A_i(x) - 2i) ≥ v}) ≤ exp(-2v²/(9H))`
whenever `v ≥ 0` and `4v/(9H) ≤ 1/32`.

With `φ(t) = ∑_{a ≥ 1} 2^{-a} e^{t(a-2)}` and `t ≥ 0` such that `φ(t) ≥ 1`, one shows
`e^{tv} 𝐩(E_H(v)) ≤ φ(t)^H` for every real `v`, where `E_H(v)` is the set above. Choosing
`t = 4v/(9H)` and using `φ(t) ≤ e^{9t²/8}` gives the claim.

## Main definitions

* `CollatzPosDens.fcMaximalExceeds`: the predicate `max_{1 ≤ i ≤ H} (A_i(x) - 2i) ≥ v`.

## Main results

* `CollatzPosDens.fcMaximal_exp_mul_geomMass_le`: `e^{tv} 𝐩(E_H(v)) ≤ φ(t)^H`.
* `CollatzPosDens.fcMaximal_geomMass_le`: the maximal inequality.

## Implementation notes

The source groups the words of `E_H(v)` by their first crossing time and prefix (an optional
stopping argument). We instead argue by induction on `H`, conditioning on the first letter `a`:
a word `a y` lies in `E_{H+1}(v)` exactly when `a - 2 ≥ v` or `y ∈ E_H(v - (a - 2))`. This
gives the same bound without stopping times. The hypotheses `H ≥ 1` and `v > 0` of the source
are relaxed to `v ≥ 0` (for `H = 0` the set is empty).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open Real

namespace CollatzPosDens

/-- The predicate `max_{1 ≤ i ≤ H} (A_i(x) - 2i) ≥ v` on words. -/
def fcMaximalExceeds (H : ℕ) (v : ℝ) (x : Word) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ H ∧ v ≤ (Word.valSum (x.take i) : ℝ) - 2 * i

/-- No word exceeds any level within `0` steps. -/
theorem fcMaximalExceeds_zero (v : ℝ) (x : Word) : ¬ fcMaximalExceeds 0 v x := by
  rintro ⟨i, h1, h2, -⟩
  omega

/-- First-letter decomposition: `a y` exceeds `v` within `H + 1` steps iff `a - 2 ≥ v` or `y`
exceeds `v - (a - 2)` within `H` steps. -/
theorem fcMaximalExceeds_cons (H : ℕ) (v : ℝ) (a : ℕ+) (y : Word) :
    fcMaximalExceeds (H + 1) v (a :: y) ↔
      v ≤ (a : ℝ) - 2 ∨ fcMaximalExceeds H (v - ((a : ℝ) - 2)) y := by
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
      linarith
  · rintro (h | ⟨j, h1, h2, h⟩)
    · exact ⟨1, le_rfl, by omega, by simpa using h⟩
    · refine ⟨j + 1, by omega, by omega, ?_⟩
      simp only [List.take_succ_cons, Word.valSum_cons]
      push_cast
      linarith

/-- **Exponential maximal inequality.** If `t ≥ 0` and `Φ = ∑_{a ≥ 1} 2^{-a} e^{t(a-2)} ≥ 1`,
then for every real `v`, `e^{tv} 𝐩({x ∈ ℤ_{≥1}^H : max_{i ≤ H} (A_i(x) - 2i) ≥ v}) ≤ Φ^H`. -/
theorem fcMaximal_exp_mul_geomMass_le {t : ℝ} (ht : 0 ≤ t)
    (hΦ : 1 ≤ concentrationMgf t) (H : ℕ) (v : ℝ) :
    ENNReal.ofReal (exp (t * v)) * geomMass {x : Word | x.length = H ∧ fcMaximalExceeds H v x} ≤
      concentrationMgf t ^ H := by
  rw [concentrationMgf] at hΦ ⊢
  set Φ := ∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * ENNReal.ofReal (exp (t * ((a : ℝ) - 2)))
  induction H generalizing v with
  | zero =>
    have : {x : Word | x.length = 0 ∧ fcMaximalExceeds 0 v x} = ∅ := by
      ext x
      simp [fcMaximalExceeds_zero]
    rw [this]
    simp
  | succ H ih =>
    rw [geomMass_setOf_length_succ_and, ← ENNReal.tsum_mul_left, pow_succ',
      ← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun a => ?_
    by_cases hav : v ≤ (a : ℝ) - 2
    · have hset : {x : Word | x.length = H ∧ fcMaximalExceeds (H + 1) v (a :: x)} =
          {x : Word | x.length = H} := by
        ext x
        simp [fcMaximalExceeds_cons, hav]
      rw [hset, geomMass_setOf_length_eq, mul_one]
      calc ENNReal.ofReal (exp (t * v)) * 2⁻¹ ^ (a : ℕ)
          ≤ ENNReal.ofReal (exp (t * ((a : ℝ) - 2))) * 2⁻¹ ^ (a : ℕ) := by
            gcongr
        _ = 2⁻¹ ^ (a : ℕ) * ENNReal.ofReal (exp (t * ((a : ℝ) - 2))) * 1 := by ring
        _ ≤ 2⁻¹ ^ (a : ℕ) * ENNReal.ofReal (exp (t * ((a : ℝ) - 2))) * Φ ^ H := by
            gcongr
            exact one_le_pow₀ hΦ
    · have hset : {x : Word | x.length = H ∧ fcMaximalExceeds (H + 1) v (a :: x)} =
          {x : Word | x.length = H ∧ fcMaximalExceeds H (v - ((a : ℝ) - 2)) x} := by
        ext x
        simp [fcMaximalExceeds_cons, hav]
      have hexp : ENNReal.ofReal (exp (t * v)) =
          ENNReal.ofReal (exp (t * ((a : ℝ) - 2))) *
            ENNReal.ofReal (exp (t * (v - ((a : ℝ) - 2)))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← Real.exp_add]
        congr 2
        ring
      rw [hset, hexp]
      calc _ = 2⁻¹ ^ (a : ℕ) * ENNReal.ofReal (exp (t * ((a : ℝ) - 2))) *
              (ENNReal.ofReal (exp (t * (v - ((a : ℝ) - 2)))) *
                geomMass {x : Word | x.length = H ∧
                  fcMaximalExceeds H (v - ((a : ℝ) - 2)) x}) := by ring
        _ ≤ 2⁻¹ ^ (a : ℕ) * ENNReal.ofReal (exp (t * ((a : ℝ) - 2))) * Φ ^ H := by
            gcongr
            exact ih _

/-- **Maximal inequality for valuation sums.** For `v ≥ 0` with `4v/(9H) ≤ 1/32`,
`𝐩({x ∈ ℤ_{≥1}^H : max_{1 ≤ i ≤ H} (A_i(x) - 2i) ≥ v}) ≤ exp(-2v²/(9H))`. -/
@[collatz_pos_dens "lem_fc_maximal"]
theorem fcMaximal_geomMass_le (H : ℕ) {v : ℝ} (hv : 0 ≤ v) (hvH : 4 * v / (9 * H) ≤ 1 / 32) :
    geomMass {x : Word | x.length = H ∧
        ∃ i, 1 ≤ i ∧ i ≤ H ∧ v ≤ (Word.valSum (x.take i) : ℝ) - 2 * i} ≤
      ENNReal.ofReal (exp (-2 * v ^ 2 / (9 * H))) := by
  set t := 4 * v / (9 * H) with ht_def
  have ht0 : 0 ≤ t := by positivity
  have htabs : |t| ≤ 1 / 32 := by rwa [abs_of_nonneg ht0]
  have hb := fcMgf_bounds htabs
  have he2 : exp t < 2 := by
    have := Real.add_one_le_exp (-t)
    have h1 : exp t * exp (-t) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [exp_pos t, exp_pos (-t)]
  have hΦ := concentrationMgf_eq_ofReal he2
  have hmain := fcMaximal_exp_mul_geomMass_le ht0
    (hΦ ▸ ENNReal.one_le_ofReal.mpr hb.1) H v
  rw [hΦ] at hmain
  calc geomMass _ = ENNReal.ofReal (exp (-(t * v))) *
        (ENNReal.ofReal (exp (t * v)) * geomMass _) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add, neg_add_cancel,
          Real.exp_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ ENNReal.ofReal (exp (-(t * v))) * ENNReal.ofReal (exp (H * (9 * t ^ 2 / 8))) := by
        gcongr
        refine hmain.trans ?_
        rw [← ENNReal.ofReal_pow (zero_le_one.trans hb.1), Real.exp_nat_mul]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (zero_le_one.trans hb.1) hb.2 H)
      _ = ENNReal.ofReal (exp (-2 * v ^ 2 / (9 * H))) := by
        rw [← ENNReal.ofReal_mul (exp_pos _).le, ← Real.exp_add]
        congr 2
        rcases Nat.eq_zero_or_pos H with rfl | hH
        · simp [ht_def]
        · have : (H : ℝ) ≠ 0 := by positivity
          rw [ht_def]
          field_simp
          ring

end CollatzPosDens
