/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnHoldList
public import CollatzPosDens.Renewal.RnPascalTotal
public import CollatzPosDens.Renewal.RnVpgf
public import CollatzPosDens.Renewal.RnVpgfTilt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Vertical tail of hold lists

For `P ∈ ℕ` and real `Y`, the hold-list weights `η^{⊗P}(h)` of the hold lists `h ∈ 𝒫^P` whose
total vertical displacement `l(h_1) + ⋯ + l(h_P)` is at least `Y` sum to at most
`8^P (25/27)^Y`.

On that range `1 ≤ (27/25)^{∑_i l(h_i) - Y}`, so the sum is at most
`(25/27)^Y ∏_{i=1}^P ∑_{h_i ∈ 𝒫} η(h_i) (27/25)^{l(h_i)} = (25/27)^Y 𝖵(27/25)^P`, and
`𝖵(27/25) < 8`.

## Main results

* `CollatzPosDens.tsum_holdListLaw_verTail_le`: the bound, as a sum in `[0, ∞]`.
* `CollatzPosDens.summable_holdListLaw_verTail`: the real series converges.
* `CollatzPosDens.tsum_holdListLaw_verTail_le_real`: the bound for the real series.

## Implementation notes

As for `holdListLaw`, a point is a pair `(j, l) : ℕ × ℤ`, and `𝒫 = ℤ_{≥1} × ℤ` is the set
of pairs with `1 ≤ j`; the restriction matters, since `η(0, 0) = 1`. So `𝒫^P` is the set of
tuples `h : Fin P → ℕ × ℤ` with `1 ≤ j(h_i)` for all `i`, and the range of summation is the
subtype of those tuples with moreover `Y ≤ ∑_i l(h_i)`. The principal statement is the sum in
`[0, ∞]` of the terms embedded by `ENNReal.ofReal`, which needs no summability hypothesis; the
real-valued form, with its convergence, is deduced from it.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- On the vertical tail, `η^{⊗P}(h) ≤ (25/27)^Y ∏_i η(h_i) (27/25)^{l(h_i)}`. -/
private lemma holdListLaw_le_verTail {P : ℕ} {Y : ℝ} (h : Fin P → ℕ × ℤ)
    (hY : Y ≤ ∑ i, ((h i).2 : ℝ)) :
    holdListLaw h ≤
      (25 / 27 : ℝ) ^ Y * ∏ i, (holdLaw (h i).1 (h i).2 * (27 / 25 : ℝ) ^ (h i).2) := by
  set r : ℝ := 27 / 25
  have hr0 : (0 : ℝ) < r := by norm_num [r]
  have hl : r ^ Y ≤ ∏ i, r ^ (h i).2 := by
    calc r ^ Y ≤ r ^ (∑ i, ((h i).2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num [r]) hY
      _ = ∏ i, r ^ (h i).2 := by
          rw [Real.rpow_sum_of_pos hr0]
          exact Finset.prod_congr rfl fun i _ ↦ Real.rpow_intCast r _
  have hinv : (25 / 27 : ℝ) ^ Y * r ^ Y = 1 := by
    rw [← Real.mul_rpow (by norm_num) hr0.le]
    norm_num [r]
  rw [Finset.prod_mul_distrib, holdListLaw_def]
  have h0 : 0 ≤ ∏ i, holdLaw (h i).1 (h i).2 :=
    Finset.prod_nonneg fun i _ ↦ holdLaw_nonneg _ _
  calc ∏ i, holdLaw (h i).1 (h i).2
      = (25 / 27 : ℝ) ^ Y * r ^ Y * ∏ i, holdLaw (h i).1 (h i).2 := by rw [hinv, one_mul]
    _ ≤ (25 / 27 : ℝ) ^ Y * (∏ i, r ^ (h i).2) * ∏ i, holdLaw (h i).1 (h i).2 := by gcongr
    _ = _ := by ring

/-- **Vertical tail of hold lists.** For `P ∈ ℕ` and real `Y`, in `[0, ∞]`,
`∑ η^{⊗P}(h) ≤ 8^P (25/27)^Y`, the sum over `h ∈ 𝒫^P` with `Y ≤ l(h_1) + ⋯ + l(h_P)`. Here
`𝒫^P` is the set of `h : Fin P → ℕ × ℤ` with `1 ≤ j(h_i)` for every `i`. -/
@[collatz_pos_dens "lem_rn_list_ver_tail"]
theorem tsum_holdListLaw_verTail_le (P : ℕ) (Y : ℝ) :
    ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ Y ≤ ∑ i, ((h i).2 : ℝ)},
      ENNReal.ofReal (holdListLaw h.1) ≤ ENNReal.ofReal (8 ^ P * (25 / 27 : ℝ) ^ Y) := by
  set G : (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun h ↦
    ∏ i, ENNReal.ofReal (holdLaw (h i).1 (h i).2 * (27 / 25 : ℝ) ^ (h i).2)
  set c : ℝ≥0∞ := ENNReal.ofReal ((25 / 27 : ℝ) ^ Y)
  have hpt : ∀ h : Fin P → ℕ × ℤ, Y ≤ ∑ i, ((h i).2 : ℝ) →
      ENNReal.ofReal (holdListLaw h) ≤ c * G h := by
    intro h hY
    refine (ENNReal.ofReal_le_ofReal (holdListLaw_le_verTail h hY)).trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg fun i _ ↦
      mul_nonneg (holdLaw_nonneg _ _) (by positivity)]
  have hG : ∑' h : {h : Fin P → ℕ × ℤ // ∀ i, 1 ≤ (h i).1}, G h.1 =
      holdVpgf (27 / 25) ^ P := by
    rw [holdVpgf_eq_tsum_natPoints, ← tsum_pi_fin_prod_ennreal_const]
    exact (Equiv.subtypePiEquivPi (α := Fin P) (p := fun _ (p : ℕ × ℤ) ↦ 1 ≤ p.1)).tsum_eq
      (fun h ↦ ∏ i, ENNReal.ofReal (holdLaw (h i).1.1 (h i).1.2 * (27 / 25 : ℝ) ^ (h i).1.2))
  calc ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ Y ≤ ∑ i, ((h i).2 : ℝ)},
        ENNReal.ofReal (holdListLaw h.1)
      ≤ ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ Y ≤ ∑ i, ((h i).2 : ℝ)},
          c * G h.1 := ENNReal.tsum_le_tsum fun h ↦ hpt h.1 h.2.2
    _ ≤ ∑' h : {h : Fin P → ℕ × ℤ // ∀ i, 1 ≤ (h i).1}, c * G h.1 :=
        ENNReal.tsum_mono_subtype (fun h ↦ c * G h)
          (s := {h | (∀ i, 1 ≤ (h i).1) ∧ Y ≤ ∑ i, ((h i).2 : ℝ)})
          (t := {h | ∀ i, 1 ≤ (h i).1}) fun h hh ↦ hh.1
    _ = c * holdVpgf (27 / 25) ^ P := by rw [ENNReal.tsum_mul_left, hG]
    _ ≤ c * 8 ^ P := by
        gcongr
        exact holdVpgf_tilt_lt.le
    _ = ENNReal.ofReal (8 ^ P * (25 / 27 : ℝ) ^ Y) := by
        rw [mul_comm, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat]

/-- The real series of hold-list weights over the vertical tail converges. -/
theorem summable_holdListLaw_verTail (P : ℕ) (Y : ℝ) :
    Summable fun h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ Y ≤ ∑ i, ((h i).2 : ℝ)} ↦
      holdListLaw h.1 :=
  (ENNReal.summable_toReal ((tsum_holdListLaw_verTail_le P Y).trans_lt
    ENNReal.ofReal_lt_top).ne).congr fun _ ↦ ENNReal.toReal_ofReal (holdListLaw_nonneg _)

/-- **Vertical tail of hold lists**, real form: `∑ η^{⊗P}(h) ≤ 8^P (25/27)^Y`, the sum over
`h ∈ 𝒫^P` with `Y ≤ l(h_1) + ⋯ + l(h_P)`. -/
theorem tsum_holdListLaw_verTail_le_real (P : ℕ) (Y : ℝ) :
    ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ Y ≤ ∑ i, ((h i).2 : ℝ)},
      holdListLaw h.1 ≤ 8 ^ P * (25 / 27 : ℝ) ^ Y := by
  have h := tsum_holdListLaw_verTail_le P Y
  rwa [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ holdListLaw_nonneg _)
    (summable_holdListLaw_verTail P Y), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h

end CollatzPosDens
