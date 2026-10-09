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
public import CollatzPosDens.Renewal.RnVpgfLow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lower vertical tail of hold lists

For `P ∈ ℕ` and real `Y`, the hold-list weights `η^{⊗P}(h)` of the hold lists `h ∈ 𝒫^P` whose
total vertical displacement `l(h_1) + ⋯ + l(h_P)` is at most `Y` sum to at most
`v^{(127/10) P - Y}`, where `v = 4095/4096`.

Since `0 < v < 1`, on that range `1 ≤ v^{∑_i l(h_i) - Y}`, so the sum is at most
`v^{-Y} ∏_{i=1}^P ∑_{h_i ∈ 𝒫} η(h_i) v^{l(h_i)} = v^{-Y} 𝖵(v)^P`, and `𝖵(v)^{10} < v^{127}` gives
`𝖵(v) ≤ v^{127/10}`.

## Main results

* `CollatzPosDens.tsum_holdListLaw_verLow_le`: the bound, as a sum in `[0, ∞]`.
* `CollatzPosDens.summable_holdListLaw_verLow`: the real series converges.
* `CollatzPosDens.tsum_holdListLaw_verLow_le_real`: the bound for the real series.

## Implementation notes

As for the hold-list weight, a point is a pair `(j, l) : ℕ × ℤ`, and `𝒫 = ℤ_{≥1} × ℤ` is the set
of pairs with `1 ≤ j`; the restriction matters, since `η(0, 0) = 1`. So `𝒫^P` is the set of
tuples `h : Fin P → ℕ × ℤ` with `1 ≤ j(h_i)` for all `i`, and the range of summation is the
subtype of those tuples with moreover `∑_i l(h_i) ≤ Y`. The principal statement is the sum in
`[0, ∞]` of the terms embedded by `ENNReal.ofReal`, which needs no summability hypothesis; the
real-valued form, with its convergence, is deduced from it. The power `v^{(127/10) P - Y}` is the
real power. Taking tenth roots needs no positivity of `𝖵(v)`: in `[0, ∞]`, `a^{10} ≤ b^{10}`
implies `a ≤ b` outright.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- On the lower vertical tail, `η^{⊗P}(h) ≤ v^{-Y} ∏_i η(h_i) v^{l(h_i)}` with
`v = 4095/4096`. -/
private lemma holdListLaw_le_verLow {P : ℕ} {Y : ℝ} (h : Fin P → ℕ × ℤ)
    (hY : ∑ i, ((h i).2 : ℝ) ≤ Y) :
    holdListLaw h ≤
      (4095 / 4096 : ℝ) ^ (-Y) * ∏ i, (holdLaw (h i).1 (h i).2 * (4095 / 4096 : ℝ) ^ (h i).2) := by
  set v : ℝ := 4095 / 4096
  have hv0 : (0 : ℝ) < v := by norm_num [v]
  have hl : v ^ Y ≤ ∏ i, v ^ (h i).2 :=
    calc v ^ Y ≤ v ^ (∑ i, ((h i).2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hv0 (by norm_num [v]) hY
      _ = ∏ i, v ^ (h i).2 := by
          rw [Real.rpow_sum_of_pos hv0]
          exact Finset.prod_congr rfl fun i _ ↦ Real.rpow_intCast v _
  have hinv : v ^ (-Y) * v ^ Y = 1 := by
    rw [← Real.rpow_add hv0]
    simp
  rw [Finset.prod_mul_distrib, holdListLaw_def]
  have h0 : 0 ≤ ∏ i, holdLaw (h i).1 (h i).2 :=
    Finset.prod_nonneg fun i _ ↦ holdLaw_nonneg _ _
  have hvY : (0 : ℝ) ≤ v ^ (-Y) := by positivity
  calc ∏ i, holdLaw (h i).1 (h i).2
      = v ^ (-Y) * v ^ Y * ∏ i, holdLaw (h i).1 (h i).2 := by rw [hinv, one_mul]
    _ ≤ v ^ (-Y) * (∏ i, v ^ (h i).2) * ∏ i, holdLaw (h i).1 (h i).2 := by gcongr
    _ = _ := by ring

/-- `𝖵(4095/4096) ≤ (4095/4096)^{127/10}`, the positive tenth root of
`𝖵(4095/4096)^{10} < (4095/4096)^{127}`. -/
private lemma holdVpgf_low_le_rpow_verLow :
    holdVpgf (4095 / 4096) ≤ ENNReal.ofReal ((4095 / 4096 : ℝ) ^ (127 / 10 : ℝ)) := by
  refine (ENNReal.pow_le_pow_left_iff (n := 10) (by norm_num)).mp ?_
  refine holdVpgf_low_pow_lt.le.trans_eq ?_
  rw [← ENNReal.ofReal_pow (by positivity), ← Real.rpow_mul_natCast (by norm_num)]
  norm_num

/-- **Lower vertical tail of hold lists.** For `P ∈ ℕ` and real `Y`, in `[0, ∞]`,
`∑ η^{⊗P}(h) ≤ (4095/4096)^{(127/10) P - Y}`, the sum over `h ∈ 𝒫^P` with
`l(h_1) + ⋯ + l(h_P) ≤ Y`. Here `𝒫^P` is the set of `h : Fin P → ℕ × ℤ` with `1 ≤ j(h_i)` for
every `i`. -/
@[collatz_pos_dens "lem_rn_list_ver_low"]
theorem tsum_holdListLaw_verLow_le (P : ℕ) (Y : ℝ) :
    ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).2 : ℝ) ≤ Y},
      ENNReal.ofReal (holdListLaw h.1) ≤
        ENNReal.ofReal ((4095 / 4096 : ℝ) ^ (127 / 10 * (P : ℝ) - Y)) := by
  set v : ℝ := 4095 / 4096
  have hv0 : (0 : ℝ) < v := by norm_num [v]
  set G : (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun h ↦
    ∏ i, ENNReal.ofReal (holdLaw (h i).1 (h i).2 * v ^ (h i).2)
  set c : ℝ≥0∞ := ENNReal.ofReal (v ^ (-Y))
  have hpt : ∀ h : Fin P → ℕ × ℤ, ∑ i, ((h i).2 : ℝ) ≤ Y →
      ENNReal.ofReal (holdListLaw h) ≤ c * G h := by
    intro h hY
    refine (ENNReal.ofReal_le_ofReal (holdListLaw_le_verLow h hY)).trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_prod_of_nonneg fun i _ ↦
      mul_nonneg (holdLaw_nonneg _ _) (by positivity)]
  have hG : ∑' h : {h : Fin P → ℕ × ℤ // ∀ i, 1 ≤ (h i).1}, G h.1 = holdVpgf v ^ P := by
    rw [holdVpgf_eq_tsum_natPoints, ← tsum_pi_fin_prod_ennreal_const]
    exact (Equiv.subtypePiEquivPi (α := Fin P) (p := fun _ (p : ℕ × ℤ) ↦ 1 ≤ p.1)).tsum_eq
      (fun h ↦ ∏ i, ENNReal.ofReal (holdLaw (h i).1.1 (h i).1.2 * v ^ (h i).1.2))
  calc ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).2 : ℝ) ≤ Y},
        ENNReal.ofReal (holdListLaw h.1)
      ≤ ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).2 : ℝ) ≤ Y},
          c * G h.1 := ENNReal.tsum_le_tsum fun h ↦ hpt h.1 h.2.2
    _ ≤ ∑' h : {h : Fin P → ℕ × ℤ // ∀ i, 1 ≤ (h i).1}, c * G h.1 :=
        ENNReal.tsum_mono_subtype (fun h ↦ c * G h)
          (s := {h | (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).2 : ℝ) ≤ Y})
          (t := {h | ∀ i, 1 ≤ (h i).1}) fun h hh ↦ hh.1
    _ = c * holdVpgf v ^ P := by rw [ENNReal.tsum_mul_left, hG]
    _ ≤ c * ENNReal.ofReal (v ^ (127 / 10 : ℝ)) ^ P := by
        gcongr
        exact holdVpgf_low_le_rpow_verLow
    _ = ENNReal.ofReal (v ^ (127 / 10 * (P : ℝ) - Y)) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← Real.rpow_mul_natCast hv0.le, ← Real.rpow_add hv0]
        congr 2
        ring

/-- The real series of hold-list weights over the lower vertical tail converges. -/
theorem summable_holdListLaw_verLow (P : ℕ) (Y : ℝ) :
    Summable fun h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).2 : ℝ) ≤ Y} ↦
      holdListLaw h.1 :=
  (ENNReal.summable_toReal ((tsum_holdListLaw_verLow_le P Y).trans_lt
    ENNReal.ofReal_lt_top).ne).congr fun _ ↦ ENNReal.toReal_ofReal (holdListLaw_nonneg _)

/-- **Lower vertical tail of hold lists**, real form:
`∑ η^{⊗P}(h) ≤ (4095/4096)^{(127/10) P - Y}`, the sum over `h ∈ 𝒫^P` with
`l(h_1) + ⋯ + l(h_P) ≤ Y`. -/
theorem tsum_holdListLaw_verLow_le_real (P : ℕ) (Y : ℝ) :
    ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).2 : ℝ) ≤ Y},
      holdListLaw h.1 ≤ (4095 / 4096 : ℝ) ^ (127 / 10 * (P : ℝ) - Y) := by
  have h := tsum_holdListLaw_verLow_le P Y
  rwa [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ holdListLaw_nonneg _)
    (summable_holdListLaw_verLow P Y), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h

end CollatzPosDens
