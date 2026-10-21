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
public import CollatzPosDens.Transfer.S02Ycl
public import CollatzPosDens.Transfer.S02Vcl
public import CollatzPosDens.StoppingTrace.TrVpgfClear
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Lower vertical tail of hold lists at the clearing point

For a Fourier index `ι ∈ 𝔍`, `P ∈ ℕ` and real `Y`, the hold-list weights `η^{⊗P}(h)` of the
hold lists `h ∈ 𝒫^P` whose total vertical displacement `l(h_1) + ⋯ + l(h_P)` is at most `Y` sum
to at most `y^{v P - Y}`, where `y = y_cl(ι) ∈ {8191/8192, 255/256}` is the clearing point and
`v = v_cl(ι) ∈ {1279/100, 25/2}` the clearing exponent.

Since `0 < y < 1`, on that range `1 ≤ y^{∑_i l(h_i) - Y}`, so the sum is at most
`y^{-Y} ∏_{i=1}^P ∑_{h_i ∈ 𝒫} η(h_i) y^{l(h_i)} = y^{-Y} 𝖵(y)^P` (Tonelli), and
`𝖵(y) < y^v` gives `𝖵(y)^P ≤ y^{v P}`.

## Main results

* `CollatzPosDens.tsum_holdListLaw_verLowClear_le`: the bound, as a sum in `[0, ∞]`.
* `CollatzPosDens.summable_holdListLaw_verLowClear`: the real series converges.
* `CollatzPosDens.tsum_holdListLaw_verLowClear_le_real`: the bound for the real series.

## Implementation notes

A point is a pair `(j, l) : ℕ × ℤ`, and `𝒫 = ℤ_{≥1} × ℤ` is the set of pairs with `1 ≤ j`; the
restriction matters, since `η(0, 0) = 1`. So `𝒫^P` is the set of tuples `h : Fin P → ℕ × ℤ` with
`1 ≤ j(h_i)` for all `i`, and the range of summation is the subtype of those tuples with moreover
`∑_i l(h_i) ≤ Y`. The principal statement is the sum in `[0, ∞]` of the terms embedded by
`ENNReal.ofReal`, which needs no summability hypothesis; the real-valued form, with its
convergence, is deduced from it. The power `y^{v P - Y}` is the real power.

## References

* [Mazur, *Collatz positive density*], §9.13.
-/

@[expose] public section

namespace CollatzPosDens

open scoped ENNReal

/-- On the lower vertical tail, `η^{⊗P}(h) ≤ y^{-Y} ∏_i η(h_i) y^{l(h_i)}` for every
`0 < y ≤ 1`. -/
private lemma holdListLaw_le_rpow_mul_prod {P : ℕ} {Y y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1)
    (h : Fin P → ℕ × ℤ) (hY : ∑ i, ((h i).2 : ℝ) ≤ Y) :
    holdListLaw h ≤ y ^ (-Y) * ∏ i, (holdLaw (h i).1 (h i).2 * y ^ (h i).2) := by
  have hl : y ^ Y ≤ ∏ i, y ^ (h i).2 := by
    calc y ^ Y ≤ y ^ (∑ i, ((h i).2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hy1 hY
      _ = ∏ i, y ^ (h i).2 := by
          rw [Real.rpow_sum_of_pos hy0]
          exact Finset.prod_congr rfl fun i _ ↦ Real.rpow_intCast y _
  have hinv : y ^ (-Y) * y ^ Y = 1 := by
    rw [← Real.rpow_add hy0]
    simp
  rw [Finset.prod_mul_distrib, holdListLaw_def]
  have h0 : 0 ≤ ∏ i, holdLaw (h i).1 (h i).2 :=
    Finset.prod_nonneg fun i _ ↦ holdLaw_nonneg _ _
  have hyY : (0 : ℝ) ≤ y ^ (-Y) := by positivity
  calc ∏ i, holdLaw (h i).1 (h i).2
      = y ^ (-Y) * y ^ Y * ∏ i, holdLaw (h i).1 (h i).2 := by rw [hinv, one_mul]
    _ ≤ y ^ (-Y) * (∏ i, y ^ (h i).2) * ∏ i, holdLaw (h i).1 (h i).2 := by gcongr
    _ = _ := by ring

/-- **Lower vertical tail of hold lists at the clearing point.** For a Fourier index `ι`,
`P ∈ ℕ` and real `Y`, in `[0, ∞]`, `∑ η^{⊗P}(h) ≤ y_cl(ι)^{v_cl(ι) P - Y}`, the sum over
`h ∈ 𝒫^P` with
`l(h_1) + ⋯ + l(h_P) ≤ Y`. Here `𝒫^P` is the set of `h : Fin P → ℕ × ℤ` with `1 ≤ j(h_i)` for
every `i`. -/
@[collatz_pos_dens "lem_tr_ver_low_clear"]
theorem tsum_holdListLaw_verLowClear_le (ι : FIndex) (P : ℕ) (Y : ℝ) :
    ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).2 : ℝ) ≤ Y},
      ENNReal.ofReal (holdListLaw h.1) ≤
        ENNReal.ofReal ((clearingPoint ι : ℝ) ^ ((clearingPower ι : ℝ) * P - Y)) := by
  set v : ℝ := (clearingPoint ι : ℝ) with hv
  have hv0 : (0 : ℝ) < v := by rw [hv]; exact_mod_cast clearingPoint_pos ι
  have hv1 : v ≤ 1 := by rw [hv]; exact_mod_cast clearingPoint_le_one ι
  set G : (Fin P → ℕ × ℤ) → ℝ≥0∞ := fun h ↦
    ∏ i, ENNReal.ofReal (holdLaw (h i).1 (h i).2 * v ^ (h i).2)
  set c : ℝ≥0∞ := ENNReal.ofReal (v ^ (-Y))
  have hpt : ∀ h : Fin P → ℕ × ℤ, ∑ i, ((h i).2 : ℝ) ≤ Y →
      ENNReal.ofReal (holdListLaw h) ≤ c * G h := by
    intro h hY
    refine (ENNReal.ofReal_le_ofReal (holdListLaw_le_rpow_mul_prod hv0 hv1 h hY)).trans_eq ?_
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
    _ ≤ c * ENNReal.ofReal (v ^ (clearingPower ι : ℝ)) ^ P := by
        gcongr
        exact (holdVpgf_clearingPoint_lt ι).le
    _ = ENNReal.ofReal (v ^ ((clearingPower ι : ℝ) * P - Y)) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← Real.rpow_mul_natCast hv0.le, ← Real.rpow_add hv0]
        congr 2
        ring

/-- The real series of hold-list weights over the lower vertical tail converges. -/
theorem summable_holdListLaw_verLowClear (P : ℕ) (Y : ℝ) :
    Summable fun h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).2 : ℝ) ≤ Y} ↦
      holdListLaw h.1 :=
  (ENNReal.summable_toReal
    ((tsum_holdListLaw_verLowClear_le .o P Y).trans_lt ENNReal.ofReal_lt_top).ne).congr fun _ ↦
    ENNReal.toReal_ofReal (holdListLaw_nonneg _)

/-- **Lower vertical tail of hold lists at the clearing point**, real form:
`∑ η^{⊗P}(h) ≤ y_cl(ι)^{v_cl(ι) P - Y}`, the sum over `h ∈ 𝒫^P` with
`l(h_1) + ⋯ + l(h_P) ≤ Y`. -/
theorem tsum_holdListLaw_verLowClear_le_real (ι : FIndex) (P : ℕ) (Y : ℝ) :
    ∑' h : {h : Fin P → ℕ × ℤ // (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).2 : ℝ) ≤ Y},
      holdListLaw h.1 ≤ (clearingPoint ι : ℝ) ^ ((clearingPower ι : ℝ) * P - Y) := by
  have h := tsum_holdListLaw_verLowClear_le ι P Y
  have hv0 : (0 : ℝ) < clearingPoint ι := by exact_mod_cast clearingPoint_pos ι
  rwa [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ holdListLaw_nonneg _)
    (summable_holdListLaw_verLowClear P Y), ENNReal.ofReal_le_ofReal_iff (by positivity)] at h

end CollatzPosDens
