/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FcCover
public import CollatzPosDens.FirstCrossing.FcLowerTail
public import CollatzPosDens.FirstCrossing.FcMarginal
public import CollatzPosDens.FirstCrossing.FcMaximal
public import CollatzPosDens.Transfer.S03Log3Bounds

/-!
# Deficit of a central window

Let `u`, `K` and `w` be natural numbers with `1000 ≤ w ≤ u / 8`, and let `𝒱` be the set of
words of the first-crossing family `𝒲(u, r_u, K)` whose length lies in the central window
`u - w ≤ |v| ≤ u + w`. Then
$$1 - \mathbf p(\mathcal V) \le 2 \exp\Bigl(-\frac{2 (207 w / 500)^2}{9 (u + w)}\Bigr)
  + 2^{-(K+1)}.$$

With the shift `r_u` the barrier is `H(i) = 2u + B((i - u)₊) - B((u - i)₊)`. By the covering
bound `CollatzPosDens.one_sub_geomMass_firstCrossing_window_le`, `1 - 𝐩(𝒱)` is at most
`𝐩(E₁) + 𝐩(E₂) + 2^{-(K+1)}`, where `E₁` is the set of words crossing the barrier too early (at
a time `ℓ_u ≤ i < u - w`, which forces `A_i - 2i ≥ 207w/500`) and `E₂` the set of words still
below the barrier at time `u + w` (which forces `A_{u+w} - 2(u + w) ≤ -207w/500`). Both events
depend only on the first `u + w` letters, and each has mass at most
`exp(-2(207w/500)²/(9(u + w)))`, by the maximal inequality and the lower tail bound for
valuation sums.

## Main results

* `CollatzPosDens.one_sub_geomMass_deficitWindow_le`: the deficit bound for the central
  window.

## Implementation notes

The statement is usually posed for integers `u`, `K ≥ 0` and `w` with `1000 ≤ w ≤ u/8`; this
forces `u ≥ 0`, so all three are natural numbers here, and `w ≤ u/8` is written `8 w ≤ u`.

## References

* [Mazur, *Collatz positive density*], §15.5.
-/

@[expose] public section

open scoped ENNReal
open InformationTheory Real

namespace CollatzPosDens

/-- Crossing the barrier at a time `i < u - w` forces the deviation `A - 2i ≥ 207w/500`. -/
private lemma deficitWindow_low {u w i A : ℕ} (hw : 1000 ≤ w) (hi : i + w < u)
    (hA : barrier u (rb u) i ≤ (A : ℤ)) : (207 * w / 500 : ℝ) ≤ (A : ℝ) - 2 * i := by
  have hiu : i ≤ u := by omega
  rw [barrier_of_ge _ hiu] at hA
  have hB := ceilLog3_lt_mul_logb_add_one (u - i)
  have hl := logb_two_three_bounds.2
  have hA' : (2 * (u : ℤ) - ceilLog3 (u - i)) ≤ A := by linarith
  have hA'' : (2 * (u : ℝ) - ceilLog3 (u - i)) ≤ A := by exact_mod_cast hA'
  rw [Nat.cast_sub hiu] at hB
  have hw' : (w : ℝ) + 1 + i ≤ u := by exact_mod_cast (show w + 1 + i ≤ u by omega)
  have hw1 : (1000 : ℝ) ≤ w := by exact_mod_cast hw
  have hprod : 0 ≤ (317 / 200 - logb 2 3) * ((u : ℝ) - i) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Being below the barrier at time `u + w` forces `A - 2(u + w) ≤ -207w/500`. -/
private lemma deficitWindow_high {u w A : ℕ} (hw : 1000 ≤ w)
    (hA : (A : ℤ) < barrier u (rb u) (u + w)) :
    (A : ℝ) - 2 * ((u + w : ℕ) : ℝ) ≤ -(207 * w / 500 : ℝ) := by
  rw [barrier_of_le _ (Nat.le_add_right u w), Nat.add_sub_cancel_left] at hA
  have hB := ceilLog3_lt_mul_logb_add_one w
  have hl := logb_two_three_bounds.2
  have hA' : (A : ℤ) < 2 * (u : ℤ) + ceilLog3 w := by linarith
  have hA'' : (A : ℝ) < 2 * (u : ℝ) + ceilLog3 w := by exact_mod_cast hA'
  have hw1 : (1000 : ℝ) ≤ w := by exact_mod_cast hw
  have hprod : 0 ≤ (317 / 200 - logb 2 3) * (w : ℝ) := mul_nonneg (by linarith) (by linarith)
  push_cast
  nlinarith

/-- **Deficit of a central window.** For `1000 ≤ w ≤ u/8`, the words of the first-crossing
family `𝒲(u, r_u, K)` with length in `[u - w, u + w]` have geometric mass at least
`1 - 2 exp(-2(207w/500)²/(9(u + w))) - 2^{-(K+1)}`. -/
@[collatz_pos_dens "lem_deficit_window"]
theorem one_sub_geomMass_deficitWindow_le {u K w : ℕ} (hw : 1000 ≤ w) (hwu : 8 * w ≤ u) :
    1 - geomMass {v ∈ firstCrossing u (rb u) K | u - w ≤ v.length ∧ v.length ≤ u + w} ≤
      2 * ENNReal.ofReal (exp (-2 * (207 * w / 500 : ℝ) ^ 2 / (9 * (u + w)))) +
        2⁻¹ ^ (K + 1) := by
  have hnh : u + w ≤ hb u := by
    rw [hb_def, wb_def]
    omega
  have hlw : lb u < u - w := by
    rw [lb_def, wb_def]
    omega
  have hl1 : 1 ≤ lb u := by
    rw [lb_def, wb_def]
    omega
  set v0 : ℝ := 207 * w / 500 with hv0
  set M := {x : Word | x.length = u + w ∧
    ∃ i, 1 ≤ i ∧ i ≤ u + w ∧ v0 ≤ (Word.valSum (x.take i) : ℝ) - 2 * i}
  set L := {x : Word | x.length = u + w ∧ (x.valSum : ℝ) - 2 * ((u : ℝ) + w) ≤ -v0}
  have hcover := one_sub_geomMass_firstCrossing_window_le u (rb u) K hlw (by omega) hnh
  have hE₁ : {v : Word | v.length = hb u ∧
      ∃ i, lb u ≤ i ∧ i < u - w ∧ barrier u (rb u) i ≤ (Word.valSum (v.take i) : ℤ)} ⊆
      {v : Word | v.length = hb u ∧ v.take (u + w) ∈ M} := by
    rintro v ⟨hv, i, hi, hiw, hA⟩
    refine ⟨hv, by rw [List.length_take, hv]; omega, i, by omega, by omega, ?_⟩
    rw [List.take_take, min_eq_left (by omega)]
    exact deficitWindow_low hw (by omega) hA
  have hE₂ : {v : Word | v.length = hb u ∧
      (Word.valSum (v.take (u + w)) : ℤ) < barrier u (rb u) (u + w)} ⊆
      {v : Word | v.length = hb u ∧ v.take (u + w) ∈ L} := by
    rintro v ⟨hv, hA⟩
    refine ⟨hv, by rw [List.length_take, hv]; omega, ?_⟩
    have h := deficitWindow_high hw hA
    push_cast at h
    exact h
  have hw1 : (1000 : ℝ) ≤ w := by exact_mod_cast hw
  have hv0pos : 0 < v0 := by
    rw [hv0]
    positivity
  have htilt : 4 * v0 / (9 * ((u + w : ℕ) : ℝ)) ≤ 1 / 32 := by
    have hu8 : 8 * (w : ℝ) ≤ u := by exact_mod_cast hwu
    rw [div_le_iff₀ (by push_cast; positivity), hv0]
    push_cast
    linarith
  have hMb := fcMaximal_geomMass_le (u + w) hv0pos.le htilt
  have hLb := fcLowerTail_geomMass_le (H := u + w) (by omega) hv0pos htilt
  rw [Nat.cast_add] at hMb hLb
  calc _ ≤ _ := hcover
    _ ≤ geomMass {v : Word | v.length = hb u ∧ v.take (u + w) ∈ M} +
          geomMass {v : Word | v.length = hb u ∧ v.take (u + w) ∈ L} + 2⁻¹ ^ (K + 1) := by
        gcongr
        · exact geomMass_mono hE₁
        · exact geomMass_mono hE₂
    _ = geomMass M + geomMass L + 2⁻¹ ^ (K + 1) := by
        rw [geomMass_setOf_take_mem hnh (fun x hx => hx.1),
          geomMass_setOf_take_mem hnh (fun x hx => hx.1)]
    _ ≤ ENNReal.ofReal (exp (-2 * v0 ^ 2 / (9 * ((u : ℝ) + w)))) +
          ENNReal.ofReal (exp (-2 * v0 ^ 2 / (9 * ((u : ℝ) + w)))) + 2⁻¹ ^ (K + 1) := by
        gcongr
    _ = _ := by rw [two_mul]

end CollatzPosDens
