/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.FirstCrossingPrefixDisjoint
public import CollatzPosDens.FirstCrossing.FcComplement
public import CollatzPosDens.FirstCrossing.FcLowerTail
public import CollatzPosDens.FirstCrossing.FcMarginal
public import CollatzPosDens.FirstCrossing.FcMaximal
public import CollatzPosDens.FirstCrossing.Overshoot
public import CollatzPosDens.Transfer.Log3Bounds

/-!
# Deficit of a central window

Let `u`, `K` and `w` be natural numbers with `1000 ≤ w ≤ u / 8`, and let `V` be the set of
words of `firstCrossing u (rb u) K` whose length lies in the central window
`u - w ≤ v.length ≤ u + w`. Then
$$1 - \mathrm{geomMass}(V) \le 2 \exp\Bigl(-\frac{2 (207 w / 500)^2}{9 (u + w)}\Bigr)
  + 2^{-(K+1)}.$$

Since `V` is prefix-free with lengths at most `hb u`, `1 - geomMass V` is the mass of the set
`Y` of words of length `hb u` with no prefix in `V`. A word of `Y` either crosses
`barrier u (rb u)` too early (at a time `lb u ≤ i < u - w`, which forces the valuation sum `A`
at time `i` to satisfy `A - 2i ≥ 207w/500`), or is still below the barrier at time `u + w`
(which forces `A - 2(u + w) ≤ -207w/500`), or overshoots the barrier by more than `K` at its
first crossing. The first two events have mass at most `exp(-2(207w/500)²/(9(u + w)))` each,
by the maximal inequality and the lower tail bound for valuation sums, and the third has mass
at most `2^{-(K+1)}`.

## Main results

* `CollatzPosDens.one_sub_geomMass_deficitWindow_le`: the deficit bound for the central
  window.

## Implementation notes

The source takes integers `u`, `K ≥ 0` and `w` with `1000 ≤ w ≤ u/8`; this forces `u ≥ 0`, so
all three are natural numbers here, and `w ≤ u/8` is written `8 w ≤ u`.

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

/-- **Deficit of a central window.** For `1000 ≤ w ≤ u/8`, the words of
`firstCrossing u (rb u) K` with length in `[u - w, u + w]` have geometric mass at least
`1 - 2 exp(-2(207w/500)²/(9(u + w))) - 2^{-(K+1)}`. -/
@[collatz_pos_dens "lem_deficit_window"]
theorem one_sub_geomMass_deficitWindow_le {u K w : ℕ} (hw : 1000 ≤ w) (hwu : 8 * w ≤ u) :
    1 - geomMass {v ∈ firstCrossing u (rb u) K | u - w ≤ v.length ∧ v.length ≤ u + w} ≤
      2 * ENNReal.ofReal (exp (-2 * (207 * w / 500 : ℝ) ^ 2 / (9 * (u + w)))) +
        2⁻¹ ^ (K + 1) := by
  set V := {v ∈ firstCrossing u (rb u) K | u - w ≤ v.length ∧ v.length ≤ u + w} with hV
  set v0 : ℝ := 207 * w / 500 with hv0
  have hVsub : V ⊆ firstCrossing u (rb u) K := fun x hx => hx.1
  have hpf : IsPrefixFree V := fun x hx y hy hxy =>
    isPrefixFree_firstCrossing u (rb u) K x (hVsub hx) y (hVsub hy) hxy
  have hlen : ∀ x ∈ V, x.length ≤ hb u := fun x hx => length_le_hb_of_mem_firstCrossing hx.1
  rw [one_sub_geomMass_eq_geomMass_setOf_not_prefix_mem hpf hlen]
  have hnh : u + w ≤ hb u := by rw [hb_def, wb_def]; omega
  have hlw : lb u + w < u := by rw [lb_def, wb_def]; omega
  have hl1 : 1 ≤ lb u := by rw [lb_def, wb_def]; omega
  set M := {x : Word | x.length = u + w ∧
    ∃ i, 1 ≤ i ∧ i ≤ u + w ∧ v0 ≤ (Word.valSum (x.take i) : ℝ) - 2 * i} with hM
  set L := {x : Word | x.length = u + w ∧
    (x.valSum : ℝ) - 2 * ((u : ℝ) + w) ≤ -v0} with hL
  set O := {v : Word | v.length = hb u ∧ ∃ s, lb u < s ∧ s ≤ hb u ∧
      (∀ i, lb u ≤ i → i < s → (Word.valSum (v.take i) : ℤ) < barrier u (rb u) i) ∧
      barrier u (rb u) s + K < (Word.valSum (v.take s) : ℤ)} with hO
  have hcover : {y : Word | y.length = hb u ∧ ¬ ∃ x ∈ V, x <+: y} ⊆
      ({v : Word | v.length = hb u ∧ v.take (u + w) ∈ M} ∪
        {v : Word | v.length = hb u ∧ v.take (u + w) ∈ L}) ∪ O := by
    rintro y ⟨hy, hny⟩
    by_contra hc
    simp only [Set.mem_union, not_or] at hc
    obtain ⟨⟨hyM, hyL⟩, hyO⟩ := hc
    have hyn : (y.take (u + w)).length = u + w := by simp [hy]; omega
    have hlow : ∀ i, lb u ≤ i → i + w < u →
        (Word.valSum (y.take i) : ℤ) < barrier u (rb u) i := by
      intro i hi hiw
      by_contra hge
      push Not at hge
      refine hyM ⟨hy, hyn, i, by omega, by omega, ?_⟩
      rw [List.take_take, min_eq_left (by omega)]
      exact deficitWindow_low hw hiw hge
    have hhigh : barrier u (rb u) (u + w) ≤ (Word.valSum (y.take (u + w)) : ℤ) := by
      by_contra hlt
      push Not at hlt
      have h := deficitWindow_high hw hlt
      push_cast at h
      exact hyL ⟨hy, hyn, h⟩
    classical
    have hex : ∃ s, lb u ≤ s ∧ barrier u (rb u) s ≤ (Word.valSum (y.take s) : ℤ) :=
      ⟨u + w, by omega, hhigh⟩
    obtain ⟨hs1, hs2⟩ := Nat.find_spec hex
    have hsn : Nat.find hex ≤ u + w := Nat.find_min' hex ⟨by omega, hhigh⟩
    have hmin : ∀ i, lb u ≤ i → i < Nat.find hex →
        (Word.valSum (y.take i) : ℤ) < barrier u (rb u) i := by
      intro i hi his
      by_contra h
      push Not at h
      exact Nat.find_min hex his ⟨hi, h⟩
    have hsw : u ≤ Nat.find hex + w := by
      by_contra h
      push Not at h
      exact absurd hs2 (not_le.2 (hlow _ hs1 (by omega)))
    have hover : (Word.valSum (y.take (Nat.find hex)) : ℤ) ≤
        barrier u (rb u) (Nat.find hex) + K := by
      by_contra h
      push Not at h
      exact hyO ⟨hy, Nat.find hex, by omega, by omega, hmin, h⟩
    have hys : (y.take (Nat.find hex)).length = Nat.find hex := by
      rw [List.length_take, hy]; omega
    refine hny ⟨y.take (Nat.find hex), ⟨?_, ?_, ?_⟩, List.take_prefix _ _⟩
    · rw [mem_firstCrossing, hys]
      refine ⟨by omega, by omega, fun i hi his => ?_, hs2, hover⟩
      rw [List.take_take, min_eq_left his.le]
      exact hmin i hi his
    · rw [hys]; omega
    · rw [hys]; exact hsn
  have hv0nn : 0 ≤ v0 := by positivity
  have hv0pos : 0 < v0 := by
    have : (1000 : ℝ) ≤ w := by exact_mod_cast hw
    rw [hv0]; positivity
  have htilt : 4 * v0 / (9 * ((u + w : ℕ) : ℝ)) ≤ 1 / 32 := by
    have hw1 : (1000 : ℝ) ≤ w := by exact_mod_cast hw
    have hu8 : 8 * (w : ℝ) ≤ u := by exact_mod_cast hwu
    rw [div_le_iff₀ (by push_cast; positivity), hv0]
    push_cast
    linarith
  have hMb := fcMaximal_geomMass_le (u + w) hv0nn htilt
  have hLb := fcLowerTail_geomMass_le (H := u + w) (by omega) hv0pos htilt
  have hOb := geomMass_overshoot_le u (rb u) K
  have hexp : ((u + w : ℕ) : ℝ) = (u : ℝ) + w := by push_cast; ring
  rw [hexp] at hMb hLb
  calc geomMass {y : Word | y.length = hb u ∧ ¬ ∃ x ∈ V, x <+: y}
      ≤ geomMass (({v : Word | v.length = hb u ∧ v.take (u + w) ∈ M} ∪
          {v : Word | v.length = hb u ∧ v.take (u + w) ∈ L}) ∪ O) := geomMass_mono hcover
    _ ≤ geomMass {v : Word | v.length = hb u ∧ v.take (u + w) ∈ M} +
          geomMass {v : Word | v.length = hb u ∧ v.take (u + w) ∈ L} + geomMass O :=
        (geomMass_union_le _ _).trans (add_le_add_left (geomMass_union_le _ _) _)
    _ = geomMass M + geomMass L + geomMass O := by
        rw [geomMass_setOf_take_mem hnh (fun x hx => hx.1),
          geomMass_setOf_take_mem hnh (fun x hx => hx.1)]
    _ ≤ ENNReal.ofReal (exp (-2 * v0 ^ 2 / (9 * ((u : ℝ) + w)))) +
          ENNReal.ofReal (exp (-2 * v0 ^ 2 / (9 * ((u : ℝ) + w)))) + 2⁻¹ ^ (K + 1) := by
        gcongr
    _ = _ := by rw [two_mul]

end CollatzPosDens
