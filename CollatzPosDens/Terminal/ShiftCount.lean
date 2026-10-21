/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.FcCapSumProp
public import CollatzPosDens.Recipe.CovGen
public import CollatzPosDens.Recipe.NstarRange
public import CollatzPosDens.Recipe.TargetFloor
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.EndpointRatio
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.TerminalShift

/-!
# The number of terminal shifts

For every integer `j ≥ J_c` (the coverage generation `J_c = 23000`), every real `X` and every
odd integer `t ≥ t_min` (the target floor), the set `{u_h : h ∈ 𝓗_j(t)}` of terminal shifts has
fewer than `j^2/82` elements.

Write `σ_j = ∑_{i<j} (K_i + 3)`. By the endpoint ratio bound any two endpoints satisfy
`R_{h'} ≤ 2^{σ_j} R_h`. Since `L_{b_j}` is positive and linear in `R`, this gives
`u_h ≤ u_{h'} + σ_j` for all `h, h' ∈ 𝓗_j(t)`. Hence, if `u₀` is the least shift, every shift
lies in `[u₀, u₀ + σ_j]`, a set of `σ_j + 1` integers. Finally `σ_j + 1 < j^2/82` for
`j ≥ J_c ≥ N_*` by the cap sum `CollatzPosDens.one_add_sum_cap_add_three_lt_sq_div_82`.

## Main results

* `CollatzPosDens.terminalShift_le_add_of_le_two_pow_mul`: if `R' ≤ 2^s R` with
  `R, R' > 0`, then `u_{j,X}(R) ≤ u_{j,X}(R') + s`.
* `CollatzPosDens.historyShift_image_subset_Icc`: all shifts lie in a window
  `[u₀, u₀ + σ_j]`.
* `CollatzPosDens.encard_historyShift_image_le`: the set of shifts has at most `σ_j + 1`
  elements.
* `CollatzPosDens.ncard_historyShift_image_lt`: the set of shifts has fewer than `j^2/82`
  elements.

## Implementation notes

The paper takes the least endpoint `R_min` and the window `[u₀ - σ_j, u₀]` with
`u₀ = u_{j,X}(R_min)`. Here `u₀` is the least shift instead (a least element of a nonempty set of
natural numbers always exists), and the window is `[u₀, u₀ + σ_j]`; this avoids showing that a
least endpoint exists. The conclusion asserts that the set of shifts is finite and that its
cardinality, as a real number, is below `j^2/82`. The hypothesis `X > 0` of the paper's statement
is not needed and is dropped.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `R, R' > 0` and `R' ≤ 2^s R`, then `u_{j,X}(R) ≤ u_{j,X}(R') + s`. -/
theorem terminalShift_le_add_of_le_two_pow_mul {j s : ℕ} {X R R' : ℝ} (hR : 0 < R)
    (hR' : 0 < R') (h : R' ≤ 2 ^ s * R) :
    terminalShift j X R ≤ terminalShift j X R' + s := by
  rw [terminalShift_le_iff hR]
  have hL1 : 0 ≤ lowerScale (scale j) 1 := (lowerScale_pos _ one_pos).le
  calc X ≤ 2 ^ terminalShift j X R' * lowerScale (scale j) R' :=
        le_two_pow_terminalShift_mul j X hR'
    _ = 2 ^ terminalShift j X R' * lowerScale (scale j) 1 * R' := by
        rw [lowerScale_eq_mul]; ring
    _ ≤ 2 ^ terminalShift j X R' * lowerScale (scale j) 1 * (2 ^ s * R) := by gcongr
    _ = 2 ^ (terminalShift j X R' + s) * lowerScale (scale j) R := by
        rw [lowerScale_eq_mul _ R, pow_add]; ring

/-- For odd `t ≥ t_min` and `h, h' ∈ 𝓗_j(t)`, `u_h ≤ u_{h'} + σ_j`. -/
theorem historyShift_le_add_sum_cap {j : ℕ} (X : ℝ) {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) {h h' : Fin j → Word} (hh : h ∈ centralHistories t j)
    (hh' : h' ∈ centralHistories t j) :
    historyShift j X t h ≤ historyShift j X t h' + ∑ i ∈ Finset.range j, (cap i + 3) := by
  have hR : (0 : ℝ) < historyEndpoint (t : ℚ) h := by
    exact_mod_cast historyEndpointAt_large_endpoint_pos hodd (targetFloor_le_iff.1 ht) hh
  have hR' : (0 : ℝ) < historyEndpoint (t : ℚ) h' := by
    exact_mod_cast historyEndpointAt_large_endpoint_pos hodd (targetFloor_le_iff.1 ht) hh'
  have h2 : (historyEndpoint (t : ℚ) h' : ℝ) ≤
      2 ^ (∑ i ∈ Finset.range j, (cap i + 3)) * historyEndpoint (t : ℚ) h := by
    exact_mod_cast historyEndpoint_le_two_pow_mul hodd ht hh hh'
  exact terminalShift_le_add_of_le_two_pow_mul hR hR' h2

/-- All shifts `u_h`, `h ∈ 𝓗_j(t)`, lie in a window `[u₀, u₀ + σ_j]`. -/
theorem historyShift_image_subset_Icc (j : ℕ) (X : ℝ) {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) : ∃ u₀ : ℕ, historyShift j X t '' centralHistories t j ⊆
      Set.Icc u₀ (u₀ + ∑ i ∈ Finset.range j, (cap i + 3)) := by
  rcases (historyShift j X t '' centralHistories t j).eq_empty_or_nonempty with hS | hS
  · exact ⟨0, by simp [hS]⟩
  obtain ⟨h₀, hh₀, hu₀⟩ := Nat.sInf_mem hS
  refine ⟨sInf (historyShift j X t '' centralHistories t j), ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨Nat.sInf_le ⟨h, hh, rfl⟩, ?_⟩
  rw [← hu₀]
  exact historyShift_le_add_sum_cap X hodd ht hh hh₀

/-- The set `{u_h : h ∈ 𝓗_j(t)}` has at most `σ_j + 1` elements. -/
theorem encard_historyShift_image_le (j : ℕ) (X : ℝ) {t : ℤ} (hodd : Odd t)
    (ht : (targetFloor : ℤ) ≤ t) :
    (historyShift j X t '' centralHistories t j).encard ≤
      ((∑ i ∈ Finset.range j, (cap i + 3) + 1 : ℕ) : ℕ∞) := by
  obtain ⟨u₀, hsub⟩ := historyShift_image_subset_Icc j X hodd ht
  refine (Set.encard_le_encard hsub).trans ?_
  rw [← Finset.coe_Icc, Set.encard_coe_eq_coe_finsetCard, Nat.card_Icc]
  exact_mod_cast le_of_eq (by omega)

/-- **Number of terminal shifts.** For every integer `j ≥ J_c`, every real `X` and every odd
integer `t ≥ t_min`, the set `{u_h : h ∈ 𝓗_j(t)}` is finite with fewer than `j^2/82`
elements. -/
@[collatz_pos_dens "lem_shift_count"]
theorem ncard_historyShift_image_lt {j : ℕ} (hj : covGen ≤ j) (X : ℝ) {t : ℤ}
    (hodd : Odd t) (ht : (targetFloor : ℤ) ≤ t) :
    (historyShift j X t '' centralHistories t j).Finite ∧
      ((historyShift j X t '' centralHistories t j).ncard : ℝ) < (j : ℝ) ^ 2 / 82 := by
  have hle := encard_historyShift_image_le j X hodd ht
  have hfin : (historyShift j X t '' centralHistories t j).Finite :=
    Set.finite_of_encard_le_coe hle
  refine ⟨hfin, ?_⟩
  rw [← hfin.cast_ncard_eq] at hle
  have hle' : ((historyShift j X t '' centralHistories t j).ncard : ℝ) ≤
      1 + ∑ i ∈ Finset.range j, ((cap i : ℝ) + 3) := by
    have := ENat.natCast_le_natCast.1 hle
    have h' : ((historyShift j X t '' centralHistories t j).ncard : ℝ) ≤
        ((∑ i ∈ Finset.range j, (cap i + 3) + 1 : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h'
    linarith
  exact hle'.trans_lt
    (one_add_sum_cap_add_three_lt_sq_div_82 (selEnd_le_generationThreshold_range.2.trans hj))

end CollatzPosDens
