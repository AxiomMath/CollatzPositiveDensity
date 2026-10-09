/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.EndpointLarge
public import CollatzPosDens.Seed.EndpointRatio
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.TerminalShift

/-!
# The number of terminal shifts

For every integer `n ≥ 10000`, every real `X` and every odd integer `M ≥ 16^{b₀}`, the set
`{u_h : h ∈ 𝓗_n(M)}` of terminal shifts has fewer than `n^2/56` elements.

Write `σ_n = ∑_{j<n} (K_j + 3)`. By the endpoint ratio bound any two endpoints satisfy
`R_{h'} ≤ 2^{σ_n} R_h`. Since `L_{b_n}` is linear in `R`, this gives `u_h ≤ u_{h'} + σ_n` for
all `h, h' ∈ 𝓗_n(M)`. Hence, if `u₀` is the least shift, every shift lies in
`[u₀, u₀ + σ_n]`, a set of `σ_n + 1` integers. Finally
`σ_n + 1 ≤ 19 n + n(n-1)/64 + 1 < n^2/56` for `n ≥ 10000`.

## Main results

* `CollatzPosDens.terminalShift_le_add_of_le_two_pow_mul`: if `R' ≤ 2^s R` with
  `R, R' > 0`, then `u_{n,X}(R) ≤ u_{n,X}(R') + s`.
* `CollatzPosDens.historyShift_image_subset_Icc`: all shifts lie in a window
  `[u₀, u₀ + σ_n]`.
* `CollatzPosDens.encard_historyShift_image_le`: the set of shifts has at most `σ_n + 1`
  elements.
* `CollatzPosDens.ncard_historyShift_image_lt`: for `n ≥ 10000` the set of shifts is finite
  with fewer than `n^2/56` elements.

## Implementation notes

The source takes the least endpoint `R_min` and the window `[u₀ - σ_n, u₀]` with
`u₀ = u_{n,X}(R_min)`. Here `u₀` is the least shift instead (a least element of a nonempty set
of natural numbers always exists), and the window is `[u₀, u₀ + σ_n]`; this avoids showing that
a least endpoint exists. The conclusion asserts that the set of shifts is finite and that its
cardinality, as a real number, is below `n^2/56`. The hypothesis `X > 0` of the source is not
needed and is dropped.

## References

* [Mazur, *Collatz positive density*], §18.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `R, R' > 0` and `R' ≤ 2^s R`, then `u_{n,X}(R) ≤ u_{n,X}(R') + s`. -/
theorem terminalShift_le_add_of_le_two_pow_mul {n s : ℕ} {X R R' : ℝ} (hR : 0 < R)
    (hR' : 0 < R') (h : R' ≤ 2 ^ s * R) :
    terminalShift n X R ≤ terminalShift n X R' + s := by
  rw [terminalShift_le_iff hR]
  have hL1 : 0 ≤ lowerScale (scale n) 1 := (lowerScale_pos _ one_pos).le
  calc X ≤ 2 ^ terminalShift n X R' * lowerScale (scale n) R' :=
        le_two_pow_terminalShift_mul n X hR'
    _ = 2 ^ terminalShift n X R' * lowerScale (scale n) 1 * R' := by
        rw [lowerScale_eq_mul]; ring
    _ ≤ 2 ^ terminalShift n X R' * lowerScale (scale n) 1 * (2 ^ s * R) := by gcongr
    _ = 2 ^ (terminalShift n X R' + s) * lowerScale (scale n) R := by
        rw [lowerScale_eq_mul _ R, pow_add]; ring

/-- For odd `M ≥ 16^{b₀}` and `h, h' ∈ 𝓗_n(M)`, `u_h ≤ u_{h'} + σ_n`. -/
theorem historyShift_le_add_sum_cap {n : ℕ} (X : ℝ) {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) {h h' : Fin n → Word} (hh : h ∈ centralHistories M n)
    (hh' : h' ∈ centralHistories M n) :
    historyShift n X M h ≤ historyShift n X M h' + ∑ j ∈ Finset.range n, (cap j + 3) := by
  have hR : (0 : ℝ) < historyEndpoint M h := by
    exact_mod_cast historyEndpointAt_large_endpoint_pos hodd hM hh
  have hR' : (0 : ℝ) < historyEndpoint M h' := by
    exact_mod_cast historyEndpointAt_large_endpoint_pos hodd hM hh'
  have h2 : (historyEndpoint M h' : ℝ) ≤
      2 ^ (∑ j ∈ Finset.range n, (cap j + 3)) * historyEndpoint M h := by
    exact_mod_cast historyEndpoint_le_two_pow_mul hodd hM hh hh'
  exact terminalShift_le_add_of_le_two_pow_mul hR hR' h2

/-- All shifts `u_h`, `h ∈ 𝓗_n(M)`, lie in a window `[u₀, u₀ + σ_n]`. -/
theorem historyShift_image_subset_Icc (n : ℕ) (X : ℝ) {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) : ∃ u₀ : ℕ, historyShift n X M '' centralHistories M n ⊆
      Set.Icc u₀ (u₀ + ∑ j ∈ Finset.range n, (cap j + 3)) := by
  rcases (historyShift n X M '' centralHistories M n).eq_empty_or_nonempty with hS | hS
  · exact ⟨0, by simp [hS]⟩
  obtain ⟨h₀, hh₀, hu₀⟩ := Nat.sInf_mem hS
  refine ⟨sInf (historyShift n X M '' centralHistories M n), ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  refine ⟨Nat.sInf_le ⟨h, hh, rfl⟩, ?_⟩
  rw [← hu₀]
  exact historyShift_le_add_sum_cap X hodd hM hh hh₀

/-- The set `{u_h : h ∈ 𝓗_n(M)}` has at most `σ_n + 1` elements. -/
theorem encard_historyShift_image_le (n : ℕ) (X : ℝ) {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) :
    (historyShift n X M '' centralHistories M n).encard ≤
      ((∑ j ∈ Finset.range n, (cap j + 3) + 1 : ℕ) : ℕ∞) := by
  obtain ⟨u₀, hsub⟩ := historyShift_image_subset_Icc n X hodd hM
  refine (Set.encard_le_encard hsub).trans ?_
  rw [← Finset.coe_Icc, Set.encard_coe_eq_coe_finsetCard, Nat.card_Icc]
  exact_mod_cast le_of_eq (by omega)

/-- `56 (σ_n + 1) < n^2` for `n ≥ 10000`. -/
theorem ncard_historyShift_image_lt_aux {n : ℕ} (hn : 10000 ≤ n) :
    56 * (∑ j ∈ Finset.range n, (cap j + 3) + 1) < n ^ 2 := by
  have h1 : ∑ j ∈ Finset.range n, (cap j + 3) =
      19 * n + ∑ j ∈ Finset.range n, j / 32 := by
    simp only [cap, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul]
    ring
  have h2 : 32 * ∑ j ∈ Finset.range n, j / 32 ≤ ∑ j ∈ Finset.range n, j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => Nat.mul_div_le j 32
  have h3 := Finset.sum_range_id_mul_two n
  have h4 : n * (n - 1) + n = n * n := by
    rcases n with _ | n
    · simp
    · simp only [Nat.add_sub_cancel]; ring
  rw [h1]
  nlinarith

/-- **Number of terminal shifts.** For every integer `n ≥ 10000`, every real `X` and every odd
integer `M ≥ 16^{b₀}`, the set `{u_h : h ∈ 𝓗_n(M)}` is finite with fewer than `n^2/56`
elements. -/
@[collatz_pos_dens "lem_shift_count"]
theorem ncard_historyShift_image_lt {n : ℕ} (hn : 10000 ≤ n) (X : ℝ) {M : ℤ} (hodd : Odd M)
    (hM : 16 ^ scale 0 ≤ M) :
    (historyShift n X M '' centralHistories M n).Finite ∧
      ((historyShift n X M '' centralHistories M n).ncard : ℝ) < (n : ℝ) ^ 2 / 56 := by
  have hle := encard_historyShift_image_le n X hodd hM
  have hfin : (historyShift n X M '' centralHistories M n).Finite :=
    Set.finite_of_encard_le_coe hle
  refine ⟨hfin, ?_⟩
  rw [← hfin.cast_ncard_eq] at hle
  have hle' := ENat.natCast_le_natCast.1 hle
  have := ncard_historyShift_image_lt_aux hn
  rw [lt_div_iff₀ (by norm_num)]
  have h5 : (historyShift n X M '' centralHistories M n).ncard * 56 < n ^ 2 := by omega
  exact_mod_cast h5

end CollatzPosDens
