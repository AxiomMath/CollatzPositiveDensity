/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Interval sums of a periodic sequence

Let `g : ℕ → ℝ` be periodic with period `L ≥ 1`, with mean `μ = (1 / L) ∑_{k < L} g k` over one
period. The centred partial sums `Q k = ∑_{j < k} (g j - μ)` are themselves `L`-periodic, since
one full period of `g - μ` sums to `0`. Hence every `Q k` lies between the minimum and the maximum
of `Q` on `{0, …, L}`, and if `D` is the difference of that maximum and minimum, then every sum of
`g` over `t` consecutive integers differs from `t μ` by at most `D`, because it equals
`t μ + Q (u + t) - Q u`.

## Main results

* `CollatzPosDens.centredPartialSum_add_period`: the centred partial sums are `L`-periodic.
* `CollatzPosDens.abs_sum_Ico_sub_le_of_periodic`: `|∑_{k = u}^{u + t - 1} g k - t μ| ≤ D`.
* `CollatzPosDens.sum_Ico_le_of_periodic`, `CollatzPosDens.sub_le_sum_Ico_of_periodic`: its two
  halves, `∑_{k = u}^{u + t - 1} g k ≤ t μ + D` and `t μ - D ≤ ∑_{k = u}^{u + t - 1} g k`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §10.1.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- If `g` is `L`-periodic and `μ` is the mean of `g` over one period, then the centred partial
sums `k ↦ ∑_{j < k} (g j - μ)` are `L`-periodic. -/
theorem centredPartialSum_add_period {L : ℕ} (hL : L ≠ 0) {g : ℕ → ℝ}
    (hg : ∀ k, g (k + L) = g k) (k : ℕ) :
    ∑ j ∈ range (k + L), (g j - (∑ i ∈ range L, g i) / L) =
      ∑ j ∈ range k, (g j - (∑ i ∈ range L, g i) / L) := by
  have hL' : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
  rw [add_comm k L, sum_range_add]
  have h0 : ∑ j ∈ range L, (g j - (∑ i ∈ range L, g i) / L) = 0 := by
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ hL', sub_self]
  rw [h0, zero_add]
  refine sum_congr rfl fun j _ => ?_
  rw [add_comm L j, hg]

/-- The centred partial sums of an `L`-periodic sequence only depend on the index modulo `L`. -/
theorem centredPartialSum_mod {L : ℕ} (hL : L ≠ 0) {g : ℕ → ℝ}
    (hg : ∀ k, g (k + L) = g k) (k : ℕ) :
    ∑ j ∈ range k, (g j - (∑ i ∈ range L, g i) / L) =
      ∑ j ∈ range (k % L), (g j - (∑ i ∈ range L, g i) / L) := by
  have key : ∀ n r : ℕ, ∑ j ∈ range (r + L * n), (g j - (∑ i ∈ range L, g i) / L) =
      ∑ j ∈ range r, (g j - (∑ i ∈ range L, g i) / L) := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      rw [Nat.mul_succ, ← add_assoc, centredPartialSum_add_period hL hg, ih]
  conv_lhs => rw [← Nat.mod_add_div k L]
  exact key _ _

/-- **Interval sums of a periodic sequence.** Let `L ≥ 1` and let `g : ℕ → ℝ` be `L`-periodic,
with mean `μ = (1 / L) ∑_{k < L} g k` over a period, and let `D` be the maximum minus the minimum
over `0 ≤ k ≤ L` of the centred partial sums `∑_{j < k} (g j - μ)`. Then every sum of `g` over
`t` consecutive integers `u, …, u + t - 1` differs from `t μ` by at most `D`. -/
@[collatz_pos_dens "lem_c3_cyc_interval"]
theorem abs_sum_Ico_sub_le_of_periodic {L : ℕ} (hL : 1 ≤ L) {g : ℕ → ℝ}
    (hg : ∀ k, g (k + L) = g k) {μ D : ℝ} (hμ : μ = (1 / L) * ∑ k ∈ range L, g k)
    (hD : D = (range (L + 1)).sup' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)) -
      (range (L + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)))
    (u t : ℕ) :
    |∑ k ∈ Ico u (u + t), g k - t * μ| ≤ D := by
  have hL0 : L ≠ 0 := by omega
  have hμ' : μ = (∑ i ∈ range L, g i) / L := by rw [hμ, one_div_mul_eq_div]
  set Q : ℕ → ℝ := fun k => ∑ j ∈ range k, (g j - μ) with hQ
  have hmod : ∀ k, Q k = Q (k % L) := by
    intro k; simp only [hQ, hμ']; exact centredPartialSum_mod hL0 hg k
  have hmem : ∀ k, k % L ∈ range (L + 1) := fun k =>
    mem_range.mpr (by have := Nat.mod_lt k (by omega : 0 < L); omega)
  have hle : ∀ k, Q k ≤ (range (L + 1)).sup' nonempty_range_add_one Q := fun k =>
    (hmod k).trans_le (le_sup' Q (hmem k))
  have hge : ∀ k, (range (L + 1)).inf' nonempty_range_add_one Q ≤ Q k := fun k =>
    (inf'_le Q (hmem k)).trans_eq (hmod k).symm
  have hsum : ∑ k ∈ Ico u (u + t), g k = t * μ + (Q (u + t) - Q u) := by
    have h1 : ∑ k ∈ Ico u (u + t), g k = ∑ k ∈ range (u + t), g k - ∑ k ∈ range u, g k := by
      rw [sum_Ico_eq_sub _ (by omega)]
    simp only [hQ, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, h1]
    push_cast; ring
  rw [hsum, hD, add_sub_cancel_left, abs_le]
  have := hle (u + t)
  have := hge u
  have := hle u
  have := hge (u + t)
  constructor <;> linarith

/-- Under the hypotheses of `abs_sum_Ico_sub_le_of_periodic`, every sum of `g` over `t`
consecutive integers is at most `t μ + D`. -/
theorem sum_Ico_le_of_periodic {L : ℕ} (hL : 1 ≤ L) {g : ℕ → ℝ} (hg : ∀ k, g (k + L) = g k)
    {μ D : ℝ} (hμ : μ = (1 / L) * ∑ k ∈ range L, g k)
    (hD : D = (range (L + 1)).sup' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)) -
      (range (L + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)))
    (u t : ℕ) :
    ∑ k ∈ Ico u (u + t), g k ≤ t * μ + D := by
  have := (abs_le.1 (abs_sum_Ico_sub_le_of_periodic hL hg hμ hD u t)).2
  linarith

/-- Under the hypotheses of `abs_sum_Ico_sub_le_of_periodic`, every sum of `g` over `t`
consecutive integers is at least `t μ - D`. -/
theorem sub_le_sum_Ico_of_periodic {L : ℕ} (hL : 1 ≤ L) {g : ℕ → ℝ} (hg : ∀ k, g (k + L) = g k)
    {μ D : ℝ} (hμ : μ = (1 / L) * ∑ k ∈ range L, g k)
    (hD : D = (range (L + 1)).sup' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)) -
      (range (L + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)))
    (u t : ℕ) :
    t * μ - D ≤ ∑ k ∈ Ico u (u + t), g k := by
  have := (abs_le.1 (abs_sum_Ico_sub_le_of_periodic hL hg hμ hD u t)).1
  linarith

end CollatzPosDens
