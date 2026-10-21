/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.ModEq
public import CollatzPosDens.Attr

/-!
# Integers of one residue class in an interval

Let `m ≥ 1` and `c` be integers and let `α, λ` be reals with `λ ≥ 0`. The integers `t` with
`α ≤ t ≤ α + λ` and `t ≡ c (mod m)` form a finite set with at most `λ / m + 1` elements: writing
such an integer as `t = c + m s`, the integers `s` are distinct and lie in the closed interval
`[(α - c)/m, (α - c)/m + λ/m]` of length `λ / m`, which contains at most `λ / m + 1` integers.

## Main results

* `CollatzPosDens.finite_setOf_modEq_of_mem_Icc`: the set of such integers is finite.
* `CollatzPosDens.ncard_setOf_modEq_le`: it has at most `λ / m + 1` elements.
* `CollatzPosDens.ncard_setOf_modEq_pow_three_le`: the case `m = 3^n`, with the bound
  `λ 3^{-n} + 1`.

## Implementation notes

The number of integers is `Set.ncard` of the set of such integers; the set is finite
(`CollatzPosDens.finite_setOf_modEq_of_mem_Icc`), so this is its cardinality.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The integers of a closed real interval `[a, a + Λ]` with `Λ ≥ 0` number at most `Λ + 1`. -/
private theorem ncard_int_mem_Icc_le {T : Set ℤ} {a Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hT : ∀ t ∈ T, a ≤ t ∧ (t : ℝ) ≤ a + Λ) : (T.ncard : ℝ) ≤ Λ + 1 := by
  have hsub : T ⊆ (Finset.Icc ⌈a⌉ ⌊a + Λ⌋ : Set ℤ) := fun t ht => by
    simp only [Finset.coe_Icc, Set.mem_Icc, Int.ceil_le, Int.le_floor]
    exact hT t ht
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Int.card_Icc] at h1
  have h4 : (T.ncard : ℝ) ≤ (⌊a + Λ⌋ + 1 - ⌈a⌉).toNat := by exact_mod_cast h1
  have h2 : ((⌊a + Λ⌋ + 1 - ⌈a⌉).toNat : ℝ) ≤ max ((⌊a + Λ⌋ : ℝ) + 1 - ⌈a⌉) 0 := by
    have : ((⌊a + Λ⌋ + 1 - ⌈a⌉).toNat : ℤ) = max (⌊a + Λ⌋ + 1 - ⌈a⌉) 0 := Int.toNat_eq_max _
    have h : (((⌊a + Λ⌋ + 1 - ⌈a⌉).toNat : ℤ) : ℝ) = ((max (⌊a + Λ⌋ + 1 - ⌈a⌉) 0 : ℤ) : ℝ) := by
      rw [this]
    push_cast at h
    exact h.le
  have h3 : max ((⌊a + Λ⌋ : ℝ) + 1 - ⌈a⌉) 0 ≤ Λ + 1 :=
    max_le (by linarith [Int.floor_le (a + Λ), Int.le_ceil a]) (by linarith)
  linarith

/-- The integers `t` with `α ≤ t ≤ α + λ` and `t ≡ c (mod m)` form a finite set. -/
theorem finite_setOf_modEq_of_mem_Icc (m c : ℤ) (α L : ℝ) :
    {t : ℤ | α ≤ t ∧ (t : ℝ) ≤ α + L ∧ t ≡ c [ZMOD m]}.Finite := by
  refine (Finset.finite_toSet (Finset.Icc ⌈α⌉ ⌊α + L⌋)).subset fun t ht => ?_
  simp only [Finset.coe_Icc, Set.mem_Icc, Int.ceil_le, Int.le_floor]
  exact ⟨ht.1, ht.2.1⟩

/-- Let `m ≥ 1` and `c` be integers and `α, λ` reals with `λ ≥ 0`. The number of integers `t`
with `α ≤ t ≤ α + λ` and `t ≡ c (mod m)` is at most `λ / m + 1`. -/
theorem ncard_setOf_modEq_le {m : ℤ} (hm : 0 < m) (c : ℤ) {α L : ℝ} (hL : 0 ≤ L) :
    ({t : ℤ | α ≤ t ∧ (t : ℝ) ≤ α + L ∧ t ≡ c [ZMOD m]}.ncard : ℝ) ≤ L / m + 1 := by
  set s := {t : ℤ | α ≤ t ∧ (t : ℝ) ≤ α + L ∧ t ≡ c [ZMOD m]}
  set g : ℤ → ℤ := fun t => (t - c) / m
  have hg : ∀ t ∈ s, t = c + m * g t := fun t ht => by
    have hdvd : m ∣ t - c := (Int.ModEq.dvd ht.2.2.symm)
    have := Int.mul_ediv_cancel' hdvd
    simp only [g]
    linarith
  have hinj : Set.InjOn g s := fun t ht t' ht' h => by
    rw [hg t ht, hg t' ht', h]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hbd : ∀ u ∈ g '' s, (α - c) / m ≤ u ∧ (u : ℝ) ≤ (α - c) / m + L / m := by
    rintro _ ⟨t, ht, rfl⟩
    have hR : (t : ℝ) = c + m * (g t : ℝ) := by exact_mod_cast hg t ht
    obtain ⟨h1, h2, -⟩ := ht
    constructor
    · rw [div_le_iff₀ hmR]; nlinarith
    · rw [← add_div, le_div_iff₀ hmR]; nlinarith
  rw [← hinj.ncard_image]
  exact ncard_int_mem_Icc_le (div_nonneg hL hmR.le) hbd

/-- **Integers of one residue class in an interval.** Let `n ∈ ℕ`, `c ∈ ℤ`, and `α, λ` reals with
`λ ≥ 0`. The number of integers `t` with `α ≤ t ≤ α + λ` and `t ≡ c (mod 3^n)` is at most
`λ 3^{-n} + 1`. -/
@[collatz_pos_dens "lem_mx_sh_residue_count"]
theorem ncard_setOf_modEq_pow_three_le (n : ℕ) (c : ℤ) {α L : ℝ} (hL : 0 ≤ L) :
    ({t : ℤ | α ≤ t ∧ (t : ℝ) ≤ α + L ∧ t ≡ c [ZMOD 3 ^ n]}.ncard : ℝ) ≤ L * 3⁻¹ ^ n + 1 := by
  have h := ncard_setOf_modEq_le (m := 3 ^ n) (by positivity) c (α := α) hL
  push_cast at h
  rwa [inv_pow, ← div_eq_mul_inv]

end CollatzPosDens
