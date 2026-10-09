/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnGreen
public import CollatzPosDens.Renewal.RnHoldSupport
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Defs

/-!
# The Green's function is a finite sum

For `(j, s) ∈ ℤ × ℤ`, only finitely many pairs `(N, h)` with `N ∈ ℕ`, `h ∈ 𝒫^N` and
`h_1 + ⋯ + h_N = (j, s)` have `η^{⊗N}(h) ≠ 0`. Indeed every step has `j(h_i) ≥ 1`, so
`N ≤ j` and `1 ≤ j(h_i) ≤ j`; and `η(h_i) ≠ 0` forces `l(h_i) ≥ 2 j(h_i) + 2 ≥ 4` by
`two_mul_add_two_le_of_holdLaw_ne_zero`, so `4 ≤ l(h_i) ≤ s`. The pairs therefore have bounded
length and entries in a finite box.

## Main results

* `CollatzPosDens.green_finite`: the set of such pairs `(N, h)` is finite.
* `CollatzPosDens.green_finite_length_le`: such a pair has `N ≤ j`.
* `CollatzPosDens.green_finite_support`: for each `N`, the summand of the inner sum of
  `green j s` has finite support.
* `CollatzPosDens.green_finite_support_outer`: the outer summand of `green j s` vanishes
  for `N > j`, so it has finite support.

## Implementation notes

A pair `(N, h)` is a point of the sigma type `Σ N : ℕ, Fin N → ℕ × ℤ`, and `h ∈ 𝒫^N` is the
condition that every first coordinate is at least `1`; the constraint `h_1 + ⋯ + h_N = (j, s)`
is stated coordinatewise with first coordinates summed in `ℤ`, exactly as in `green`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A nonzero hold-list weight has every factor nonzero. -/
private lemma holdLaw_ne_zero_of_holdListLaw_ne_zero {N : ℕ} {h : Fin N → ℕ × ℤ}
    (hne : holdListLaw h ≠ 0) (i : Fin N) : holdLaw (h i).1 (h i).2 ≠ 0 :=
  (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)

/-- A hold list in `𝒫^N` with first coordinates summing to `j` has length `N ≤ j`. -/
theorem green_finite_length_le {N : ℕ} {h : Fin N → ℕ × ℤ} {j : ℤ}
    (hP : ∀ i, 1 ≤ (h i).1) (hj : ∑ i, ((h i).1 : ℤ) = j) : (N : ℤ) ≤ j := by
  rw [← hj]
  calc (N : ℤ) = ∑ _i : Fin N, (1 : ℤ) := by simp
    _ ≤ ∑ i, ((h i).1 : ℤ) := Finset.sum_le_sum fun i _ ↦ by exact_mod_cast hP i

/-- Every step of such a list lies in the box `[1, j] × [4, s]`. -/
private lemma green_finite_mem_box {N : ℕ} {h : Fin N → ℕ × ℤ} {j s : ℤ}
    (hP : ∀ i, 1 ≤ (h i).1) (hj : ∑ i, ((h i).1 : ℤ) = j) (hs : ∑ i, (h i).2 = s)
    (hne : holdListLaw h ≠ 0) (i : Fin N) :
    1 ≤ (h i).1 ∧ ((h i).1 : ℤ) ≤ j ∧ 4 ≤ (h i).2 ∧ (h i).2 ≤ s := by
  have hl : ∀ k, 4 ≤ (h k).2 := fun k ↦ by
    have := two_mul_add_two_le_of_holdLaw_ne_zero (hP k)
      (holdLaw_ne_zero_of_holdListLaw_ne_zero hne k)
    have := hP k
    omega
  refine ⟨hP i, ?_, hl i, ?_⟩
  · rw [← hj]
    exact Finset.single_le_sum (f := fun k ↦ ((h k).1 : ℤ)) (fun k _ ↦ by positivity)
      (Finset.mem_univ i)
  · rw [← hs]
    exact Finset.single_le_sum (f := fun k ↦ (h k).2) (fun k _ ↦ by linarith [hl k])
      (Finset.mem_univ i)

/-- **The Green's function is a finite sum.** For `(j, s) ∈ ℤ × ℤ`, only finitely many pairs
`(N, h)` with `N ∈ ℕ`, `h ∈ 𝒫^N` and `h_1 + ⋯ + h_N = (j, s)` have `η^{⊗N}(h) ≠ 0`. -/
@[collatz_pos_dens "lem_rn_green_finite"]
theorem green_finite (j s : ℤ) :
    {x : Σ N : ℕ, Fin N → ℕ × ℤ | (∀ i, 1 ≤ (x.2 i).1) ∧ ∑ i, ((x.2 i).1 : ℤ) = j ∧
      ∑ i, (x.2 i).2 = s ∧ holdListLaw x.2 ≠ 0}.Finite := by
  let B : Set (ℕ × ℤ) := ↑(Finset.Icc 1 j.toNat ×ˢ Finset.Icc 4 s)
  have hB : B.Finite := Finset.finite_toSet _
  refine (Set.Finite.biUnion (Set.finite_Iic j.toNat) fun N _ ↦
    ((Set.Finite.pi (t := fun _ : Fin N ↦ B) fun _ ↦ hB).image (Sigma.mk N))).subset ?_
  rintro ⟨N, h⟩ ⟨hP, hj, hs, hne⟩
  dsimp only at hP hj hs hne
  simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_image, Set.mem_pi, Set.mem_univ, true_implies]
  refine ⟨N, by have := green_finite_length_le hP hj; omega, h, fun i ↦ ?_, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := green_finite_mem_box hP hj hs hne i
  simp only [B, Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc]
  omega

/-- For each length `N`, the summand of the inner sum of `green j s` has finite support. -/
theorem green_finite_support (j s : ℤ) (N : ℕ) :
    (Function.support fun h : {h : Fin N → ℕ × ℤ //
      (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s} ↦
        holdListLaw h.1).Finite := by
  refine ((green_finite j s).preimage
    (f := fun h : {h : Fin N → ℕ × ℤ //
      (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s} ↦
        (⟨N, h.1⟩ : Σ N : ℕ, Fin N → ℕ × ℤ)) ?_).subset ?_
  · intro a _ b _ hab
    exact Subtype.ext (eq_of_heq (Sigma.mk.inj hab).2)
  · intro h hh
    exact ⟨h.2.1, h.2.2.1, h.2.2.2, hh⟩

/-- The outer summand of `green j s` vanishes for `N > j`. -/
theorem green_finite_tsum_eq_zero {j s : ℤ} {N : ℕ} (hN : j < N) :
    ∑' h : {h : Fin N → ℕ × ℤ //
      (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s},
        holdListLaw h.1 = 0 := by
  have : IsEmpty {h : Fin N → ℕ × ℤ //
      (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s} :=
    ⟨fun h ↦ by have := green_finite_length_le h.2.1 h.2.2.1; omega⟩
  exact tsum_empty

/-- The outer summand of `green j s` has finite support. -/
theorem green_finite_support_outer (j s : ℤ) :
    (Function.support fun N : ℕ ↦ ∑' h : {h : Fin N → ℕ × ℤ //
      (∀ i, 1 ≤ (h i).1) ∧ ∑ i, ((h i).1 : ℤ) = j ∧ ∑ i, (h i).2 = s},
        holdListLaw h.1).Finite :=
  (Set.finite_Iic j.toNat).subset fun N hN ↦ by
    by_contra hle
    simp only [Set.mem_Iic, not_le] at hle
    exact hN (green_finite_tsum_eq_zero (by omega))

end CollatzPosDens
