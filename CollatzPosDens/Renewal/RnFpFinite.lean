/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnFpLaw
public import CollatzPosDens.Renewal.RnHoldSupport
public import Mathlib.Data.Set.Finite.List

/-!
# The first-passage law is a finite sum

Let `s` be a level and `x = (r, ℓ) ∈ ℤ × ℤ`. Only finitely many first-passage words
`h = (h_1, …, h_K)` for level `s` with `h_1 + ⋯ + h_K = x` have `η^{⊗K}(h) ≠ 0`. Indeed every
step has `j(h_i) ≥ 1`, so `K ≤ r` and `1 ≤ j(h_i) ≤ r`; and every factor `η(h_i)` is nonzero, so
`l(h_i) ≥ 2 j(h_i) + 2 ≥ 3` by the support bound for `η`, whence `3 ≤ l(h_i) ≤ ℓ`. The words
therefore range over the lists of length at most `r` with entries in the finite box
`[1, r] × [3, ℓ]`.

## Main results

* `CollatzPosDens.firstPassageLaw_finite`: the set of first-passage words for `s` with sum
  `x` and nonzero weight is finite.
* `CollatzPosDens.firstPassageLaw_finite_support`: the summand of the sum defining
  `F_s(x)` has finite support.

## Implementation notes

As in `firstPassageLaw`, a pair `(K, h)` with `K ≥ 1` and `h ∈ 𝒫^K` is a list `h` (its length is
`K`, and `K ≥ 1`, `h ∈ 𝒫^K` are part of `IsFirstPassageWord`), and the level `s` is taken in `ℤ`
rather than in `ℕ`, which is more general than a natural-number level. The finiteness holds for
every level; the first-passage condition is used only through `h ∈ 𝒫^K`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A list of points of `𝒫` of nonzero weight has length at most the sum of its first
coordinates, and its entries lie in the box `[1, r] × [3, ℓ]` where `(r, ℓ)` is its sum. -/
private lemma firstPassageLaw_finite_bounds :
    ∀ (h : List (ℤ × ℤ)), (∀ p ∈ h, p ∈ bkPoints) → firstPassageLawWeight h ≠ 0 →
      (h.length : ℤ) ≤ h.sum.1 ∧ 3 * (h.length : ℤ) ≤ h.sum.2 ∧
        ∀ p ∈ h, 1 ≤ p.1 ∧ p.1 ≤ h.sum.1 ∧ 3 ≤ p.2 ∧ p.2 ≤ h.sum.2
  | [], _, _ => by simp
  | p :: t, hP, hw => by
    rw [firstPassageLawWeight_cons] at hw
    have hp1 : 1 ≤ p.1 := hP p List.mem_cons_self
    have hsupp := two_mul_add_two_le_of_holdLaw_ne_zero (by omega) (left_ne_zero_of_mul hw)
    obtain ⟨ih1, ih2, ih3⟩ := firstPassageLaw_finite_bounds t
      (fun q hq => hP q (List.mem_cons_of_mem _ hq)) (right_ne_zero_of_mul hw)
    simp only [List.length_cons, List.sum_cons, Prod.fst_add, Prod.snd_add, List.mem_cons,
      forall_eq_or_imp]
    refine ⟨by push_cast; omega, by push_cast; omega, ⟨hp1, by omega, by omega, by omega⟩,
      fun q hq => ?_⟩
    obtain ⟨_, _, _, _⟩ := ih3 q hq
    omega

/-- **The first-passage law is a finite sum.** For a level `s` and `x ∈ ℤ × ℤ`, only finitely
many first-passage words `h = (h_1, …, h_K)` for level `s` with `h_1 + ⋯ + h_K = x` have
`η^{⊗K}(h) ≠ 0`. -/
@[collatz_pos_dens "lem_rn_fp_finite"]
theorem firstPassageLaw_finite (s : ℤ) (x : ℤ × ℤ) :
    {h : List (ℤ × ℤ) | IsFirstPassageWord s h ∧ h.sum = x ∧
      firstPassageLawWeight h ≠ 0}.Finite := by
  let B : Finset (ℤ × ℤ) := Finset.Icc 1 x.1 ×ˢ Finset.Icc 3 x.2
  refine ((List.finite_length_le (α := B) (n := x.1.toNat)).image
    (List.map Subtype.val)).subset ?_
  rintro h ⟨hfp, hsum, hw⟩
  obtain ⟨hlen, -, hbox⟩ := firstPassageLaw_finite_bounds h (fun _ hp => hfp.mem_bkPoints hp) hw
  rw [hsum] at hlen hbox
  have hB : ∀ p ∈ h, p ∈ B := fun p hp => by
    obtain ⟨_, _, _, _⟩ := hbox p hp
    simp only [B, Finset.mem_product, Finset.mem_Icc]
    omega
  lift h to List B using hB
  exact ⟨h, by simp only [Set.mem_ofPred_eq, List.length_map] at hlen ⊢; omega, rfl⟩

/-- The summand of the sum defining the first-passage law `F_s(x)` has finite support. -/
theorem firstPassageLaw_finite_support (s : ℤ) (x : ℤ × ℤ) :
    (Function.support fun h : {h : List (ℤ × ℤ) // IsFirstPassageWord s h ∧ h.sum = x} ↦
      firstPassageLawWeight h.1).Finite :=
  ((firstPassageLaw_finite s x).preimage Subtype.val_injective.injOn).subset
    fun h hh ↦ ⟨h.2.1, h.2.2, hh⟩

end CollatzPosDens
