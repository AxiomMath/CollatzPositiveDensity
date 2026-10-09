/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Group.Int.Even
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Ring
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbitOdd
public import CollatzPosDens.Maps.ConcatAdmissible

/-!
# An admissible word is determined by its length and source

Let `R` be a positive odd integer and let `u, u'` be words of the same length `d`, both
admissible from `R`, with `src(u, R) = src(u', R)`. Then `u = u'`.

All terms of both inverse orbits are positive odd integers. Peeling off the last letters
`a, a'` of `u, u'`, the equality of sources gives `2 ^ a R_{d-1} = 3 R_d + 1 = 2 ^ {a'} R'_{d-1}`
with `R_{d-1}, R'_{d-1}` odd, so `a = a'` (both are the `2`-adic valuation of `3 R_d + 1`) and
`R_{d-1} = R'_{d-1}`; one concludes by induction on `d`.

## Main results

* `CollatzPosDens.Admissible.eq_of_src_eq`: two admissible words from a positive odd integer
  with the same length and the same source are equal.
* `CollatzPosDens.eq_and_eq_of_two_pow_mul_eq`: the decomposition `2^a x` with `x` odd is unique.

## Implementation notes

The downward induction on the index `i` of the inverse orbit is carried out as an induction on
the word from its right end (`List.reverseRecOn`), using that a prefix of an admissible word is
admissible.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The decomposition of an integer as `2^a · x` with `x` odd is unique. -/
theorem eq_and_eq_of_two_pow_mul_eq {a a' : ℕ} {x x' : ℤ} (hx : Odd x) (hx' : Odd x')
    (h : 2 ^ a * x = 2 ^ a' * x') : a = a' ∧ x = x' := by
  wlog hle : a ≤ a' generalizing a a' x x'
  · obtain ⟨h1, h2⟩ := this hx' hx h.symm (by omega)
    exact ⟨h1.symm, h2.symm⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hx2 : x = 2 ^ k * x' := by
    have h2 : (2 : ℤ) ^ a ≠ 0 := pow_ne_zero _ two_ne_zero
    apply mul_left_cancel₀ h2
    rw [h, pow_add]; ring
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simpa using hx2
  · exfalso
    have : Even x := by
      rw [hx2]
      exact (Int.even_pow.mpr ⟨even_two, hk.ne'⟩).mul_right x'
    exact (Int.not_even_iff_odd.mpr hx) this

/-- **Words are determined by their source.** If `R` is a positive odd integer and `u, u'` are
words of the same length, both admissible from `R`, with `src(u, R) = src(u', R)`, then
`u = u'`. -/
@[collatz_pos_dens "lem_word_determined"]
theorem Admissible.eq_of_src_eq {R : ℤ} (hpos : 0 < R) (hodd : Odd R) {u u' : Word}
    (hlen : u.length = u'.length) (hu : Admissible R u) (hu' : Admissible R u')
    (hsrc : src u R = src u' R) : u = u' := by
  induction u using List.reverseRecOn generalizing u' with
  | nil => simpa [eq_comm] using hlen
  | append_singleton v a ih =>
    induction u' using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton v' a' =>
      simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen
      obtain ⟨x, hx, -, hxodd⟩ :=
        hu.exists_inverseOrbit_eq_pos_odd hpos hodd (i := v.length) (by simp)
      obtain ⟨x', hx', -, hxodd'⟩ :=
        hu'.exists_inverseOrbit_eq_pos_odd hpos hodd (i := v'.length) (by simp)
      rw [inverseOrbit, List.take_left] at hx hx'
      rw [src_concat, src_concat, hx, hx', invStep, invStep] at hsrc
      have hq : ((2 ^ (a : ℕ) * x : ℤ) : ℚ) = ((2 ^ (a' : ℕ) * x' : ℤ) : ℚ) := by
        push_cast; linarith
      obtain ⟨haa, hxx⟩ := eq_and_eq_of_two_pow_mul_eq hxodd hxodd' (by exact_mod_cast hq)
      have hv : v = v' := ih hlen (admissible_append.1 hu).1 (admissible_append.1 hu').1 (by
        rw [hx, hx', hxx])
      rw [hv, PNat.coe_inj.mp haa]

end CollatzPosDens
