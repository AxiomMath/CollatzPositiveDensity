/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbit

/-!
# Admissible words

A word `w` of length `d` is *admissible* from `R` if every term `R₀, …, R_d` of its inverse
orbit from `R` is an integer.

## Main definitions

* `CollatzPosDens.Admissible R w`: the word `w` is admissible from `R`.

## Main results

* `CollatzPosDens.admissible_iff_exists_int`: admissibility says each `R_i`, `i ≤ d`, is the
  image of an integer.
* `CollatzPosDens.Admissible.den_eq_one`, `CollatzPosDens.Admissible.den_src_eq_one`: the
  starting point and the source of an admissible word are integers.
* `CollatzPosDens.admissible_nil`: the empty word is admissible from `R` iff `R` is an integer.

## Implementation notes

The source takes `R` to be a positive odd integer. The definition makes sense for any rational
`R` (the condition at `i = 0` already forces `R` to be an integer), so it is stated for `R : ℚ`
with no oddness or positivity assumption; the lemmas that need them assume them. Integrality of
a rational `q` is expressed as `q.den = 1`, which makes `Admissible` decidable.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The word `w` is *admissible* from `R` if every term `R₀, …, R_{|w|}` of the inverse orbit
of `R` along `w` is an integer. -/
@[collatz_pos_dens "def_admissible"]
def Admissible (R : ℚ) (w : Word) : Prop :=
  ∀ i ≤ w.length, (inverseOrbit w R i).den = 1

/-- Admissibility of a word from a rational starting point is decidable. -/
instance (R : ℚ) (w : Word) : Decidable (Admissible R w) :=
  inferInstanceAs (Decidable (∀ i ≤ w.length, (inverseOrbit w R i).den = 1))

/-- Admissibility says that every term of the inverse orbit is the image of an integer. -/
lemma admissible_iff_exists_int {R : ℚ} {w : Word} :
    Admissible R w ↔ ∀ i ≤ w.length, ∃ n : ℤ, inverseOrbit w R i = n := by
  refine forall₂_congr fun i _ => ⟨fun h => ⟨_, (Rat.coe_int_num_of_den_eq_one h).symm⟩, ?_⟩
  rintro ⟨n, hn⟩
  rw [hn, Rat.den_intCast]

/-- The `i`-th term of the inverse orbit along an admissible word is an integer, `i ≤ |w|`. -/
lemma Admissible.den_inverseOrbit_eq_one {R : ℚ} {w : Word} (h : Admissible R w) {i : ℕ}
    (hi : i ≤ w.length) : (inverseOrbit w R i).den = 1 :=
  h i hi

/-- The starting point of an admissible word is an integer. -/
lemma Admissible.den_eq_one {R : ℚ} {w : Word} (h : Admissible R w) : R.den = 1 :=
  h 0 (Nat.zero_le _)

/-- The source of an admissible word is an integer. -/
lemma Admissible.den_src_eq_one {R : ℚ} {w : Word} (h : Admissible R w) : (src w R).den = 1 := by
  simpa using h w.length le_rfl

/-- The empty word is admissible from `R` if and only if `R` is an integer. -/
@[simp] lemma admissible_nil {R : ℚ} : Admissible R [] ↔ R.den = 1 := by
  simp [Admissible]

end CollatzPosDens
