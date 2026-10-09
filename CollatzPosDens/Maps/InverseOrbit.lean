/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Word

/-!
# Inverse orbits

For a rational `R` and a word `w = (a₁, …, a_d)`, the *inverse orbit* of `R` along `w` is the
sequence of rationals `R₀, …, R_d` with `R₀ = R` and `R_i = (2 ^ {a_i} R_{i-1} - 1) / 3` for
`1 ≤ i ≤ d`. Its last term `R_d` is the *source* `src(w, R)`.

## Main definitions

* `CollatzPosDens.invStep a R`: one inverse step `(2 ^ a R - 1) / 3`.
* `CollatzPosDens.src w R`: the source `src(w, R) = R_d`.
* `CollatzPosDens.inverseOrbit w R i`: the term `R_i` of the inverse orbit.

## Main results

* `CollatzPosDens.inverseOrbit_zero`, `CollatzPosDens.inverseOrbit_succ`: the defining
  recursion `R₀ = R`, `R_i = (2 ^ {a_i} R_{i-1} - 1) / 3`.
* `CollatzPosDens.inverseOrbit_length`: `R_d = src(w, R)`.
* `CollatzPosDens.src_append`: `src(u v, R) = src(v, src(u, R))`.

## Implementation notes

The source is a left fold of `invStep` over the word, and `R_i` is the source of the prefix
`w_{≤ i} = w.take i`. The exponent of `invStep` is a natural number, which covers the positive
letters of a word. For `i > |w|` the term `inverseOrbit w R i` equals `src(w, R)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- One inverse Syracuse step with exponent `a`: `R ↦ (2 ^ a R - 1) / 3`. -/
@[collatz_pos_dens "def_inverse_orbit"]
def invStep (a : ℕ) (R : ℚ) : ℚ := (2 ^ a * R - 1) / 3

/-- The source `src(w, R) = R_d` of the inverse orbit of `R` along `w = (a₁, …, a_d)`. -/
@[collatz_pos_dens "def_inverse_orbit"]
def src (w : Word) (R : ℚ) : ℚ := w.foldl (fun R (a : ℕ+) => invStep a R) R

/-- The term `R_i` of the inverse orbit of `R` along `w`: the source of the prefix `w_{≤ i}`. -/
@[collatz_pos_dens "def_inverse_orbit"]
def inverseOrbit (w : Word) (R : ℚ) (i : ℕ) : ℚ := src (w.take i) R

/-- The source along the empty word is the starting point. -/
@[simp] lemma src_nil (R : ℚ) : src [] R = R := rfl

/-- The first letter of the word is the first inverse step. -/
@[simp] lemma src_cons (a : ℕ+) (w : Word) (R : ℚ) :
    src (a :: w) R = src w (invStep a R) := rfl

/-- Appending one letter to the word applies one more inverse step. -/
@[simp] lemma src_concat (w : Word) (a : ℕ+) (R : ℚ) :
    src (w ++ [a]) R = invStep a (src w R) := by
  simp [src]

/-- The source along a concatenation: `src(u v, R) = src(v, src(u, R))`. -/
@[collatz_pos_dens "lem_src_concat"]
theorem src_append (u v : Word) (R : ℚ) : src (u ++ v) R = src v (src u R) := by
  simp [src, List.foldl_append]

/-- The inverse orbit starts at `R₀ = R`. -/
@[simp] lemma inverseOrbit_zero (w : Word) (R : ℚ) : inverseOrbit w R 0 = R := rfl

/-- The recursion `R_{i+1} = (2 ^ {a_{i+1}} R_i - 1) / 3` of the inverse orbit. -/
lemma inverseOrbit_succ (w : Word) (R : ℚ) {i : ℕ} (hi : i < w.length) :
    inverseOrbit w R (i + 1) = invStep w[i] (inverseOrbit w R i) := by
  rw [inverseOrbit, List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some,
    src_concat, inverseOrbit]

/-- The last term of the inverse orbit is the source. -/
@[simp] lemma inverseOrbit_length (w : Word) (R : ℚ) :
    inverseOrbit w R w.length = src w R := by
  simp [inverseOrbit]

end CollatzPosDens
