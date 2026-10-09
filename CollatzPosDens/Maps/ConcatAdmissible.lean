/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbitOdd
public import CollatzPosDens.Maps.ConcatOrbit

/-!
# Admissibility of a concatenation

Let `R` be a positive odd integer and `u, v` words. Then `u v` is admissible from `R` if and
only if `u` is admissible from `R` and `v` is admissible from `src(u, R)`; when `u` is admissible
from `R`, the source `src(u, R)` is a positive odd integer.

The terms of the inverse orbit of `u v` from `R` are those of the inverse orbit of `u` from `R`,
followed by those of the inverse orbit of `v` from `src(u, R)`, so all are integers if and only
if both lists are.

## Main results

* `CollatzPosDens.admissible_append`: `u v` is admissible from `R` iff `u` is admissible from `R`
  and `v` is admissible from `src(u, R)`.
* `CollatzPosDens.Admissible.exists_src_eq_pos_odd`: the source of a positive odd integer along
  an admissible word is a positive odd integer.

## Implementation notes

The equivalence `admissible_append` holds for every rational `R`, with no positivity or oddness
assumption, and is stated in that generality.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Before the end of `u`, the inverse orbit of `u v` is the inverse orbit of `u`. -/
lemma inverseOrbit_append_of_le_length (u v : Word) (R : ℚ) {i : ℕ} (hi : i ≤ u.length) :
    inverseOrbit (u ++ v) R i = inverseOrbit u R i := by
  rw [inverseOrbit, List.take_append_of_le_length hi, inverseOrbit]

/-- The word `u v` is admissible from `R` if and only if `u` is admissible from `R` and `v` is
admissible from `src(u, R)`. -/
@[collatz_pos_dens "lem_concat_admissible"]
theorem admissible_append {R : ℚ} {u v : Word} :
    Admissible R (u ++ v) ↔ Admissible R u ∧ Admissible (src u R) v := by
  refine ⟨fun h => ⟨fun i hi => ?_, fun i hi => ?_⟩, fun ⟨hu, hv⟩ i hi => ?_⟩
  · rw [← inverseOrbit_append_of_le_length u v R hi]
    exact h i (by simp; omega)
  · rw [← inverseOrbit_append_length_add]
    exact h _ (by simp; omega)
  · rcases le_or_gt i u.length with hiu | hiu
    · rw [inverseOrbit_append_of_le_length u v R hiu]
      exact hu i hiu
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt hiu
      rw [show u.length + j + 1 = u.length + (j + 1) by omega, inverseOrbit_append_length_add]
      exact hv _ (by simp at hi; omega)

/-- If `R` is a positive odd integer and `w` is admissible from `R`, then `src(w, R)` is a
positive odd integer. -/
@[collatz_pos_dens "lem_concat_admissible"]
theorem Admissible.exists_src_eq_pos_odd {R : ℤ} {w : Word} (hw : Admissible R w)
    (hpos : 0 < R) (hodd : Odd R) : ∃ m : ℤ, src w R = m ∧ 0 < m ∧ Odd m := by
  simpa using hw.exists_inverseOrbit_eq_pos_odd hpos hodd le_rfl

end CollatzPosDens
