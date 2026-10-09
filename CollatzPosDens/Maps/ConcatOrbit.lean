/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbit

/-!
# Inverse orbits along a concatenation

Let `R ∈ ℚ`, `u, v` words and `d = |u|`. If `(R_i)` is the inverse orbit of `u v` from `R` and
`(R'_i)` the inverse orbit of `v` from `src(u, R)`, then `R_{d+i} = R'_i` for `0 ≤ i ≤ |v|`.

## Main results

* `CollatzPosDens.inverseOrbit_append_length_add`: `R_{|u| + i} = R'_i`.

## Implementation notes

The statement is proved for every `i`, not only `i ≤ |v|`: past the end of the word both
inverse orbits are constant, equal to `src(u v, R) = src(v, src(u, R))`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The inverse orbit of `u v` from `R`, shifted by `|u|`, is the inverse orbit of `v` from
`src(u, R)`: `R_{|u| + i} = R'_i`. -/
@[collatz_pos_dens "lem_s01_concat_orbit"]
theorem inverseOrbit_append_length_add (u v : Word) (R : ℚ) (i : ℕ) :
    inverseOrbit (u ++ v) R (u.length + i) = inverseOrbit v (src u R) i := by
  simp only [inverseOrbit, List.take_length_add_append, src, List.foldl_append]

end CollatzPosDens
