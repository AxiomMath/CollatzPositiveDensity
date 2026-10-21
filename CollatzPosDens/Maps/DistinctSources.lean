/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.OrbitHitsSeedOnce
public import CollatzPosDens.Maps.WordDetermined

/-!
# Distinct admissible words have distinct sources

Let `R` be a positive odd integer that is not Syracuse-periodic. If the words `u, u'` are both
admissible from `R` and `src(u, R) = src(u', R)`, then `u = u'`.

The common source `x` is a positive odd integer with `S^{|u|}(x) = R = S^{|u'|}(x)`, since the
Syracuse map undoes each inverse step. As `R` is not Syracuse-periodic, the orbit of `x` hits `R`
only once, so `|u| = |u'|`; an admissible word is determined by its length and its source.

## Main results

* `CollatzPosDens.Admissible.eq_of_src_eq_of_not_syrPeriodic`: two words admissible from a
  positive odd non-periodic integer with the same source are equal.

## Implementation notes

The seed is a natural number `R : ℕ`, as `SyrPeriodic` is a predicate on `ℕ`; the words are
admissible from its cast `(R : ℤ)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **Distinct sources.** Let `R` be a positive odd integer that is not Syracuse-periodic. If the
words `u, u'` are both admissible from `R` and `src(u, R) = src(u', R)`, then `u = u'`. -/
@[collatz_pos_dens "lem_distinct_sources"]
theorem Admissible.eq_of_src_eq_of_not_syrPeriodic {R : ℕ} (hpos : 0 < R) (hodd : Odd R)
    (hper : ¬ SyrPeriodic R) {u u' : Word} (hu : Admissible (R : ℤ) u)
    (hu' : Admissible (R : ℤ) u') (hsrc : src u (R : ℤ) = src u' (R : ℤ)) : u = u' :=
  eq_of_src_eq (by exact_mod_cast hpos) (by exact_mod_cast hodd)
    (length_eq_of_src_eq hpos hodd hper hu hu' hsrc) hu hu' hsrc

end CollatzPosDens
