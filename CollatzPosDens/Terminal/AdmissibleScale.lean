/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.LowerScale
public import CollatzPosDens.Terminal.UpperScale
public import CollatzPosDens.FirstCrossing.Scales

/-!
# Admissible external scales

Let `t` be a target. A real number `X > 0` is *admissible for generation `j`* at `t` if
`L_{b_j}(R_h) < X ≤ U_{b_j}(R_h)` for every central history `h ∈ 𝓗_j(t)`, where `R_h` is the
endpoint of `h`, `b_j` is the `j`-th scale, and `L_b`, `U_b` are the lower and upper external
scales.

## Main definitions

* `CollatzPosDens.IsAdmissibleScale t j X`: `X` is an admissible scale for generation `j`
  at the target `t`.

## Main results

* `CollatzPosDens.isAdmissibleScale_iff`: the defining condition.
* `CollatzPosDens.IsAdmissibleScale.pos`: an admissible scale is positive.
* `CollatzPosDens.IsAdmissibleScale.lowerScale_lt`: `L_{b_j}(R_h) < X` for `h ∈ 𝓗_j(t)`.
* `CollatzPosDens.IsAdmissibleScale.le_upperScale`: `X ≤ U_{b_j}(R_h)` for `h ∈ 𝓗_j(t)`.

## Implementation notes

In the source, `t` is an odd positive integer. As for `CollatzPosDens.centralHistories`, the
target `t` is here an arbitrary rational number, which is more general; the endpoint `R_h` is
then a rational number, cast to `ℝ` to be fed to the real-valued scales. A history of
generation `j` is a tuple `(w₀, …, w_{j-1})`, indexed by `Fin j`. The standing requirement
`X > 0` is made part of the predicate.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A real `X` is *admissible for generation `j`* at the target `t` if `X > 0`
and `L_{b_j}(R_h) < X ≤ U_{b_j}(R_h)` for every central history `h ∈ 𝓗_j(t)`. -/
@[collatz_pos_dens "def_admissible_scale"]
def IsAdmissibleScale (t : ℚ) (j : ℕ) (X : ℝ) : Prop :=
  0 < X ∧ ∀ h ∈ centralHistories t j,
    lowerScale (scale j) (historyEndpoint t h) < X ∧
      X ≤ upperScale (scale j) (historyEndpoint t h)

/-- The defining condition of an admissible scale. -/
theorem isAdmissibleScale_iff {t : ℚ} {j : ℕ} {X : ℝ} :
    IsAdmissibleScale t j X ↔ 0 < X ∧ ∀ h ∈ centralHistories t j,
      lowerScale (scale j) (historyEndpoint t h) < X ∧
        X ≤ upperScale (scale j) (historyEndpoint t h) :=
  Iff.rfl

namespace IsAdmissibleScale

variable {t : ℚ} {j : ℕ} {X : ℝ}

/-- An admissible scale is positive. -/
theorem pos (hX : IsAdmissibleScale t j X) : 0 < X := hX.1

/-- An admissible scale lies strictly above `L_{b_j}(R_h)` for every central history `h`. -/
theorem lowerScale_lt (hX : IsAdmissibleScale t j X) {h : Fin j → Word}
    (hh : h ∈ centralHistories t j) : lowerScale (scale j) (historyEndpoint t h) < X :=
  (hX.2 h hh).1

/-- An admissible scale lies at most at `U_{b_j}(R_h)` for every central history `h`. -/
theorem le_upperScale (hX : IsAdmissibleScale t j X) {h : Fin j → Word}
    (hh : h ∈ centralHistories t j) : X ≤ upperScale (scale j) (historyEndpoint t h) :=
  (hX.2 h hh).2

end IsAdmissibleScale

end CollatzPosDens
