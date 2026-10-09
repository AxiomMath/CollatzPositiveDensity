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

A real number `X > 0` is *admissible for generation `n`* from the seed `M` if
`L_{b_n}(R_h) < X ≤ U_{b_n}(R_h)` for every central history `h ∈ 𝓗_n(M)`, where `R_h` is the
endpoint of `h`, `b_n` is the `n`-th scale, and `L_b`, `U_b` are the lower and upper external
scales.

## Main definitions

* `CollatzPosDens.IsAdmissibleScale M n X`: `X` is an admissible scale for generation `n`
  from `M`.

## Main results

* `CollatzPosDens.isAdmissibleScale_iff`: the defining condition.
* `CollatzPosDens.IsAdmissibleScale.pos`: an admissible scale is positive.
* `CollatzPosDens.IsAdmissibleScale.lowerScale_lt`: `L_{b_n}(R_h) < X` for `h ∈ 𝓗_n(M)`.
* `CollatzPosDens.IsAdmissibleScale.le_upperScale`: `X ≤ U_{b_n}(R_h)` for `h ∈ 𝓗_n(M)`.

## Implementation notes

As for `CollatzPosDens.centralHistories`, the seed `M` is taken in `ℚ`; the endpoint `R_h`
is then a rational number, cast to `ℝ` to be fed to the real-valued scales. The standing
requirement `X > 0` is made part of the predicate.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- A real `X` is *admissible for generation `n`* from the seed `M` if `X > 0` and
`L_{b_n}(R_h) < X ≤ U_{b_n}(R_h)` for every central history `h ∈ 𝓗_n(M)`. -/
@[collatz_pos_dens "def_admissible_scale"]
def IsAdmissibleScale (M : ℚ) (n : ℕ) (X : ℝ) : Prop :=
  0 < X ∧ ∀ h ∈ centralHistories M n,
    lowerScale (scale n) (historyEndpoint M h) < X ∧
      X ≤ upperScale (scale n) (historyEndpoint M h)

/-- The defining condition of an admissible scale. -/
theorem isAdmissibleScale_iff {M : ℚ} {n : ℕ} {X : ℝ} :
    IsAdmissibleScale M n X ↔ 0 < X ∧ ∀ h ∈ centralHistories M n,
      lowerScale (scale n) (historyEndpoint M h) < X ∧
        X ≤ upperScale (scale n) (historyEndpoint M h) :=
  Iff.rfl

namespace IsAdmissibleScale

variable {M : ℚ} {n : ℕ} {X : ℝ}

/-- An admissible scale is positive. -/
theorem pos (hX : IsAdmissibleScale M n X) : 0 < X := hX.1

/-- An admissible scale lies strictly above `L_{b_n}(R_h)` for every central history `h`. -/
theorem lowerScale_lt (hX : IsAdmissibleScale M n X) {h : Fin n → Word}
    (hh : h ∈ centralHistories M n) : lowerScale (scale n) (historyEndpoint M h) < X :=
  (hX.2 h hh).1

/-- An admissible scale lies at most at `U_{b_n}(R_h)` for every central history `h`. -/
theorem le_upperScale (hX : IsAdmissibleScale M n X) {h : Fin n → Word}
    (hh : h ∈ centralHistories M n) : X ≤ upperScale (scale n) (historyEndpoint M h) :=
  (hX.2 h hh).2

end IsAdmissibleScale

end CollatzPosDens
