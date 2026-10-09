/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Terminal.UnweightedMass

/-!
# Selected pairs of level `(M, n, X)`

A *selected pair of level `(M, n, X)`* is a counted pair `(h, w)` of the unweighted terminal
mass `Υ_{n,X}(M)`: a central history `h ∈ 𝓗_n(M)` together with a word
`w ∈ 𝒲(b_n, u_h, 1)` satisfying the length condition `Λ_{b_n,u_h}(w)` and admissible from the
endpoint `R_h` of `h`, where `u_h = u_{n,X}(R_h)` is the terminal shift. Its *source* is
`src(w, R_h)`, which is an integer since `w` is admissible from `R_h`.

## Main definitions

* `CollatzPosDens.IsSelectedPair n X M h w`: `(h, w)` is a selected pair of level
  `(M, n, X)`.
* `CollatzPosDens.selectedPairSource M h w`: the source `src(w, R_h)` of `(h, w)`.

## Main results

* `CollatzPosDens.isSelectedPair_iff`: the defining conditions of a selected pair.
* `CollatzPosDens.IsSelectedPair.den_selectedPairSource_eq_one`,
  `CollatzPosDens.IsSelectedPair.exists_intCast_eq_selectedPairSource`: the source of a
  selected pair is an integer.
* `CollatzPosDens.setOf_isSelectedPair_finite`: there are finitely many selected pairs of a
  given level.

## Implementation notes

The definition needs neither that `M` be a positive odd integer nor that `X > 0`, so, as for
`Υ_{n,X}(M)`, the starting point is taken in `ℚ` and `X` is an arbitrary real. Sources are
rational numbers, as for `src`; integrality of the source of a selected pair is a lemma.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {X : ℝ} {M : ℚ}

/-- `(h, w)` is a *selected pair of level `(M, n, X)`*: a counted pair of `Υ_{n,X}(M)`. -/
@[collatz_pos_dens "def_s07_selected_pair"]
def IsSelectedPair (n : ℕ) (X : ℝ) (M : ℚ) (h : Fin n → Word) (w : Word) : Prop :=
  (h, w) ∈ unweightedMassPairs n X M

/-- The *source* `src(w, R_h)` of a pair `(h, w)`, where `R_h` is the endpoint of `h`. -/
@[collatz_pos_dens "def_s07_selected_pair"]
abbrev selectedPairSource (M : ℚ) (h : Fin n → Word) (w : Word) : ℚ :=
  src w (historyEndpoint M h)

/-- The selected pairs of level `(M, n, X)` are the counted pairs of `Υ_{n,X}(M)`. -/
theorem isSelectedPair_iff_mem_unweightedMassPairs {h : Fin n → Word} {w : Word} :
    IsSelectedPair n X M h w ↔ (h, w) ∈ unweightedMassPairs n X M :=
  Iff.rfl

/-- The defining conditions of a selected pair of level `(M, n, X)`. -/
theorem isSelectedPair_iff {h : Fin n → Word} {w : Word} :
    IsSelectedPair n X M h w ↔
      h ∈ centralHistories M n ∧ w ∈ firstCrossing (scale n) (historyShift n X M h) 1 ∧
        LengthOk (scale n) (historyShift n X M h) w ∧ Admissible (historyEndpoint M h) w :=
  mem_unweightedMassPairs

/-- The history of a selected pair is a central history. -/
theorem IsSelectedPair.mem_centralHistories {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X M h w) : h ∈ centralHistories M n :=
  (isSelectedPair_iff.1 hp).1

/-- The word of a selected pair lies in the first-crossing family `𝒲(b_n, u_h, 1)`. -/
theorem IsSelectedPair.mem_firstCrossing {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X M h w) : w ∈ firstCrossing (scale n) (historyShift n X M h) 1 :=
  (isSelectedPair_iff.1 hp).2.1

/-- The word of a selected pair satisfies the length condition `Λ_{b_n,u_h}`. -/
theorem IsSelectedPair.lengthOk {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X M h w) : LengthOk (scale n) (historyShift n X M h) w :=
  (isSelectedPair_iff.1 hp).2.2.1

/-- The word of a selected pair is admissible from the endpoint of its history. -/
theorem IsSelectedPair.admissible {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X M h w) : Admissible (historyEndpoint M h) w :=
  (isSelectedPair_iff.1 hp).2.2.2

/-- The source of a selected pair is an integer, in the form `den = 1`. -/
theorem IsSelectedPair.den_selectedPairSource_eq_one {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X M h w) : (selectedPairSource M h w).den = 1 :=
  hp.admissible.den_src_eq_one

/-- The source of a selected pair is an integer. -/
theorem IsSelectedPair.exists_intCast_eq_selectedPairSource {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X M h w) : ∃ z : ℤ, selectedPairSource M h w = z :=
  ⟨(selectedPairSource M h w).num,
    (Rat.coe_int_num_of_den_eq_one hp.den_selectedPairSource_eq_one).symm⟩

/-- There are finitely many selected pairs of level `(M, n, X)`. -/
theorem setOf_isSelectedPair_finite (n : ℕ) (X : ℝ) (M : ℚ) :
    {p : (Fin n → Word) × Word | IsSelectedPair n X M p.1 p.2}.Finite :=
  unweightedMassPairs_finite n X M

end CollatzPosDens
