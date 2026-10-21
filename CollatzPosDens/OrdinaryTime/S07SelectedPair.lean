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
# Selected pairs of level `(t, n, X)`

A *selected pair of level `(t, n, X)`* is a counted pair `(h, w)` of the unweighted terminal
mass `unweightedMass n X t`, that is, a member of `unweightedMassPairs n X t`: a central history
`h ∈ centralHistories t n` together with a word `w ∈ firstCrossing (scale n) u 1`, where
`u = historyShift n X t h` is the terminal shift, such that `LengthOk (scale n) u w` holds and
`w` is admissible from the endpoint `historyEndpoint t h` of `h`. Its *source* is
`src w (historyEndpoint t h)`, which is an integer since `w` is admissible from the endpoint.

## Main definitions

* `CollatzPosDens.IsSelectedPair n X t h w`: `(h, w)` is a selected pair of level
  `(t, n, X)`.
* `CollatzPosDens.selectedPairSource t h w`: the source `src w (historyEndpoint t h)` of
  `(h, w)`.

## Main results

* `CollatzPosDens.isSelectedPair_iff`: the defining conditions of a selected pair.
* `CollatzPosDens.IsSelectedPair.den_selectedPairSource_eq_one`,
  `CollatzPosDens.IsSelectedPair.exists_intCast_eq_selectedPairSource`: the source of a
  selected pair is an integer.
* `CollatzPosDens.setOf_isSelectedPair_finite`: there are finitely many selected pairs of a
  given level.

## Implementation notes

The definition needs neither that the starting point `t` be a positive odd integer nor that
`X > 0`, so, as for `unweightedMass`, `t` is taken in `ℚ` and `X` is an arbitrary real. Sources
are rational numbers, as for `src`; integrality of the source of a selected pair is a lemma. A
history `h = (w₀, …, w_{n-1})` of generation `n` is a tuple `Fin n → Word`, as in
`centralHistories`.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {X : ℝ} {t : ℚ}

/-- `(h, w)` is a *selected pair of level `(t, n, X)`*: a member of `unweightedMassPairs n X t`. -/
@[collatz_pos_dens "def_s07_selected_pair"]
def IsSelectedPair (n : ℕ) (X : ℝ) (t : ℚ) (h : Fin n → Word) (w : Word) : Prop :=
  (h, w) ∈ unweightedMassPairs n X t

/-- The *source* `src(w, R_h)` of a pair `(h, w)`, where `R_h` is the endpoint of `h`. -/
@[collatz_pos_dens "def_s07_selected_pair"]
abbrev selectedPairSource (t : ℚ) (h : Fin n → Word) (w : Word) : ℚ :=
  src w (historyEndpoint t h)

/-- The selected pairs of level `(t, n, X)` are the members of `unweightedMassPairs n X t`. -/
theorem isSelectedPair_iff_mem_unweightedMassPairs {h : Fin n → Word} {w : Word} :
    IsSelectedPair n X t h w ↔ (h, w) ∈ unweightedMassPairs n X t :=
  Iff.rfl

/-- The defining conditions of a selected pair of level `(t, n, X)`. -/
theorem isSelectedPair_iff {h : Fin n → Word} {w : Word} :
    IsSelectedPair n X t h w ↔
      h ∈ centralHistories t n ∧ w ∈ firstCrossing (scale n) (historyShift n X t h) 1 ∧
        LengthOk (scale n) (historyShift n X t h) w ∧ Admissible (historyEndpoint t h) w :=
  mem_unweightedMassPairs

/-- The history of a selected pair is a central history. -/
theorem IsSelectedPair.mem_centralHistories {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X t h w) : h ∈ centralHistories t n :=
  (isSelectedPair_iff.1 hp).1

/-- The word of a selected pair lies in the first-crossing family `𝒲(b_n, u_h, 1)`. -/
theorem IsSelectedPair.mem_firstCrossing {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X t h w) : w ∈ firstCrossing (scale n) (historyShift n X t h) 1 :=
  (isSelectedPair_iff.1 hp).2.1

/-- The word of a selected pair satisfies the length condition `Λ_{b_n,u_h}`. -/
theorem IsSelectedPair.lengthOk {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X t h w) : LengthOk (scale n) (historyShift n X t h) w :=
  (isSelectedPair_iff.1 hp).2.2.1

/-- The word of a selected pair is admissible from the endpoint of its history. -/
theorem IsSelectedPair.admissible {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X t h w) : Admissible (historyEndpoint t h) w :=
  (isSelectedPair_iff.1 hp).2.2.2

/-- The source of a selected pair is an integer, in the form `den = 1`. -/
theorem IsSelectedPair.den_selectedPairSource_eq_one {h : Fin n → Word} {w : Word}
    (hp : IsSelectedPair n X t h w) : (selectedPairSource t h w).den = 1 :=
  hp.admissible.den_src_eq_one

/-- The source of a selected pair is an integer. -/
theorem IsSelectedPair.exists_intCast_eq_selectedPairSource {h : Fin n → Word}
    {w : Word} (hp : IsSelectedPair n X t h w) : ∃ z : ℤ, selectedPairSource t h w = z :=
  ⟨(selectedPairSource t h w).num,
    (Rat.coe_int_num_of_den_eq_one hp.den_selectedPairSource_eq_one).symm⟩

/-- There are finitely many selected pairs of level `(t, n, X)`. -/
theorem setOf_isSelectedPair_finite (n : ℕ) (X : ℝ) (t : ℚ) :
    {p : (Fin n → Word) × Word | IsSelectedPair n X t p.1 p.2}.Finite :=
  unweightedMassPairs_finite n X t

end CollatzPosDens
