/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.BlackSet.BkBlack
public import CollatzPosDens.BlackSet.BkColTop
public import CollatzPosDens.Transfer.EpsStar

/-!
# Hits of a sequence of points

Fix a level `n`, a residue `ξ ∈ G_n` and a colour scale `ε`. Let `x = (x_t)_{t ∈ ℕ}` be a
sequence of points of `𝒫`. A time `t` is a *hit* of `x` if `x_t` is black. For a time `t' < t`
with `x_{t'}` black, the time `t` is a *hit of `x` after `t'`* if `x_t` is black and
`l(x_t) > l_*(x_{t'})`, i.e. `x_t` is black and lies strictly above the top of the black column
run through `x_{t'}`.

## Main definitions

* `CollatzPosDens.IsTrHit n ξ ε x t`: the time `t` is a hit of `x`.
* `CollatzPosDens.IsTrHitAfter n ξ ε x t' t`: the time `t` is a hit of `x` after `t'`.

## Main results

* `CollatzPosDens.isTrHit_iff`, `CollatzPosDens.isTrHitAfter_iff`: unfolding lemmas.
* `CollatzPosDens.IsTrHitAfter.isTrHit`: a hit after `t'` is a hit.
* `CollatzPosDens.IsTrHitAfter.bkColTop_lt`, `CollatzPosDens.IsTrHitAfter.bkL_lt`: a hit
  after `t'` lies strictly above `l_*(x_{t'})`, hence strictly above `x_{t'}`.
* `CollatzPosDens.not_isTrHitAfter_self`, `CollatzPosDens.IsTrHitAfter.ne`: a hit after
  `t'` differs from `t'`.

## Implementation notes

In the paper the colour scale is `ε = ε_*` (`CollatzPosDens.epsStar`); here the predicates
are stated for an arbitrary `ε : ℝ`. The points `x_t` range over `ℤ × ℤ`, of which `𝒫` is a
subset, so the definitions apply in particular to sequences in `𝒫`. The conditions `t' < t` and
"`x_{t'}` is black" are not part of `IsTrHitAfter`; they are imposed as separate hypotheses.
Decidability instances (classical) are provided, so that least hits can be taken with
`Nat.find`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The time `t` is a *hit* of the sequence `x` if `x_t` is black. -/
@[collatz_pos_dens "def_tr_hit"]
def IsTrHit (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℕ → ℤ × ℤ) (t : ℕ) : Prop :=
  BkBlack n ξ ε (x t)

/-- The time `t` is a *hit of `x` after `t'`* if `x_t` is black and `l(x_t) > l_*(x_{t'})`. -/
@[collatz_pos_dens "def_tr_hit"]
def IsTrHitAfter (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℕ → ℤ × ℤ) (t' t : ℕ) : Prop :=
  BkBlack n ξ ε (x t) ∧ bkColTop n ξ ε (x t') < bkL (x t)

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {x : ℕ → ℤ × ℤ} {t t' : ℕ}

/-- Unfolding lemma for `IsTrHit`. -/
theorem isTrHit_iff : IsTrHit n ξ ε x t ↔ BkBlack n ξ ε (x t) := Iff.rfl

/-- Unfolding lemma for `IsTrHitAfter`. -/
theorem isTrHitAfter_iff :
    IsTrHitAfter n ξ ε x t' t ↔ BkBlack n ξ ε (x t) ∧ bkColTop n ξ ε (x t') < bkL (x t) :=
  Iff.rfl

/-- Being a hit is decidable (classically). -/
noncomputable instance (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℕ → ℤ × ℤ) :
    DecidablePred (IsTrHit n ξ ε x) :=
  fun t => inferInstanceAs (Decidable (BkBlack n ξ ε (x t)))

/-- Being a hit after `t'` is decidable (classically). -/
noncomputable instance (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℕ → ℤ × ℤ) (t' : ℕ) :
    DecidablePred (IsTrHitAfter n ξ ε x t') :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- A hit after `t'` is a hit. -/
theorem IsTrHitAfter.isTrHit (h : IsTrHitAfter n ξ ε x t' t) : IsTrHit n ξ ε x t := h.1

/-- A hit after `t'` lies strictly above `l_*(x_{t'})`. -/
theorem IsTrHitAfter.bkColTop_lt (h : IsTrHitAfter n ξ ε x t' t) :
    bkColTop n ξ ε (x t') < bkL (x t) := h.2

/-- A hit after `t'` lies strictly above `x_{t'}`: `l(x_{t'}) < l(x_t)`. -/
theorem IsTrHitAfter.bkL_lt (h : IsTrHitAfter n ξ ε x t' t) : bkL (x t') < bkL (x t) :=
  le_bkColTop.trans_lt h.2

/-- A time is never a hit after itself. -/
theorem not_isTrHitAfter_self : ¬IsTrHitAfter n ξ ε x t t :=
  fun h => h.bkL_lt.false

/-- A hit after `t'` is a time different from `t'`. -/
theorem IsTrHitAfter.ne (h : IsTrHitAfter n ξ ε x t' t) : t' ≠ t := by
  rintro rfl
  exact not_isTrHitAfter_self h

end CollatzPosDens
