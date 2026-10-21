/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.StoppingTrace.TrFreshPath
public import CollatzPosDens.Transfer.EpsStar
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.S02Beta

/-!
# Oversize hits of a fresh path

Fix a Fourier index `ι ∈ 𝔍`, a level `n ≥ 1`, a unit `ξ ∈ G_n`, an entry point `e ∈ 𝒫` and a
fresh atom `a ∈ 𝒜_n`. For a time `u` with `0 ≤ u ≤ P_*(ι) - 1`, the atom `a` has an *oversize
hit at time `u` for `ι`* if the point `y^e_u(a)` of its fresh path lies in some triangle
`Δ ∈ 𝔗_{n,ξ,ε_*}` of the canonical family whose size is at least the oversize threshold:
`s_Δ ≥ β_*(ι, u)`.

## Main definitions

* `CollatzPosDens.IsTrOversizeHit ι n ξ ε e a u`: the atom `a` has an oversize hit at time `u`
  for `ι`.

## Main results

* `CollatzPosDens.isTrOversizeHit_iff`: unfolding lemma.
* `CollatzPosDens.isTrOversizeHit_iff_exists_bkCanonTriangle`: an oversize hit is a black
  point `p ∈ 𝒫` whose canonical triangle `Δ(p)` contains `y^e_u(a)` and has size at least
  `β_*(ι, u)`.
* `CollatzPosDens.IsTrOversizeHit.exists_pos_size`: the witnessing triangle has positive size.
* `CollatzPosDens.IsTrOversizeHit.mem_bkPoints`: at an oversize hit, `y^e_u(a) ∈ 𝒫`.
* `CollatzPosDens.not_isTrOversizeHit_of_forall_not_bkBlack`: without black points there is no
  oversize hit.

## Implementation notes

The predicate is stated for an arbitrary colour scale `ε : ℝ`, which specialises to
`ε = (ε_* : ℝ)` (`CollatzPosDens.epsStar`). The side conditions `n ≥ 1`, `ξ` a unit, `e ∈ 𝒫`,
`a ∈ 𝒜_n` and `u ≤ P_*(ι) - 1` play no role in the definition, so they are not part of it. The
point `e` ranges over `ℤ × ℤ` and the atom over the ambient type of `𝒜_n`, as for
`CollatzPosDens.trFreshPath`. The threshold `β_*(ι, u) ∈ ℕ` is compared with the real size `s_Δ`
through the cast `ℕ → ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The atom `a` has an *oversize hit at time `u` for `ι`* (from the entry point `e`) if there
is `Δ ∈ 𝔗_{n,ξ,ε}` with `y^e_u(a) ∈ Δ` and `s_Δ ≥ β_*(ι, u)`. -/
@[collatz_pos_dens "def_tr_oversize_hit"]
def IsTrOversizeHit (ι : FIndex) (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (e : ℤ × ℤ)
    (a : (ℕ × ℤ) × List (List ℤ × ℤ)) (u : ℕ) : Prop :=
  ∃ Δ ∈ bkFamily n ξ ε, trFreshPath e a u ∈ Δ ∧ (betaStar ι u : ℝ) ≤ Δ.s

variable {ι : FIndex} {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {e : ℤ × ℤ}
  {a : (ℕ × ℤ) × List (List ℤ × ℤ)} {u : ℕ}

/-- Unfolding lemma for `IsTrOversizeHit`. -/
theorem isTrOversizeHit_iff :
    IsTrOversizeHit ι n ξ ε e a u ↔
      ∃ Δ ∈ bkFamily n ξ ε, trFreshPath e a u ∈ Δ ∧ (betaStar ι u : ℝ) ≤ Δ.s :=
  Iff.rfl

/-- An oversize hit at time `u` is a black point `p ∈ 𝒫` whose canonical triangle `Δ(p)`
contains `y^e_u(a)` and has size at least `β_*(ι, u)`. -/
theorem isTrOversizeHit_iff_exists_bkCanonTriangle :
    IsTrOversizeHit ι n ξ ε e a u ↔
      ∃ p, ∃ hp : p ∈ bkPoints, BkBlack n ξ ε p ∧
        trFreshPath e a u ∈ bkCanonTriangle n ξ ε p hp ∧
          (betaStar ι u : ℝ) ≤ (bkCanonTriangle n ξ ε p hp).s :=
  exists_mem_bkFamily

/-- A black point whose canonical triangle contains `y^e_u(a)` and has size at least `β_*(ι, u)`
gives an oversize hit at time `u`. -/
theorem IsTrOversizeHit.of_bkCanonTriangle {p : ℤ × ℤ} (hp : p ∈ bkPoints)
    (hb : BkBlack n ξ ε p) (hmem : trFreshPath e a u ∈ bkCanonTriangle n ξ ε p hp)
    (hs : (betaStar ι u : ℝ) ≤ (bkCanonTriangle n ξ ε p hp).s) :
    IsTrOversizeHit ι n ξ ε e a u :=
  ⟨_, bkCanonTriangle_mem_bkFamily hp hb, hmem, hs⟩

/-- The triangle witnessing an oversize hit has positive size. -/
theorem IsTrOversizeHit.exists_pos_size (h : IsTrOversizeHit ι n ξ ε e a u) :
    ∃ Δ ∈ bkFamily n ξ ε, trFreshPath e a u ∈ Δ ∧ 0 < Δ.s :=
  let ⟨Δ, hΔ, hmem, hs⟩ := h
  ⟨Δ, hΔ, hmem, lt_of_lt_of_le (by exact_mod_cast betaStar_pos ι u) hs⟩

/-- At an oversize hit, the point `y^e_u(a)` lies in `𝒫`. -/
theorem IsTrOversizeHit.mem_bkPoints (h : IsTrOversizeHit ι n ξ ε e a u) :
    trFreshPath e a u ∈ bkPoints :=
  let ⟨_, _, hmem, _⟩ := h
  BkTriangle.mem_bkPoints_of_mem hmem

/-- There is no oversize hit when `𝒫` has no black points. -/
theorem not_isTrOversizeHit_of_forall_not_bkBlack (h : ∀ p ∈ bkPoints, ¬BkBlack n ξ ε p) :
    ¬IsTrOversizeHit ι n ξ ε e a u := by
  rw [isTrOversizeHit_iff_exists_bkCanonTriangle]
  rintro ⟨p, hp, hb, -⟩
  exact h p hp hb

/-- Having an oversize hit is decidable (classically). -/
noncomputable instance (ι : FIndex) (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (e : ℤ × ℤ)
    (a : (ℕ × ℤ) × List (List ℤ × ℤ)) : DecidablePred (IsTrOversizeHit ι n ξ ε e a) :=
  fun _ => Classical.dec _

end CollatzPosDens
