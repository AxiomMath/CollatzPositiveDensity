/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.StoppingTrace.TrFreshPath

/-!
# The large horizontal advance event

For a Fourier index `ι : FIndex`, `n : ℕ`, an entry point `e : ℤ × ℤ` and `m : ℕ`, the event
`Bad^e_m(ι)` is the set of fresh atoms `a ∈ 𝒜_n` (the set `trAtoms n`) whose fresh path
`y^e(a)` (the path `trFreshPath e a`) has advanced by at least `317m/400` levels above `e` at
time `P_*(ι)` (the time `pStar ι`), where `j` is the level `bkJ`:
`Bad^e_m(ι) = {a ∈ 𝒜_n : 400 (j(y^e_{P_*(ι)}(a)) - j(e)) ≥ 317m}`.

## Main definitions

* `CollatzPosDens.trBad`: the set `Bad^e_m(ι)`.

## Main results

* `CollatzPosDens.mem_trBad`: the membership criterion.
* `CollatzPosDens.trBad_subset_trAtoms`: `Bad^e_m(ι) ⊆ 𝒜_n`.
* `CollatzPosDens.trBad_antitone`: `Bad^e_m(ι)` decreases in `m`.

## Implementation notes

Levels are integers, so the difference `j(y^e_{P_*(ι)}(a)) - j(e)` is taken in `ℤ` and does not
truncate. The set lives in the ambient type `(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n` and carries
the condition `a ∈ 𝒜_n` explicitly. The hypotheses `n ≥ 1` and that `e` lies in the set of
entry points play no role in the definition and are dropped, so the set is defined for all `n`
and all `e`.

## References

* [Mazur, *Collatz positive density*], §9.11.
-/

@[expose] public section

namespace CollatzPosDens

/-- The large horizontal advance event
`Bad^e_m(ι) = {a ∈ 𝒜_n : 400 (j(y^e_{P_*(ι)}(a)) - j(e)) ≥ 317m}`. -/
@[collatz_pos_dens "def_tr_bad"]
def trBad (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) (m : ℕ) : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧ 317 * (m : ℤ) ≤ 400 * (bkJ (trFreshPath e a (pStar ι)) - bkJ e)}

/-- Membership in `Bad^e_m(ι)`. -/
theorem mem_trBad {ι : FIndex} {n : ℕ} {e : ℤ × ℤ} {m : ℕ}
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} :
    a ∈ trBad ι n e m ↔
      a ∈ trAtoms n ∧ 317 * (m : ℤ) ≤ 400 * (bkJ (trFreshPath e a (pStar ι)) - bkJ e) :=
  Iff.rfl

/-- `Bad^e_m(ι) ⊆ 𝒜_n`. -/
theorem trBad_subset_trAtoms (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) (m : ℕ) :
    trBad ι n e m ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- `Bad^e_m(ι)` is antitone in `m`. -/
theorem trBad_antitone (ι : FIndex) (n : ℕ) (e : ℤ × ℤ) : Antitone (trBad ι n e) :=
  fun _ _ hm _ ha => ⟨ha.1, le_trans (by gcongr) ha.2⟩

/-- Outside `Bad^e_m(ι)`, an atom of `𝒜_n` has `400 (j(y^e_{P_*(ι)}(a)) - j(e)) < 317m`. -/
theorem lt_of_not_mem_trBad {ι : FIndex} {n : ℕ} {e : ℤ × ℤ} {m : ℕ}
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n) (hb : a ∉ trBad ι n e m) :
    400 * (bkJ (trFreshPath e a (pStar ι)) - bkJ e) < 317 * (m : ℤ) :=
  not_le.1 fun h => hb ⟨ha, h⟩

end CollatzPosDens
