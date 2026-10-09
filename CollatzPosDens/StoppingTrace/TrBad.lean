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

For `n ≥ 1`, an entry point `e ∈ 𝒫` and `m ∈ ℕ`, the event `Bad^e_m ⊆ 𝒜_n` consists of the
fresh atoms `a` whose fresh path has advanced by at least `317m/400` levels above `e` at time
`P_*`:
`Bad^e_m = {a ∈ 𝒜_n : 400 (j(y^e_{P_*}(a)) - j(e)) ≥ 317m}`.

## Main definitions

* `CollatzPosDens.trBad`: the set `Bad^e_m`.

## Main results

* `CollatzPosDens.mem_trBad`: the membership criterion.
* `CollatzPosDens.trBad_subset_trAtoms`: `Bad^e_m ⊆ 𝒜_n`.
* `CollatzPosDens.trBad_antitone`: `Bad^e_m` decreases in `m`.
* `CollatzPosDens.lt_of_notMem_trBad`: outside `Bad^e_m`, an atom of `𝒜_n` has
  `400 (j(y^e_{P_*}(a)) - j(e)) < 317m`.

## Implementation notes

Levels are integers, so the difference `j(y^e_{P_*}(a)) - j(e)` is taken in `ℤ` and does not
truncate. The set lives in the ambient type `(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n` and carries
the condition `a ∈ 𝒜_n` explicitly. The hypotheses `n ≥ 1` and `e ∈ 𝒫` play no role in the
definition and are dropped.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The large horizontal advance event
`Bad^e_m = {a ∈ 𝒜_n : 400 (j(y^e_{P_*}(a)) - j(e)) ≥ 317m}`. -/
@[collatz_pos_dens "def_tr_bad"]
def trBad (n : ℕ) (e : ℤ × ℤ) (m : ℕ) : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧ 317 * (m : ℤ) ≤ 400 * (bkJ (trFreshPath e a pStar) - bkJ e)}

/-- Membership in `Bad^e_m`. -/
theorem mem_trBad {n : ℕ} {e : ℤ × ℤ} {m : ℕ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)} :
    a ∈ trBad n e m ↔
      a ∈ trAtoms n ∧ 317 * (m : ℤ) ≤ 400 * (bkJ (trFreshPath e a pStar) - bkJ e) :=
  Iff.rfl

/-- `Bad^e_m ⊆ 𝒜_n`. -/
theorem trBad_subset_trAtoms (n : ℕ) (e : ℤ × ℤ) (m : ℕ) : trBad n e m ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- `Bad^e_m` is antitone in `m`. -/
theorem trBad_antitone (n : ℕ) (e : ℤ × ℤ) : Antitone (trBad n e) :=
  fun _ _ hm _ ha => ⟨ha.1, le_trans (by gcongr) ha.2⟩

/-- Outside `Bad^e_m`, an atom of `𝒜_n` has `400 (j(y^e_{P_*}(a)) - j(e)) < 317m`. -/
theorem lt_of_notMem_trBad {n : ℕ} {e : ℤ × ℤ} {m : ℕ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (ha : a ∈ trAtoms n) (hb : a ∉ trBad n e m) :
    400 * (bkJ (trFreshPath e a pStar) - bkJ e) < 317 * (m : ℤ) :=
  not_le.1 fun h => hb ⟨ha, h⟩

end CollatzPosDens
