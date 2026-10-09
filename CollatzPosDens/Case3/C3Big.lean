/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkFamily
public import CollatzPosDens.BlackSet.BkTriangle
public import CollatzPosDens.StoppingTrace.TrFreshLaw
public import CollatzPosDens.StoppingTrace.TrFreshPath

/-!
# The large-triangle event within a block of offsets

Fix a level `n`, a residue `ξ` and a tolerance `ε`, with canonical family `𝔗 = 𝔗_{n,ξ,ε}`. For an
entry point `e ∈ 𝒫`, a level `G ∈ ℕ`, an offset bound `v ∈ ℕ` with `v ≤ J = ⌊n/2⌋` and a real
`s`, the large-triangle event `Big_{e,G,v,s}` is the set of atoms `a` of the fresh law `μ_{e,G}`
whose fresh path meets a large triangle of the family within the first `v` offsets:
`y^e_u(a) ∈ Δ` for some `u ∈ {0, …, v}` and some `Δ ∈ 𝔗` with `s_Δ ≥ s`.

## Main definitions

* `CollatzPosDens.c3Big`: the event `Big_{e,G,v,s}`, a set of fresh atoms in `𝒜_n`.

## Main results

* `CollatzPosDens.mem_c3Big`: the membership criterion.
* `CollatzPosDens.c3Big_subset_trAtoms`: `Big_{e,G,v,s} ⊆ 𝒜_n`.
* `CollatzPosDens.c3Big_mono`: the event grows with `v` and shrinks as `s` grows.
* `CollatzPosDens.c3Big_eq_biUnion`: the event is the union over `u ≤ v` of the events at
  offset `u`.
* `CollatzPosDens.c3Big_indep_level`: the event does not depend on `G`.
* `CollatzPosDens.c3Big_eq_of_div_two_le`: the event is constant in `v` from `v = ⌊n/2⌋` on.
* `CollatzPosDens.c3Big_eq_empty_of_bkFamily_eq_empty`: the event is empty when the family
  is.

## Implementation notes

In the source `𝔗 = 𝔗_{n,ξ,ε_*}` is fixed for the whole section; here the tolerance `ε` is an
explicit argument, which generalizes the source (the source's event is the case `ε = ε_*`). As
for the other events of the fresh law, the set lives in the ambient type
`(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n` and carries the condition `a ∈ 𝒜_n` explicitly. The event
does not depend on `G`, since neither the path nor the family does; `G` is kept so that the
event is indexed like the fresh law `μ_{e,G}`. The hypotheses `e ∈ 𝒫`, `v ≤ J` and that `ξ` is a
unit play no role in the definition and are dropped, which generalizes the source.

## References

* [Mazur, *Collatz positive density*], §10.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- The large-triangle event `Big_{e,G,v,s}`: the atoms `a ∈ 𝒜_n` of `μ_{e,G}` such that
`y^e_u(a) ∈ Δ` for some `u ∈ {0, …, v}` and some `Δ ∈ 𝔗_{n,ξ,ε}` with `s_Δ ≥ s`. -/
@[collatz_pos_dens "def_c3_big"]
def c3Big (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (e : ℤ × ℤ) (_G v : ℕ) (s : ℝ) :
    Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧ ∃ u ≤ v, ∃ Δ ∈ bkFamily n ξ ε, trFreshPath e a u ∈ Δ ∧ s ≤ Δ.s}

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {e : ℤ × ℤ} {G v : ℕ} {s : ℝ}
  {a : (ℕ × ℤ) × List (List ℤ × ℤ)}

/-- Membership in `Big_{e,G,v,s}`. -/
theorem mem_c3Big :
    a ∈ c3Big n ξ ε e G v s ↔
      a ∈ trAtoms n ∧ ∃ u ≤ v, ∃ Δ ∈ bkFamily n ξ ε, trFreshPath e a u ∈ Δ ∧ s ≤ Δ.s :=
  Iff.rfl

/-- `Big_{e,G,v,s} ⊆ 𝒜_n`. -/
theorem c3Big_subset_trAtoms (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (e : ℤ × ℤ) (G v : ℕ)
    (s : ℝ) : c3Big n ξ ε e G v s ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- A fresh atom whose path at an offset `u ≤ v` lies in a triangle `Δ ∈ 𝔗` with `s_Δ ≥ s`
lies in `Big_{e,G,v,s}`. -/
theorem mem_c3Big_of_mem {u : ℕ} {Δ : BkTriangle} (ha : a ∈ trAtoms n) (hu : u ≤ v)
    (hΔ : Δ ∈ bkFamily n ξ ε) (hmem : trFreshPath e a u ∈ Δ) (hs : s ≤ Δ.s) :
    a ∈ c3Big n ξ ε e G v s :=
  ⟨ha, u, hu, Δ, hΔ, hmem, hs⟩

/-- The large-triangle event grows with the offset bound `v` and shrinks as the size threshold
`s` grows. -/
theorem c3Big_mono {v v' : ℕ} {s s' : ℝ} (hv : v ≤ v') (hs : s' ≤ s) :
    c3Big n ξ ε e G v s ⊆ c3Big n ξ ε e G v' s' := by
  rintro a ⟨ha, u, hu, Δ, hΔ, hmem, hsΔ⟩
  exact ⟨ha, u, hu.trans hv, Δ, hΔ, hmem, hs.trans hsΔ⟩

/-- The large-triangle event does not depend on the level `G`. -/
theorem c3Big_indep_level (G G' : ℕ) : c3Big n ξ ε e G v s = c3Big n ξ ε e G' v s :=
  rfl

/-- The large-triangle event is the union over the offsets `u ≤ v` of the atoms whose path at
time `u` lies in a large triangle. -/
theorem c3Big_eq_biUnion :
    c3Big n ξ ε e G v s =
      ⋃ u ∈ Finset.range (v + 1),
        {a | a ∈ trAtoms n ∧ ∃ Δ ∈ bkFamily n ξ ε, trFreshPath e a u ∈ Δ ∧ s ≤ Δ.s} := by
  ext a
  simp only [mem_c3Big, Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, exists_prop,
    Nat.lt_succ_iff]
  constructor
  · rintro ⟨ha, u, hu, h⟩
    exact ⟨u, hu, ha, h⟩
  · rintro ⟨u, hu, ha, h⟩
    exact ⟨ha, u, hu, h⟩

/-- For `v ≥ ⌊n/2⌋`, the large-triangle event `Big_{e,G,v,s}` equals `Big_{e,G,⌊n/2⌋,s}`. -/
theorem c3Big_eq_of_div_two_le (hv : n / 2 ≤ v) :
    c3Big n ξ ε e G v s = c3Big n ξ ε e G (n / 2) s := by
  refine subset_antisymm ?_ (c3Big_mono hv le_rfl)
  rintro a ⟨ha, u, -, Δ, hΔ, hmem, hsΔ⟩
  rcases le_total u (n / 2) with hu | hu
  · exact ⟨ha, u, hu, Δ, hΔ, hmem, hsΔ⟩
  · exact ⟨ha, n / 2, le_rfl, Δ, hΔ, trFreshPath_of_le e ha hu ▸ hmem, hsΔ⟩

/-- The large-triangle event is empty when the family `𝔗_{n,ξ,ε}` is empty. -/
theorem c3Big_eq_empty_of_bkFamily_eq_empty (h : bkFamily n ξ ε = ∅) :
    c3Big n ξ ε e G v s = ∅ := by
  ext a
  simp [mem_c3Big, h]

end CollatzPosDens
