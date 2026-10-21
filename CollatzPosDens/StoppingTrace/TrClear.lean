/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.S02Beta
public import CollatzPosDens.Transfer.S02HDef
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.StoppingTrace.TrFreshLaw

/-!
# Slow clearing

For a Fourier index `ι ∈ 𝔍` and `n ≥ 1`, the *slow clearing* event `Clr(ι) ⊆ 𝒜_n` consists of
the fresh atoms `a = ((r, ℓ), β)` for which some window `{u + 1, …, u + h_*(ι, u)}` ending before
`P_*(ι)` has a small total height gain:
`Clr(ι) = {a ∈ 𝒜_n : ∃ u ∈ ℕ, u + h_*(ι, u) ≤ P_*(ι) - 1 ∧
  ∑_{i=u+1}^{u+h_*(ι,u)} l(β^i) ≤ (13/9) β_*(ι, u)}`,
where `l(β^i)` is the second coordinate of the block point `bpt(β^i)`.

## Main definitions

* `CollatzPosDens.trClearGain`: the height gain `∑_{i=q+1}^{q+h} l(β^i)` of a window.
* `CollatzPosDens.trClear`: the set `Clr(ι)`.

## Main results

* `CollatzPosDens.mem_trClear`: the membership criterion.
* `CollatzPosDens.trClear_subset_trAtoms`: `Clr(ι) ⊆ 𝒜_n`.
* `CollatzPosDens.trClearGain_eq_chBlockPath`: inside the list, the window gain is the
  increment `l(Bp_{q+h}(β)) - l(Bp_q(β))` of the block path.
* `CollatzPosDens.lt_trClearGain_of_notMem_trClear`: outside `Clr(ι)`, every admissible window
  gains more than `(13/9) β_*(ι, u)`.

## Implementation notes

The blocks of `β = (β¹, …, β^N)` are indexed from `1`; the block `β^i` is the list entry
`β[i - 1]`. For indices `i > N` the block `β^i` does not exist, and the gain counts it as `0`,
consistently with the block path `Bp`, which is constant beyond the end of the list. The gain is an
integer and the comparison with `(13/9) β_*(ι, u)` is made in `ℝ`; `trClearGain_le_iff` restates it
as `9 · gain ≤ 13 β_*(ι, u)` in `ℤ`. The set lives in the ambient type
`(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n` and carries the condition `a ∈ 𝒜_n` explicitly; the
hypothesis `n ≥ 1` plays no role in the definition and is dropped.

## References

* [Mazur, *Collatz positive density*], §9.11.
-/

@[expose] public section

namespace CollatzPosDens

/-- The height gain `∑_{i=q+1}^{q+h} l(β^i)` of the window `{q + 1, …, q + h}` of a block list
`β`, where `l(β^i)` is the second coordinate of `bpt(β^i) = bpt(β[i - 1])`; blocks beyond the end
of `β` count as `0`. -/
def trClearGain (β : List (List ℤ × ℤ)) (q h : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ioc q (q + h), ((β[i - 1]?).map fun b => (chBlockPoint b).2).getD 0

/-- The slow clearing event for the Fourier index `ι`:
`Clr(ι) = {a ∈ 𝒜_n : ∃ u, u + h_*(ι, u) ≤ P_*(ι) - 1 ∧
  ∑_{i=u+1}^{u+h_*(ι,u)} l(β^i) ≤ (13/9) β_*(ι, u)}`. -/
@[collatz_pos_dens "def_tr_clear"]
def trClear (ι : FIndex) (n : ℕ) : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧ ∃ u : ℕ, u + windowLength ι u ≤ pStar ι - 1 ∧
    (trClearGain a.2 u (windowLength ι u) : ℝ) ≤ 13 / 9 * (betaStar ι u : ℝ)}

/-- Membership in `Clr(ι)`. -/
theorem mem_trClear {ι : FIndex} {n : ℕ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)} :
    a ∈ trClear ι n ↔ a ∈ trAtoms n ∧ ∃ u : ℕ, u + windowLength ι u ≤ pStar ι - 1 ∧
      (trClearGain a.2 u (windowLength ι u) : ℝ) ≤ 13 / 9 * (betaStar ι u : ℝ) :=
  Iff.rfl

/-- `Clr(ι) ⊆ 𝒜_n`. -/
theorem trClear_subset_trAtoms (ι : FIndex) (n : ℕ) : trClear ι n ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- The comparison `gain ≤ (13/9) β_*(ι, q)` in `ℝ` is `9 · gain ≤ 13 β_*(ι, q)` in `ℤ`. -/
theorem trClearGain_le_iff (ι : FIndex) (β : List (List ℤ × ℤ)) (q h : ℕ) :
    (trClearGain β q h : ℝ) ≤ 13 / 9 * (betaStar ι q : ℝ) ↔
      9 * trClearGain β q h ≤ 13 * (betaStar ι q : ℤ) := by
  rw [← @Int.cast_le ℝ]
  push_cast
  constructor <;> intro <;> linarith

/-- The gain of an empty window is `0`. -/
@[simp]
theorem trClearGain_zero (β : List (List ℤ × ℤ)) (q : ℕ) : trClearGain β q 0 = 0 := by
  simp [trClearGain]

/-- Extending a window by one block adds the height of that block (or `0` beyond the list). -/
theorem trClearGain_succ (β : List (List ℤ × ℤ)) (q h : ℕ) :
    trClearGain β q (h + 1) =
      trClearGain β q h + ((β[q + h]?).map fun b => (chBlockPoint b).2).getD 0 := by
  rw [trClearGain, trClearGain, ← add_assoc, Finset.sum_Ioc_succ_top (by omega)]
  simp

/-- Inside the list, the window gain is the increment of the second coordinate of the block
path: `∑_{i=q+1}^{q+h} l(β^i) = l(Bp_{q+h}(β)) - l(Bp_q(β))`. -/
theorem trClearGain_eq_chBlockPath (β : List (List ℤ × ℤ)) (q h : ℕ)
    (hle : q + h ≤ β.length) :
    trClearGain β q h = (chBlockPath β (q + h)).2 - (chBlockPath β q).2 := by
  induction h with
  | zero => simp
  | succ h ih =>
    have hlt : q + h < β.length := by omega
    rw [trClearGain_succ, ih (by omega), ← add_assoc, chBlockPath_succ β hlt,
      List.getElem?_eq_getElem hlt]
    simp only [Option.map_some, Option.getD_some, Prod.snd_add]
    ring

/-- Outside `Clr(ι)`, an atom of `𝒜_n` gains more than `(13/9) β_*(ι, u)` over every window
`{u + 1, …, u + h_*(ι, u)}` with `u + h_*(ι, u) ≤ P_*(ι) - 1`. -/
theorem lt_trClearGain_of_notMem_trClear {ι : FIndex} {n : ℕ}
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n) (hc : a ∉ trClear ι n) {u : ℕ}
    (hu : u + windowLength ι u ≤ pStar ι - 1) :
    13 / 9 * (betaStar ι u : ℝ) < (trClearGain a.2 u (windowLength ι u) : ℝ) :=
  not_le.1 fun h => hc ⟨ha, u, hu, h⟩

end CollatzPosDens
