/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Beta
public import CollatzPosDens.Transfer.HDef
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.StoppingTrace.TrFreshLaw

/-!
# The failed clearing window

For `n ≥ 1`, the event `Clr ⊆ 𝒜_n` of a *failed clearing window* consists of the fresh atoms
`a = ((r, ℓ), β)` for which some window `{q + 1, …, q + h_*(q)}` ending before `P_*` has a small
total height gain:
`Clr = {a ∈ 𝒜_n : ∃ q ∈ ℕ, q + h_*(q) ≤ P_* - 1 ∧ ∑_{i=q+1}^{q+h_*(q)} l(β^i) ≤ (13/9) β_*(q)}`,
where `l(β^i)` is the second coordinate of the block point `bpt(β^i)`.

## Main definitions

* `CollatzPosDens.trClearGain`: the height gain `∑_{i=q+1}^{q+h} l(β^i)` of a window.
* `CollatzPosDens.trClear`: the set `Clr`.

## Main results

* `CollatzPosDens.mem_trClear`: the membership criterion.
* `CollatzPosDens.trClear_subset_trAtoms`: `Clr ⊆ 𝒜_n`.
* `CollatzPosDens.trClearGain_eq_chBlockPath`: inside the list, the window gain is the
  increment `l(Bp_{q+h}(β)) - l(Bp_q(β))` of the block path.
* `CollatzPosDens.lt_trClearGain_of_notMem_trClear`: outside `Clr`, every admissible window
  gains more than `(13/9) β_*(q)`.

## Implementation notes

The blocks of `β = (β¹, …, β^N)` are indexed from `1`; the block `β^i` is the list entry
`β[i - 1]`. Windows with `q + h_*(q) > N` are allowed: for indices `i > N` the block `β^i` does not
exist, and the gain counts it as `0`, consistently with the block path `Bp`, which is constant
beyond the end of the list. The gain is an integer and the comparison with `(13/9) β_*(q)` is made
in `ℝ`; `trClearGain_le_iff` restates it as `9 · gain ≤ 13 β_*(q)` in `ℤ`. The set lives in the
ambient type `(ℕ × ℤ) × List (List ℤ × ℤ)` of `𝒜_n` and carries the condition `a ∈ 𝒜_n`
explicitly; the hypothesis `n ≥ 1` plays no role in the definition and is dropped.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.8.
-/

@[expose] public section

namespace CollatzPosDens

/-- The height gain `∑_{i=q+1}^{q+h} l(β^i)` of the window `{q + 1, …, q + h}` of a block list
`β`, where `l(β^i)` is the second coordinate of `bpt(β^i) = bpt(β[i - 1])`; blocks beyond the end
of `β` count as `0`. -/
def trClearGain (β : List (List ℤ × ℤ)) (q h : ℕ) : ℤ :=
  ∑ i ∈ Finset.Ioc q (q + h), ((β[i - 1]?).map fun b => (chBlockPoint b).2).getD 0

/-- The failed clearing window event
`Clr = {a ∈ 𝒜_n : ∃ q, q + h_*(q) ≤ P_* - 1 ∧ ∑_{i=q+1}^{q+h_*(q)} l(β^i) ≤ (13/9) β_*(q)}`. -/
@[collatz_pos_dens "def_tr_clear"]
def trClear (n : ℕ) : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧ ∃ q : ℕ, q + windowLength q ≤ pStar - 1 ∧
    (trClearGain a.2 q (windowLength q) : ℝ) ≤ 13 / 9 * (betaStar q : ℝ)}

/-- Membership in `Clr`. -/
theorem mem_trClear {n : ℕ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)} :
    a ∈ trClear n ↔ a ∈ trAtoms n ∧ ∃ q : ℕ, q + windowLength q ≤ pStar - 1 ∧
      (trClearGain a.2 q (windowLength q) : ℝ) ≤ 13 / 9 * (betaStar q : ℝ) :=
  Iff.rfl

/-- `Clr ⊆ 𝒜_n`. -/
theorem trClear_subset_trAtoms (n : ℕ) : trClear n ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- The comparison `gain ≤ (13/9) β_*(q)` in `ℝ` is `9 · gain ≤ 13 β_*(q)` in `ℤ`. -/
theorem trClearGain_le_iff (β : List (List ℤ × ℤ)) (q h : ℕ) :
    (trClearGain β q h : ℝ) ≤ 13 / 9 * (betaStar q : ℝ) ↔
      9 * trClearGain β q h ≤ 13 * (betaStar q : ℤ) := by
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

/-- Outside `Clr`, an atom of `𝒜_n` gains more than `(13/9) β_*(q)` over every window
`{q + 1, …, q + h_*(q)}` with `q + h_*(q) ≤ P_* - 1`. -/
theorem lt_trClearGain_of_notMem_trClear {n : ℕ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (ha : a ∈ trAtoms n) (hc : a ∉ trClear n) {q : ℕ} (hq : q + windowLength q ≤ pStar - 1) :
    13 / 9 * (betaStar q : ℝ) < (trClearGain a.2 q (windowLength q) : ℝ) :=
  not_le.1 fun h => hc ⟨ha, q, hq, h⟩

end CollatzPosDens
