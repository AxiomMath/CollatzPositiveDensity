/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShGate
public import CollatzPosDens.Mixing.MxShPattern

/-!
# The slice of a gate `Sl^sh_n(d, j)`

For natural numbers `n`, `d` and `j`, the *slice* of the gate `(d, j)` of the shell cut is the set
of words of length `n` whose exposed pattern at the clock position `H^{sh}_n - 1` is an exposed
pattern of the gate `(d, j)`:
$$\mathrm{Sl}^{\mathrm{sh}}_n(d, j) = \{w \in \mathbb{Z}_{\ge 1}^n :
  \mathrm{Ex}_{H^{\mathrm{sh}}_n - 1}(w) \in \mathrm{Hd}^{\mathrm{sh}}_n(d, j)\}.$$
Since every pattern of `Hd^{sh}_n(d, j)` has `d` elements, a word of the slice has exactly `d`
partial sums at most `H^{sh}_n - 1`.

## Main definitions

* `CollatzPosDens.mxShSlice`: the slice `Sl^sh_n(d, j)`, a set of words.

## Main results

* `CollatzPosDens.mem_mxShSlice`: the defining condition.
* `CollatzPosDens.length_of_mem_mxShSlice`: members have length `n`.
* `CollatzPosDens.card_exposedPattern_of_mem_mxShSlice`: members have `|Ex_{H-1}(w)| = d`.
* `CollatzPosDens.mxShSlice_eq`: `Sl^sh_n(d, j)` is the set of words of length `n` with
  `|Ex_{H-1}(w)| = d` and `Ex_{H-1}(w) ∈ Hd^sh_n(d, j)`.

## Implementation notes

Words of length `n` are lists of positive integers of length `n` (`Word`), so the slice is a
`Set Word`. The paper states the definition for `n ≥ 1`; the Lean definition takes all natural
numbers. The clock position `H^{sh}_n - 1` uses truncated subtraction, which agrees with the
paper since `H^{sh}_n ≥ 1` for `n ≥ 1`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The slice `Sl^sh_n(d, j)` of the gate `(d, j)`: the words `w` of length `n` whose exposed
pattern `Ex_{H^{sh}_n - 1}(w)` lies in `Hd^{sh}_n(d, j)`. -/
@[collatz_pos_dens "def_mx_sh_slice"]
def mxShSlice (n d j : ℕ) : Set Word :=
  {w | w.length = n ∧ Word.exposedPattern (shHeight n - 1) w ∈ shRetainedHeads n d j}

/-- The defining condition of the slice `Sl^sh_n(d, j)`. -/
theorem mem_mxShSlice {n d j : ℕ} {w : Word} :
    w ∈ mxShSlice n d j ↔
      w.length = n ∧ Word.exposedPattern (shHeight n - 1) w ∈ shRetainedHeads n d j :=
  Iff.rfl

/-- Every word of the slice `Sl^sh_n(d, j)` has length `n`. -/
theorem length_of_mem_mxShSlice {n d j : ℕ} {w : Word} (hw : w ∈ mxShSlice n d j) :
    w.length = n :=
  hw.1

/-- The exposed pattern of a word of `Sl^sh_n(d, j)` lies in `Hd^sh_n(d, j)`. -/
theorem exposedPattern_mem_of_mem_mxShSlice {n d j : ℕ} {w : Word} (hw : w ∈ mxShSlice n d j) :
    Word.exposedPattern (shHeight n - 1) w ∈ shRetainedHeads n d j :=
  hw.2

/-- A word of `Sl^sh_n(d, j)` has exactly `d` partial sums at most `H^{sh}_n - 1`. -/
theorem card_exposedPattern_of_mem_mxShSlice {n d j : ℕ} {w : Word}
    (hw : w ∈ mxShSlice n d j) : #(Word.exposedPattern (shHeight n - 1) w) = d :=
  card_eq_of_mem_shRetainedHeads hw.2

/-- A word of `Sl^sh_n(d, j)` has `d ≤ n`. -/
theorem le_of_mem_mxShSlice {n d j : ℕ} {w : Word} (hw : w ∈ mxShSlice n d j) : d ≤ n := by
  rw [← card_exposedPattern_of_mem_mxShSlice hw, ← length_of_mem_mxShSlice hw]
  exact Word.card_exposedPattern_le _ _

/-- The slice is the set of words of length `n` with `|Ex_{H-1}(w)| = d` and
`Ex_{H-1}(w) ∈ Hd^sh_n(d, j)`. -/
theorem mxShSlice_eq (n d j : ℕ) :
    mxShSlice n d j = {w | w.length = n ∧ #(Word.exposedPattern (shHeight n - 1) w) = d ∧
      Word.exposedPattern (shHeight n - 1) w ∈ shRetainedHeads n d j} := by
  ext w
  exact ⟨fun hw => ⟨hw.1, card_exposedPattern_of_mem_mxShSlice hw, hw.2⟩,
    fun hw => ⟨hw.1, hw.2.2⟩⟩

/-- The slice `Sl^sh_n(d, j)` is empty when `n < d`. -/
theorem mxShSlice_eq_empty_of_lt {n d j : ℕ} (h : n < d) : mxShSlice n d j = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ hw => (le_of_mem_mxShSlice hw).not_gt h

end CollatzPosDens
