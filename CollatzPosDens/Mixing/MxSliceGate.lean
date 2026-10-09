/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxHeadGate

/-!
# The slice gate `Sl(n, k, l)`

For `n ≥ 1` and `k, l ∈ ℕ` with `k < n`, the *slice gate* `Sl(n, k, l)` is the cylinder
of words `w ∈ ℤ_{≥1}^n` of length `n` whose prefix of length `k + 1` lies in the head gate
`Hd(n, k, l)`:
$$\mathrm{Sl}(n,k,l) = \{w \in \mathbb{Z}_{\ge 1}^n : w_{\le k+1} \in \mathrm{Hd}(n,k,l)\}.$$

## Main definitions

* `CollatzPosDens.mxSliceGate`: the slice gate `Sl(n, k, l)`, a set of words.

## Main results

* `CollatzPosDens.mem_mxSliceGate`: the defining condition.
* `CollatzPosDens.length_of_mem_mxSliceGate`: members have length `n`.
* `CollatzPosDens.take_mem_mxHeadGate_of_mem_mxSliceGate`: the prefix of length `k + 1`
  of a member lies in `Hd(n, k, l)`.
* `CollatzPosDens.mxSliceGate_eq_empty_of_le`: the slice gate is empty unless `k < n`.

## Implementation notes

Words of length `n` are lists of positive integers of length `n` (`Word`), so that the slice
gate is a `Set Word`. The prefix `w_{≤ k+1}` is `w.take (k + 1)`. The definition is stated for
all `n, k, l`; the hypotheses `n ≥ 1` and `k < n` are not needed to form it (if `k ≥ n` the set
is empty, since the prefix then has length `n < k + 1`).

## References

* [Mazur, *Collatz positive density*], §13.1.
-/

@[expose] public section

namespace CollatzPosDens

/-- The slice gate `Sl(n, k, l)`: the words `w` of length `n` whose prefix `w_{≤ k+1}` of
length `k + 1` lies in the head gate `Hd(n, k, l)`. -/
@[collatz_pos_dens "def_mx_slice_gate"]
noncomputable def mxSliceGate (n k l : ℕ) : Set Word :=
  {w | w.length = n ∧ w.take (k + 1) ∈ mxHeadGate n k l}

/-- The defining condition of the slice gate `Sl(n, k, l)`. -/
theorem mem_mxSliceGate {n k l : ℕ} {w : Word} :
    w ∈ mxSliceGate n k l ↔ w.length = n ∧ w.take (k + 1) ∈ mxHeadGate n k l :=
  Iff.rfl

/-- Every word of the slice gate `Sl(n, k, l)` has length `n`. -/
theorem length_of_mem_mxSliceGate {n k l : ℕ} {w : Word} (hw : w ∈ mxSliceGate n k l) :
    w.length = n :=
  hw.1

/-- The prefix of length `k + 1` of a word of `Sl(n, k, l)` lies in `Hd(n, k, l)`. -/
theorem take_mem_mxHeadGate_of_mem_mxSliceGate {n k l : ℕ} {w : Word}
    (hw : w ∈ mxSliceGate n k l) : w.take (k + 1) ∈ mxHeadGate n k l :=
  hw.2

/-- The slice gate `Sl(n, k, l)` is empty unless `k < n`. -/
theorem mxSliceGate_eq_empty_of_le {n k l : ℕ} (h : n ≤ k) : mxSliceGate n k l = ∅ := by
  ext w
  simp only [mem_mxSliceGate, Set.mem_empty_iff_false, iff_false, not_and]
  intro hn hw
  have := length_of_mem_mxHeadGate hw
  simp only [List.length_take] at this
  omega

end CollatzPosDens
