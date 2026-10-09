/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxSliceGate

/-!
# Distinct slice gates are disjoint

Let `n ≥ 1` and `k, l, k', l' ∈ ℕ` with `k, k' < n`. If the slice gates `Sl(n, k, l)` and
`Sl(n, k', l')` meet, then `(k, l) = (k', l')`. Indeed, for a common word `w` the prefix sums
`s_i = A(w_{≤ i})` are nondecreasing in `i`, and the two gate conditions read
`s_k ≤ Lv_n < s_{k+1}` and `s_{k'} ≤ Lv_n < s_{k'+1}`. If `k < k'` then
`s_{k+1} ≤ s_{k'} ≤ Lv_n`, a contradiction; symmetrically `k' < k` is impossible. Hence `k = k'`,
and then `l = s_{k+1} = l'`.

## Main results

* `CollatzPosDens.eq_of_mxSliceGate_inter_nonempty`: if `Sl(n, k, l) ∩ Sl(n, k', l') ≠ ∅`
  then `(k, l) = (k', l')`.
* `CollatzPosDens.mxSliceGate_disjoint`: slice gates with distinct indices are disjoint.

## Implementation notes

The hypotheses `n ≥ 1` and `k, k' < n` are not needed: only monotonicity of the prefix sums is
used (which holds for nonnegative letters, not just strictly positive ones), so the statement is
proved for all `n, k, l, k', l'`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If `w ∈ Sl(n, k, l) ∩ Sl(n, k', l')` then `k' ≤ k`: the prefix sums of `w` cross the
level `Lv_n` at most once. -/
private theorem le_of_mem_mxSliceGate_mxGateDisjoint {n k l k' l' : ℕ} {w : Word}
    (hw : w ∈ mxSliceGate n k l) (hw' : w ∈ mxSliceGate n k' l') : k' ≤ k := by
  by_contra! hlt
  have hlt' := (mem_mxHeadGate.mp hw.2).2.2.1.2.1
  have hle := (mem_mxHeadGate.mp hw'.2).2.2.1.1
  rw [List.take_take, Nat.min_eq_left (Nat.le_succ k')] at hle
  have hpre : Word.valSum (w.take (k + 1)) ≤ Word.valSum (w.take k') :=
    Word.valSum_le_of_isPrefix (List.take_prefix_take_left hlt)
  have : (Word.valSum (w.take (k + 1)) : ℝ) ≤ Word.valSum (w.take k') := by exact_mod_cast hpre
  linarith

/-- If the slice gates `Sl(n, k, l)` and `Sl(n, k', l')` meet, then `(k, l) = (k', l')`. -/
@[collatz_pos_dens "lem_mx_gate_disjoint"]
theorem eq_of_mxSliceGate_inter_nonempty {n k l k' l' : ℕ}
    (h : (mxSliceGate n k l ∩ mxSliceGate n k' l').Nonempty) : (k, l) = (k', l') := by
  obtain ⟨w, hw, hw'⟩ := h
  have hk : k = k' := le_antisymm (le_of_mem_mxSliceGate_mxGateDisjoint hw' hw)
    (le_of_mem_mxSliceGate_mxGateDisjoint hw hw')
  subst hk
  rw [← valSum_of_mem_mxHeadGate hw.2, ← valSum_of_mem_mxHeadGate hw'.2]

/-- Slice gates `Sl(n, k, l)` and `Sl(n, k', l')` with `(k, l) ≠ (k', l')` are disjoint. -/
theorem mxSliceGate_disjoint {n k l k' l' : ℕ} (h : (k, l) ≠ (k', l')) :
    Disjoint (mxSliceGate n k l) (mxSliceGate n k' l') :=
  Set.disjoint_iff_inter_eq_empty.mpr <| Set.not_nonempty_iff_eq_empty.mp fun hne =>
    h (eq_of_mxSliceGate_inter_nonempty hne)

/-- The slice gates `Sl(n, k, l)`, indexed by pairs `(k, l)`, are pairwise disjoint. -/
theorem pairwiseDisjoint_mxSliceGate (n : ℕ) (s : Set (ℕ × ℕ)) :
    s.PairwiseDisjoint fun p => mxSliceGate n p.1 p.2 :=
  fun _ _ _ _ hpq => mxSliceGate_disjoint (by simpa using hpq)

end CollatzPosDens
