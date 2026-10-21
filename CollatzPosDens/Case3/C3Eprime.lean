/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Basic.Real.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.StoppingTrace.TrAtoms
public import CollatzPosDens.Case3.C3InitEvent
public import CollatzPosDens.Transfer.S02Xl
public import CollatzPosDens.Transfer.S02Xd

/-!
# The deviation event

Fix `n ≥ 1` and `J = ⌊n/2⌋`. For a Fourier index `ι ∈ 𝔍`, a level `g ∈ ℕ` and a number of
offsets `v ≤ J`, the *deviation event* `Dev_{g,v}(ι)` is the set of atoms
`a = ((r, ℓ), β) ∈ 𝒜_n` for which at least one of the following holds:

* the first passage lies in the initial deviation set: `(r, ℓ) ∈ 𝓘_g(ι)`;
* the first `v` blocks climb high: `l(β¹) + ⋯ + l(βᵛ) ≥ X_l(ι, v)`;
* some partial sum of the first `v` blocks drifts far from slope `1/4`:
  `max_{1 ≤ u ≤ v} |4 ∑_{k ≤ u} j(βᵏ) - ∑_{k ≤ u} l(βᵏ)| ≥ 4 X_d(ι, v)`, the maximum over an empty
  range being `0`.

Here `j(βᵏ)` and `l(βᵏ)` are the coordinates of the block point `bpt(βᵏ)`, `𝓘_g(ι)` is
`c3InitEvent ι g`, and `X_l`, `X_d` are the allowances `Xl`, `Xd`.

## Main definitions

* `CollatzPosDens.c3Exceptional`: the event `Dev_{g,v}(ι)`, a set of atoms of `𝒜_n`.

## Main results

* `CollatzPosDens.mem_c3Exceptional`: the membership criterion.
* `CollatzPosDens.c3Exceptional_subset_trAtoms`: `Dev_{g,v}(ι) ⊆ 𝒜_n`.
* `CollatzPosDens.notMem_c3Exceptional_iff`: an atom of `𝒜_n` lies outside `Dev_{g,v}(ι)` iff all
  three conditions fail.
* `CollatzPosDens.abs_drift_lt_of_notMem_c3Exceptional`: outside `Dev_{g,v}(ι)`, the drift bound
  `|4 ∑_{k ≤ u} j(βᵏ) - ∑_{k ≤ u} l(βᵏ)| < 4 X_d(ι, v)` holds for every `u ≤ v`, including `u = 0`.

## Implementation notes

Atoms are elements of `(ℕ × ℤ) × List (List ℤ × ℤ)`, and membership in `𝒜_n = trAtoms n` is the
first conjunct of the definition. The pair `(r, ℓ)` is read in `ℤ × ℤ`, where `𝓘_g(ι)` lives. The
sums `∑_{k ≤ u}` run over the first `u` blocks `β¹, …, βᵘ`, that is over the list `β.take u`;
they are integers, and are compared with the rational allowances `X_l(ι, v)`, `4 X_d(ι, v)` in `ℝ`.

The condition `max_{1 ≤ u ≤ v} D_u ≥ 4 X_d(ι, v)`, with the maximum over an empty range equal to
`0`, is stated as `∃ u, 1 ≤ u ≤ v ∧ D_u ≥ 4 X_d(ι, v)`. The two agree: for `v ≥ 1` the maximum of a
finite nonempty family is at least `c` iff some member is, and for `v = 0` both are false since
`4 X_d(ι, 0) > 0`.

The hypothesis `v ≤ J` plays no role in the definition and is dropped.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The deviation event `Dev_{g,v}(ι)`: the atoms `a = ((r, ℓ), β)` of `𝒜_n` with
`(r, ℓ) ∈ 𝓘_g(ι)`, or `∑_{k ≤ v} l(βᵏ) ≥ X_l(ι, v)`, or
`|4 ∑_{k ≤ u} j(βᵏ) - ∑_{k ≤ u} l(βᵏ)| ≥ 4 X_d(ι, v)` for some `1 ≤ u ≤ v`, where
`(j(βᵏ), l(βᵏ)) = bpt(βᵏ)`. -/
@[collatz_pos_dens "def_c3_eprime"]
def c3Exceptional (ι : FIndex) (n g v : ℕ) : Set ((ℕ × ℤ) × List (List ℤ × ℤ)) :=
  {a | a ∈ trAtoms n ∧
    (((a.1.1 : ℤ), a.1.2) ∈ c3InitEvent ι g ∨
      (Xl ι v : ℝ) ≤ ((((a.2.take v).map fun b => bkL (chBlockPoint b)).sum : ℤ) : ℝ) ∨
      ∃ u, 1 ≤ u ∧ u ≤ v ∧ 4 * (Xd ι v : ℝ) ≤
        |((4 * ((a.2.take u).map fun b => bkJ (chBlockPoint b)).sum -
          ((a.2.take u).map fun b => bkL (chBlockPoint b)).sum : ℤ) : ℝ)|)}

/-- Membership in the deviation event. -/
theorem mem_c3Exceptional {ι : FIndex} {n g v : ℕ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)} :
    a ∈ c3Exceptional ι n g v ↔ a ∈ trAtoms n ∧
      (((a.1.1 : ℤ), a.1.2) ∈ c3InitEvent ι g ∨
        (Xl ι v : ℝ) ≤ ((((a.2.take v).map fun b => bkL (chBlockPoint b)).sum : ℤ) : ℝ) ∨
        ∃ u, 1 ≤ u ∧ u ≤ v ∧ 4 * (Xd ι v : ℝ) ≤
          |((4 * ((a.2.take u).map fun b => bkJ (chBlockPoint b)).sum -
            ((a.2.take u).map fun b => bkL (chBlockPoint b)).sum : ℤ) : ℝ)|) :=
  Iff.rfl

/-- Membership in the deviation event, for an atom written `((r, ℓ), β)`. -/
@[simp]
theorem mk_mem_c3Exceptional {ι : FIndex} {n g v r : ℕ} {ℓ : ℤ} {β : List (List ℤ × ℤ)} :
    ((r, ℓ), β) ∈ c3Exceptional ι n g v ↔ ((r, ℓ), β) ∈ trAtoms n ∧
      (((r : ℤ), ℓ) ∈ c3InitEvent ι g ∨
        (Xl ι v : ℝ) ≤ ((((β.take v).map fun b => bkL (chBlockPoint b)).sum : ℤ) : ℝ) ∨
        ∃ u, 1 ≤ u ∧ u ≤ v ∧ 4 * (Xd ι v : ℝ) ≤
          |((4 * ((β.take u).map fun b => bkJ (chBlockPoint b)).sum -
            ((β.take u).map fun b => bkL (chBlockPoint b)).sum : ℤ) : ℝ)|) :=
  Iff.rfl

/-- The deviation event consists of atoms of `𝒜_n`. -/
theorem c3Exceptional_subset_trAtoms (ι : FIndex) (n g v : ℕ) : c3Exceptional ι n g v ⊆ trAtoms n :=
  fun _ ha => ha.1

/-- An atom of `𝒜_n` lies outside the deviation event iff all three conditions fail:
`(r, ℓ) ∉ 𝓘_g(ι)`, `∑_{k ≤ v} l(βᵏ) < X_l(ι, v)`, and
`|4 ∑_{k ≤ u} j(βᵏ) - ∑_{k ≤ u} l(βᵏ)| < 4 X_d(ι, v)` for every `1 ≤ u ≤ v`. -/
theorem notMem_c3Exceptional_iff {ι : FIndex} {n g v : ℕ} {a : (ℕ × ℤ) × List (List ℤ × ℤ)}
    (ha : a ∈ trAtoms n) :
    a ∉ c3Exceptional ι n g v ↔
      ((a.1.1 : ℤ), a.1.2) ∉ c3InitEvent ι g ∧
        ((((a.2.take v).map fun b => bkL (chBlockPoint b)).sum : ℤ) : ℝ) < (Xl ι v : ℝ) ∧
        ∀ u, 1 ≤ u → u ≤ v →
          |((4 * ((a.2.take u).map fun b => bkJ (chBlockPoint b)).sum -
            ((a.2.take u).map fun b => bkL (chBlockPoint b)).sum : ℤ) : ℝ)| <
            4 * (Xd ι v : ℝ) := by
  simp only [mem_c3Exceptional, ha, true_and, not_or, not_le, not_exists, not_and]

/-- Outside the deviation event, the drift bound
`|4 ∑_{k ≤ u} j(βᵏ) - ∑_{k ≤ u} l(βᵏ)| < 4 X_d(ι, v)` holds for every `u ≤ v`: for `u ≥ 1` by the
third condition, and for `u = 0` because both sums are empty and `X_d(ι, v) > 0`. -/
theorem abs_drift_lt_of_notMem_c3Exceptional {ι : FIndex} {n g v : ℕ}
    {a : (ℕ × ℤ) × List (List ℤ × ℤ)} (ha : a ∈ trAtoms n) (hex : a ∉ c3Exceptional ι n g v)
    {u : ℕ} (hu : u ≤ v) :
    |((4 * ((a.2.take u).map fun b => bkJ (chBlockPoint b)).sum -
      ((a.2.take u).map fun b => bkL (chBlockPoint b)).sum : ℤ) : ℝ)| < 4 * (Xd ι v : ℝ) := by
  rcases Nat.eq_zero_or_pos u with rfl | hu1
  · have h : (0 : ℝ) < Xd ι v := by exact_mod_cast Xd_pos ι v
    simpa using h
  · exact ((notMem_c3Exceptional_iff ha).1 hex).2.2 u hu1 hu

end CollatzPosDens
