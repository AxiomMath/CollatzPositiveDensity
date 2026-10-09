/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrReward
public import Mathlib.Data.List.GetD

/-!
# The weighted white count along a block list

Fix a level `n` and a residue `ξ ∈ G_n`, and let `rw = CollatzPosDens.trReward n ξ` be the block
reward of `CollatzPosDens.trReward`, which counts white points in the sense of
`CollatzPosDens.IsBkWhite n ξ ε_*` with `ε_* = CollatzPosDens.epsStar`. For a base point
`o ∈ 𝒫`, a block list `β = (β¹, …, β^N) ∈ 𝔅^N` and a time `t ∈ ℕ`, the *weighted white count*
```
N^*(o, β; t) = ∑_{i = 1}^{min(t, N)} rw(x_{i-1}(o, β), β^i)
```
adds up the rewards of the first `min(t, N)` blocks of `β`, each block being rewarded at the
point of the path `x(o, β)` where it is read.

## Main definitions

* `CollatzPosDens.trCount n ξ o β t`: the weighted white count `N^*(o, β; t) ∈ ℝ`.

## Main results

* `CollatzPosDens.trCount_zero`: `N^*(o, β; 0) = 0`.
* `CollatzPosDens.trCount_succ`: `N^*(o, β; t + 1) = N^*(o, β; t) + rw(x_t(o, β), β^{t+1})`
  for `t < N`.
* `CollatzPosDens.trCount_of_length_le`: `N^*(o, β; t) = N^*(o, β; N)` for `t ≥ N`.
* `CollatzPosDens.trCount_cons_succ`:
  `N^*(o, b :: β; t + 1) = rw(o, b) + N^*(o + bpt(b), β; t)`.
* `CollatzPosDens.trCount_append_of_le`: `N^*(o, β ++ γ; t) = N^*(o, β; t)` for `t ≤ |β|`.
* `CollatzPosDens.trCount_nonneg`, `CollatzPosDens.trCount_mono`: the count is
  nonnegative and nondecreasing in `t`.

## Implementation notes

As for `CollatzPosDens.trPath`, a list `β ∈ 𝔅^N` is a `List (List ℤ × ℤ)` with
`N = β.length` and the base point is any `o ∈ ℤ × ℤ`. The sum over `i ∈ {1, …, min(t, N)}` is
reindexed as a sum over `i ∈ {0, …, min(t, N) - 1}` of `rw(x_i(o, β), β^{i+1})`, and the block
`β^{i+1}` is `β.getD i ([], 0)`; the default value is never used since `i < N` throughout.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The weighted white count `N^*(o, β; t) = ∑_{i=1}^{min(t, N)} rw(x_{i-1}(o, β), β^i)` of a
block list `β ∈ 𝔅^N` from the base point `o`, up to time `t`, where "white" refers to
`(n, ξ, ε_*)`. -/
@[collatz_pos_dens "def_tr_count"]
noncomputable def trCount (n : ℕ) (ξ : ResidueGroup n) (o : ℤ × ℤ) (β : List (List ℤ × ℤ))
    (t : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (min t β.length), trReward n ξ (trPath o β i) (β.getD i ([], 0))

variable {n : ℕ} {ξ : ResidueGroup n}

/-- `N^*(o, β; t)` is the sum over `i < min(t, N)` of `rw(x_i(o, β), β^{i+1})`. -/
lemma trCount_def (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) (t : ℕ) :
    trCount n ξ o β t =
      ∑ i ∈ Finset.range (min t β.length), trReward n ξ (trPath o β i) (β.getD i ([], 0)) :=
  rfl

/-- `N^*(o, β; 0) = 0`. -/
@[simp]
lemma trCount_zero (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) : trCount n ξ o β 0 = 0 := by
  simp [trCount]

/-- The count along the empty list vanishes. -/
@[simp]
lemma trCount_nil (o : ℤ × ℤ) (t : ℕ) : trCount n ξ o [] t = 0 := by
  simp [trCount]

/-- `N^*(o, β; t + 1) = N^*(o, β; t) + rw(x_t(o, β), β^{t+1})` for `t < N`. -/
lemma trCount_succ (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) {t : ℕ} (ht : t < β.length) :
    trCount n ξ o β (t + 1) = trCount n ξ o β t + trReward n ξ (trPath o β t) β[t] := by
  rw [trCount_def, trCount_def, min_eq_left (Nat.succ_le_of_lt ht), min_eq_left ht.le,
    Finset.sum_range_succ, List.getD_eq_getElem _ _ ht]

/-- From time `N` on, the count stays at `N^*(o, β; N)`. -/
lemma trCount_of_length_le (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) {t : ℕ} (ht : β.length ≤ t) :
    trCount n ξ o β t = trCount n ξ o β β.length := by
  rw [trCount_def, trCount_def, min_eq_right ht, min_self]

/-- Reading the first block: `N^*(o, b :: β; t + 1) = rw(o, b) + N^*(o + bpt(b), β; t)`. -/
lemma trCount_cons_succ (o : ℤ × ℤ) (b : List ℤ × ℤ) (β : List (List ℤ × ℤ)) (t : ℕ) :
    trCount n ξ o (b :: β) (t + 1) = trReward n ξ o b + trCount n ξ (o + chBlockPoint b) β t := by
  rw [trCount_def, trCount_def, List.length_cons, Nat.add_min_add_right,
    Finset.sum_range_succ', add_comm]
  simp only [trPath_cons_succ, trPath_zero, List.getD_cons_succ, List.getD_cons_zero]

/-- Along a concatenation, for `t ≤ |β|`, `N^*(o, β ++ γ; t) = N^*(o, β; t)`. -/
lemma trCount_append_of_le (o : ℤ × ℤ) (β γ : List (List ℤ × ℤ)) {t : ℕ} (ht : t ≤ β.length) :
    trCount n ξ o (β ++ γ) t = trCount n ξ o β t := by
  rw [trCount_def, trCount_def, List.length_append, min_eq_left ht,
    min_eq_left (ht.trans (Nat.le_add_right _ _))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi : i < β.length := (Finset.mem_range.1 hi).trans_le ht
  rw [trPath_append_of_le o β γ hi.le, List.getD_append _ _ _ _ hi]

/-- The weighted white count is nonnegative. -/
lemma trCount_nonneg (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) (t : ℕ) : 0 ≤ trCount n ξ o β t :=
  Finset.sum_nonneg fun _ _ => trReward_nonneg _ _

/-- The weighted white count is nondecreasing in time. -/
lemma trCount_mono (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) : Monotone (trCount n ξ o β) :=
  fun _ _ hst => Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (min_le_min_right _ hst)) fun _ _ _ => trReward_nonneg _ _

end CollatzPosDens
