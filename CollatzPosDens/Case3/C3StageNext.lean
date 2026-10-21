/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Algebra.Order.Ring.Int

/-!
# The next state of a stage

A *stage* with parameters `G ≥ 0` (the gap threshold) and `d ≥ 1` (the length of a run of small
gaps) is driven by a state `(k, t)`, where `k` counts the stages still to be completed and
`1 ≤ t ≤ d` the departures from points of gap less than `G` still allowed in the current stage.
Departing from a point of gap `s`, the state moves to
```
nx_{G,d}(k, t; s) = (k - 1, d)   if s ≥ G or t = 1,
nx_{G,d}(k, t; s) = (k, t - 1)   otherwise,
```
an element of `ℕ × {1, …, d}`. For `k ≥ 1` the next state precedes `(k, t)` in the lexicographic
order.

## Main definitions

* `CollatzPosDens.trStageNext G d k t s`: the next state `nx_{G,d}(k, t; s)`.

## Main results

* `CollatzPosDens.trStageNext_of_le`, `CollatzPosDens.trStageNext_one`,
  `CollatzPosDens.trStageNext_of_lt`: the three cases of the definition.
* `CollatzPosDens.trStageNext_mem`: for `1 ≤ t ≤ d`, the second coordinate stays in
  `{1, …, d}`.
* `CollatzPosDens.trStageNext_lt`: for `k ≥ 1` the next state precedes `(k, t)`
  lexicographically.

## Implementation notes

The integers `k ≥ 0` and `1 ≤ t ≤ d` are natural numbers, and the threshold `G` and the gap `s`
are integers. The definition is extended to every `t ∈ ℕ` by testing `t ≤ 1` in place of
`t = 1`; on `1 ≤ t ≤ d` the two agree, and with this extension the next state of `(k, t)`
precedes it for every `k ≥ 1` and every `t`. The hypothesis `G ≥ 0` plays no role and is
dropped.

## References

* [Mazur, *Collatz positive density*], §10.4.
-/

@[expose] public section

namespace CollatzPosDens

/-- The next state `nx_{G,d}(k, t; s)` of a stage: `(k - 1, d)` if `s ≥ G` or `t = 1`, and
`(k, t - 1)` otherwise. (For `t = 0`, outside the range `1 ≤ t ≤ d`, it is `(k - 1, d)`.) -/
@[collatz_pos_dens "def_c3_stage_next"]
def trStageNext (G : ℤ) (d k t : ℕ) (s : ℤ) : ℕ × ℕ :=
  if G ≤ s ∨ t ≤ 1 then (k - 1, d) else (k, t - 1)

variable {G : ℤ} {d k t : ℕ} {s : ℤ}

/-- At a gap `s ≥ G` the stage is complete: `nx_{G,d}(k, t; s) = (k - 1, d)`. -/
theorem trStageNext_of_le (h : G ≤ s) : trStageNext G d k t s = (k - 1, d) :=
  ite_eq_left (Or.inl h)

/-- With `t = 1` the stage is complete: `nx_{G,d}(k, 1; s) = (k - 1, d)`. -/
theorem trStageNext_one : trStageNext G d k 1 s = (k - 1, d) :=
  ite_eq_left (Or.inr le_rfl)

/-- At a gap `s < G` with `t ≥ 2`, one departure is used: `nx_{G,d}(k, t; s) = (k, t - 1)`. -/
theorem trStageNext_of_lt (h : s < G) (ht : 2 ≤ t) : trStageNext G d k t s = (k, t - 1) :=
  ite_eq_right (by omega)

/-- The next state is `(k - 1, d)` or `(k, t - 1)`. -/
theorem trStageNext_eq_or :
    trStageNext G d k t s = (k - 1, d) ∨ trStageNext G d k t s = (k, t - 1) := by
  unfold trStageNext
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- For `1 ≤ t ≤ d`, the next state lies in `ℕ × {1, …, d}`. -/
theorem trStageNext_mem (ht : 1 ≤ t) (htd : t ≤ d) :
    1 ≤ (trStageNext G d k t s).2 ∧ (trStageNext G d k t s).2 ≤ d := by
  unfold trStageNext
  split_ifs with h
  · exact ⟨ht.trans htd, le_rfl⟩
  · simp only
    omega

/-- For `k ≥ 1` the next state `nx_{G,d}(k, t; s)` precedes `(k, t)` in the lexicographic
order. -/
theorem trStageNext_lt (hk : 1 ≤ k) :
    Prod.Lex (· < ·) (· < ·) (trStageNext G d k t s) (k, t) := by
  unfold trStageNext
  split_ifs with h
  · exact Prod.Lex.left _ _ (by omega)
  · exact Prod.Lex.right _ (by omega)

end CollatzPosDens
