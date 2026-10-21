/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3StageNext
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.StoppingTrace.TrTrace
public import Mathlib.Data.ENat.Basic

/-!
# The stage end index

Fix a level `n`, a residue `ξ ∈ G_n` and a colour scale `ε`. For a sequence `x = (x_u)_{u ∈ ℕ}` of
points with stopping sequence `τ_1(x) < ⋯ < τ_{ν(x)}(x)` (`CollatzPosDens.trStopTime` and
`CollatzPosDens.trNu`), a gap threshold `G` and a run length `d ≥ 1`, the *stage end indices*
`se^{G,d}_{k,t}(x; i) ∈ ℤ_{≥1} ∪ {∞}`, for integers `k ≥ 0`, `1 ≤ t ≤ d` and `i ≥ 1`, are defined
by recursion on `(k, t)` in the lexicographic order, for all `i` at once:
`se^{G,d}_{0,t}(x; i) = i`, and for `k ≥ 1`,
```
se^{G,d}_{k,t}(x; i) = ∞                                                 if ν(x) < i,
se^{G,d}_{k,t}(x; i) = se^{G,d}_{nx_{G,d}(k, t; gap(x_{τ_i(x)}))}(x; i + 1)   if ν(x) ≥ i,
```
where `nx_{G,d}` is the next state of a stage (`CollatzPosDens.trStageNext`) and `gap` is the gap
of a point (`CollatzPosDens.trGap`). Reading the stopping sequence from its `i`-th term on,
`se^{G,d}_{k,t}(x; i)` is the index of the stop at which `k` stages are complete, the state of the
stages moving at each stop `τ_j(x)` according to the gap of the point `x_{τ_j(x)}`; it is `∞` if
the stopping sequence ends first.

## Main definitions

* `CollatzPosDens.trStageEnd n ξ ε G d x k t i`: the stage end index `se^{G,d}_{k,t}(x; i)`.

## Main results

* `CollatzPosDens.trStageEnd_zero`: `se^{G,d}_{0,t}(x; i) = i`.
* `CollatzPosDens.trStageEnd_of_trNu_lt`: `se^{G,d}_{k,t}(x; i) = ∞` for `k ≥ 1` and `ν(x) < i`.
* `CollatzPosDens.trStageEnd_of_trStopTime_eq_some`: the recursion for `k ≥ 1` when
  `τ_i(x) = s` is defined.
* `CollatzPosDens.le_trStageEnd`: `i ≤ se^{G,d}_{k,t}(x; i)`.

## Implementation notes

The value `∞` is the top element of `ℕ∞`, so that the index lies in `ℕ∞`; for `i ≥ 1` it is
`≥ 1` (`CollatzPosDens.le_trStageEnd`). The recursion for `k ≥ 1` is by cases on the stopping
time `τ_i(x)` (an `Option ℕ`): `∞` when it is undefined, which for `i ≥ 1` is the case
`ν(x) < i`, and the recursive value at the gap of `x_{τ_i(x)}` when it is defined. The indices
are defined for every `t, i ∈ ℕ` by well-founded recursion on `(k, t)`
(`CollatzPosDens.trStageNext_lt`), and for every sequence `x` in `ℤ × ℤ` and every colour scale
`ε`; the values of interest are those with `1 ≤ t ≤ d` and `i ≥ 1`. No hypothesis on `G` is
needed.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The stage end indices `se^{G,d}_{k,t}(x; i) ∈ ℕ∞`: `se^{G,d}_{0,t}(x; i) = i`, and for
`k ≥ 1`, `se^{G,d}_{k,t}(x; i) = ∞` if `τ_i(x)` is undefined (for `i ≥ 1`: if `ν(x) < i`), and
`se^{G,d}_{nx_{G,d}(k,t;gap(x_{τ_i(x)}))}(x; i + 1)` otherwise. -/
@[collatz_pos_dens "def_c3_stage_end"]
noncomputable def trStageEnd (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (G : ℤ) (d : ℕ)
    (x : ℕ → ℤ × ℤ) : ℕ → ℕ → ℕ → ℕ∞
  | 0, _, i => i
  | k + 1, t, i =>
    match trStopTime n ξ ε x i with
    | none => ⊤
    | some s =>
      trStageEnd n ξ ε G d x (trStageNext G d (k + 1) t (trGap n ξ ε (x s))).1
        (trStageNext G d (k + 1) t (trGap n ξ ε (x s))).2 (i + 1)
termination_by k t _ => (k, t)
decreasing_by exact trStageNext_lt (Nat.le_add_left 1 k)

variable {n : ℕ} {ξ : ResidueGroup n} {ε : ℝ} {G : ℤ} {d : ℕ} {x : ℕ → ℤ × ℤ}

/-- `se^{G,d}_{0,t}(x; i) = i`. -/
@[simp]
theorem trStageEnd_zero (t i : ℕ) : trStageEnd n ξ ε G d x 0 t i = i := by
  rw [trStageEnd]

/-- If `τ_i(x)` is undefined, then `se^{G,d}_{k,t}(x; i) = ∞` for `k ≥ 1`. -/
theorem trStageEnd_of_trStopTime_eq_none {k : ℕ} (hk : 1 ≤ k) (t : ℕ) {i : ℕ}
    (h : trStopTime n ξ ε x i = none) : trStageEnd n ξ ε G d x k t i = ⊤ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [trStageEnd, h]

/-- If `ν(x) < i`, then `se^{G,d}_{k,t}(x; i) = ∞` for `k ≥ 1`. -/
theorem trStageEnd_of_trNu_lt {k : ℕ} (hk : 1 ≤ k) (t : ℕ) {i : ℕ}
    (h : trNu n ξ ε x < i) : trStageEnd n ξ ε G d x k t i = ⊤ :=
  trStageEnd_of_trStopTime_eq_none hk t (trStopTime_eq_none_iff.2 (Or.inr h))

/-- If `τ_i(x) = s` is defined, then for `k ≥ 1`,
`se^{G,d}_{k,t}(x; i) = se^{G,d}_{nx_{G,d}(k,t;gap(x_s))}(x; i + 1)`. -/
theorem trStageEnd_of_trStopTime_eq_some {k : ℕ} (hk : 1 ≤ k) (t : ℕ) {i s : ℕ}
    (h : trStopTime n ξ ε x i = some s) :
    trStageEnd n ξ ε G d x k t i =
      trStageEnd n ξ ε G d x (trStageNext G d k t (trGap n ξ ε (x s))).1
        (trStageNext G d k t (trGap n ξ ε (x s))).2 (i + 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [trStageEnd, h]

/-- The stage end index from `i` is at least `i`. -/
theorem le_trStageEnd : ∀ k t i : ℕ, (i : ℕ∞) ≤ trStageEnd n ξ ε G d x k t i
  | 0, t, i => by rw [trStageEnd_zero]
  | k + 1, t, i => by
    cases h : trStopTime n ξ ε x i with
    | none => rw [trStageEnd_of_trStopTime_eq_none (Nat.le_add_left 1 k) t h]; exact le_top
    | some s =>
      rw [trStageEnd_of_trStopTime_eq_some (Nat.le_add_left 1 k) t h]
      refine le_trans ?_ (le_trStageEnd _ _ (i + 1))
      exact_mod_cast Nat.le_succ i
termination_by k t _ => (k, t)
decreasing_by exact trStageNext_lt (Nat.le_add_left 1 k)

end CollatzPosDens
