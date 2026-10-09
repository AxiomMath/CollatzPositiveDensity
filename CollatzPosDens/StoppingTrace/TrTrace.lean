/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Find
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.StoppingTrace.TrHit

/-!
# The stopping sequence

Fix a level `n`, a residue `ξ ∈ G_n` and a colour scale `ε`, and put `J = ⌊n/2⌋`. For a sequence
`x = (x_t)_{t ∈ ℕ}` of points, with hits and hits after a time as in `IsTrHit` and `IsTrHitAfter`
(a time `t` is a hit if `x_t` is black, and a hit after `t'` if moreover `l(x_t) > l_*(x_{t'})`),
the *stopping sequence* of `x` is the strictly increasing sequence `τ_1(x) < ⋯ < τ_{ν(x)}(x)` of
elements of `{0, …, J - 1}` defined recursively: if no `t < J` is a hit then `ν(x) = 0`; otherwise
`τ_1(x)` is the least hit `t < J`; and once `τ_i(x)` is defined, `τ_{i+1}(x)` is the least `t`
with `τ_i(x) < t < J` that is a hit of `x` after `τ_i(x)`, and `ν(x) = i` if there is no such `t`.

## Main definitions

* `CollatzPosDens.trFirstStop`: the least hit `t < J`, when it exists.
* `CollatzPosDens.trNextStop`: the least `t` with `t' < t < J` that is a hit after `t'`,
  when it exists.
* `CollatzPosDens.trStopTime`: `τ_i(x)`, as an `Option ℕ` which is `some` exactly when
  `τ_i(x)` is defined.
* `CollatzPosDens.trNu`: the length `ν(x)` of the stopping sequence.

## Main results

* `CollatzPosDens.trStopTime_one`, `CollatzPosDens.trStopTime_succ_succ`: the recursion.
* `CollatzPosDens.trStopTime_one_eq_some_iff`,
  `CollatzPosDens.trStopTime_succ_succ_eq_some_iff`: `τ_1(x)` and `τ_{i+1}(x)` characterised
  as least hits.
* `CollatzPosDens.trStopTime_lt`, `CollatzPosDens.trStopTime_lt_trStopTime`: the
  stopping times lie below `J` and increase strictly.
* `CollatzPosDens.isTrHit_of_trStopTime_eq_some`: every stopping time is a hit, i.e.
  `x_{τ_i(x)}` is black.
* `CollatzPosDens.isSome_trStopTime_iff`: `τ_i(x)` is defined iff `1 ≤ i ≤ ν(x)`.
* `CollatzPosDens.trNu_le`, `CollatzPosDens.trNu_eq_zero_iff`,
  `CollatzPosDens.one_le_trNu_iff`.

## Implementation notes

The partially defined `τ_i(x)` is a total function `ℕ → Option ℕ`, with value `none` where the
source leaves `τ_i(x)` undefined (in particular at `i = 0`). The length `ν(x)` is the least `i`
with `τ_{i+1}(x)` undefined; such an `i` exists because the defined stopping times increase
strictly inside `{0, …, J - 1}`. The predicate `IsTrHitAfter` does not contain the side
condition `t' < t`, so it is imposed explicitly in `trNextStop`. The hypotheses `n ≥ 1` and
`ε = ε_*` play no role in the definition and are dropped, and `x` is any sequence in
`ℤ × ℤ ⊇ 𝒫`; both generalize the source.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.2.
-/

@[expose] public section

namespace CollatzPosDens

variable (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℕ → ℤ × ℤ)

open scoped Classical in
/-- The least hit `t < ⌊n/2⌋` of `x`, if there is one. -/
@[collatz_pos_dens "def_tr_trace"]
noncomputable def trFirstStop : Option ℕ :=
  if h : ∃ t, t < n / 2 ∧ IsTrHit n ξ ε x t then some (Nat.find h) else none

open scoped Classical in
/-- The least `t` with `t' < t < ⌊n/2⌋` that is a hit of `x` after `t'`, if there is one. -/
@[collatz_pos_dens "def_tr_trace"]
noncomputable def trNextStop (t' : ℕ) : Option ℕ :=
  if h : ∃ t, t < n / 2 ∧ (t' < t ∧ IsTrHitAfter n ξ ε x t' t) then some (Nat.find h) else none

/-- The stopping time `τ_i(x)`, equal to `none` when it is undefined: `τ_0` is undefined,
`τ_1(x)` is the least hit `t < ⌊n/2⌋`, and `τ_{i+1}(x)` is the least `t` with
`τ_i(x) < t < ⌊n/2⌋` that is a hit of `x` after `τ_i(x)`. -/
@[collatz_pos_dens "def_tr_trace"]
noncomputable def trStopTime : ℕ → Option ℕ
  | 0 => none
  | 1 => trFirstStop n ξ ε x
  | i + 2 => (trStopTime (i + 1)).bind (trNextStop n ξ ε x)

variable {n ξ ε x}

private theorem dite_find_eq_some_iff {N : ℕ} {P : ℕ → Prop}
    [Decidable (∃ t, t < N ∧ P t)] [DecidablePred fun t => t < N ∧ P t] {t : ℕ} :
    (if h : ∃ t, t < N ∧ P t then some (Nat.find h) else none) = some t ↔
      t < N ∧ P t ∧ ∀ s < t, ¬P s := by
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · rintro rfl
      exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2,
        fun s hs hs' => Nat.find_min h hs ⟨hs.trans (Nat.find_spec h).1, hs'⟩⟩
    · rintro ⟨ht, hh, hmin⟩
      refine le_antisymm (Nat.find_min' h ⟨ht, hh⟩) (not_lt.1 fun hlt => ?_)
      exact hmin _ hlt (Nat.find_spec h).2
  · simp only [false_iff]
    rintro ⟨ht, hh, -⟩
    exact h ⟨t, ht, hh⟩

/-- The least hit below `⌊n/2⌋` is `t` iff `t < ⌊n/2⌋` is a hit of `x` and no `s < t` is. -/
theorem trFirstStop_eq_some_iff {t : ℕ} :
    trFirstStop n ξ ε x = some t ↔
      t < n / 2 ∧ IsTrHit n ξ ε x t ∧ ∀ s < t, ¬IsTrHit n ξ ε x s := by
  classical
  exact dite_find_eq_some_iff

/-- There is no least hit below `⌊n/2⌋` iff no `t < ⌊n/2⌋` is a hit of `x`. -/
theorem trFirstStop_eq_none_iff :
    trFirstStop n ξ ε x = none ↔ ∀ t < n / 2, ¬IsTrHit n ξ ε x t := by
  classical
  unfold trFirstStop
  split_ifs with h <;> simpa using h

/-- The next stop after `t'` is `t` iff `t' < t < ⌊n/2⌋`, `t` is a hit of `x` after `t'`, and no
`s` with `t' < s < t` is. -/
theorem trNextStop_eq_some_iff {t' t : ℕ} :
    trNextStop n ξ ε x t' = some t ↔
      t < n / 2 ∧ (t' < t ∧ IsTrHitAfter n ξ ε x t' t) ∧
        ∀ s < t, ¬(t' < s ∧ IsTrHitAfter n ξ ε x t' s) := by
  classical
  exact dite_find_eq_some_iff

/-- There is no next stop after `t'` iff no `t` with `t' < t < ⌊n/2⌋` is a hit of `x` after
`t'`. -/
theorem trNextStop_eq_none_iff {t' : ℕ} :
    trNextStop n ξ ε x t' = none ↔
      ∀ t < n / 2, t' < t → ¬IsTrHitAfter n ξ ε x t' t := by
  classical
  unfold trNextStop
  split_ifs with h <;> simpa using h

/-- The least hit below `⌊n/2⌋`, when it exists, is less than `⌊n/2⌋`. -/
theorem trFirstStop_lt {t : ℕ} (h : trFirstStop n ξ ε x = some t) : t < n / 2 :=
  (trFirstStop_eq_some_iff.1 h).1

/-- The next stop after `t'`, when it exists, lies strictly between `t'` and `⌊n/2⌋`. -/
theorem trNextStop_lt {t' t : ℕ} (h : trNextStop n ξ ε x t' = some t) :
    t' < t ∧ t < n / 2 :=
  ⟨(trNextStop_eq_some_iff.1 h).2.1.1, (trNextStop_eq_some_iff.1 h).1⟩

/-- The stopping time `τ_0(x)` is undefined. -/
@[simp]
theorem trStopTime_zero : trStopTime n ξ ε x 0 = none := rfl

/-- `τ_1(x)` is the least hit below `⌊n/2⌋`. -/
theorem trStopTime_one : trStopTime n ξ ε x 1 = trFirstStop n ξ ε x := rfl

/-- `τ_{i+2}(x)` is the next stop after `τ_{i+1}(x)`, and is undefined when `τ_{i+1}(x)` is. -/
theorem trStopTime_succ_succ (i : ℕ) :
    trStopTime n ξ ε x (i + 2) = (trStopTime n ξ ε x (i + 1)).bind (trNextStop n ξ ε x) := rfl

/-- `τ_1(x) = t` iff `t` is the least hit `t < ⌊n/2⌋` of `x`. -/
theorem trStopTime_one_eq_some_iff {t : ℕ} :
    trStopTime n ξ ε x 1 = some t ↔
      t < n / 2 ∧ IsTrHit n ξ ε x t ∧ ∀ s < t, ¬IsTrHit n ξ ε x s :=
  trFirstStop_eq_some_iff

/-- `τ_1(x)` is undefined iff no `t < ⌊n/2⌋` is a hit of `x`. -/
theorem trStopTime_one_eq_none_iff :
    trStopTime n ξ ε x 1 = none ↔ ∀ t < n / 2, ¬IsTrHit n ξ ε x t :=
  trFirstStop_eq_none_iff

/-- `τ_{i+2}(x) = t` iff `τ_{i+1}(x) = t'` is defined and `t` is the least `t` with
`t' < t < ⌊n/2⌋` that is a hit of `x` after `t'`. -/
theorem trStopTime_succ_succ_eq_some_iff {i t : ℕ} :
    trStopTime n ξ ε x (i + 2) = some t ↔
      ∃ t', trStopTime n ξ ε x (i + 1) = some t' ∧ t < n / 2 ∧
        (t' < t ∧ IsTrHitAfter n ξ ε x t' t) ∧
        ∀ s < t, ¬(t' < s ∧ IsTrHitAfter n ξ ε x t' s) := by
  simp only [trStopTime_succ_succ, Option.bind_eq_some_iff, trNextStop_eq_some_iff]

/-- If `τ_{i+1}(x) = t'` is defined, then `τ_{i+2}(x)` is undefined iff no `t` with
`t' < t < ⌊n/2⌋` is a hit of `x` after `t'`. -/
theorem trStopTime_succ_succ_eq_none_iff {i t' : ℕ} (h : trStopTime n ξ ε x (i + 1) = some t') :
    trStopTime n ξ ε x (i + 2) = none ↔
      ∀ t < n / 2, t' < t → ¬IsTrHitAfter n ξ ε x t' t := by
  rw [trStopTime_succ_succ, h, Option.bind_some, trNextStop_eq_none_iff]

/-- Every defined stopping time lies in `{0, …, ⌊n/2⌋ - 1}`. -/
theorem trStopTime_lt {i t : ℕ} (h : trStopTime n ξ ε x i = some t) : t < n / 2 := by
  match i, h with
  | 1, h => exact trFirstStop_lt h
  | i + 2, h =>
    obtain ⟨t', -, h'⟩ := Option.bind_eq_some_iff.1 h
    exact (trNextStop_lt h').2

/-- Every defined stopping time is a hit: `x_{τ_i(x)}` is black. -/
theorem isTrHit_of_trStopTime_eq_some {i t : ℕ} (h : trStopTime n ξ ε x i = some t) :
    IsTrHit n ξ ε x t := by
  match i, h with
  | 1, h => exact (trFirstStop_eq_some_iff.1 h).2.1
  | i + 2, h =>
    obtain ⟨t', -, h'⟩ := Option.bind_eq_some_iff.1 h
    exact (trNextStop_eq_some_iff.1 h').2.1.2.isTrHit

/-- The defined stopping times increase strictly: `τ_{i+1}(x) < τ_{i+2}(x)` whenever both are
defined. -/
theorem trStopTime_lt_trStopTime {i t t' : ℕ} (h : trStopTime n ξ ε x (i + 1) = some t)
    (h' : trStopTime n ξ ε x (i + 2) = some t') : t < t' := by
  obtain ⟨s, hs, hs'⟩ := Option.bind_eq_some_iff.1 h'
  obtain rfl := Option.some_inj.1 (h.symm.trans hs)
  exact (trNextStop_lt hs').1

/-- The stopping time `τ_{i+1}(x)`, when defined, is at least `i`. -/
theorem le_of_trStopTime_eq_some {i t : ℕ} (h : trStopTime n ξ ε x (i + 1) = some t) :
    i ≤ t := by
  induction i generalizing t with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    obtain ⟨s, hs, hs'⟩ := Option.bind_eq_some_iff.1 h
    have := (trNextStop_lt hs').1
    have := ih hs
    omega

/-- Once undefined (at an index `i ≥ 1`), the stopping time stays undefined. -/
theorem trStopTime_succ_eq_none {i : ℕ} (h : trStopTime n ξ ε x (i + 1) = none) :
    trStopTime n ξ ε x (i + 2) = none := by
  rw [trStopTime_succ_succ, h, Option.bind_none]

/-- If `τ_{i+1}(x)` is undefined, then so is `τ_{k+1}(x)` for every `k ≥ i`. -/
theorem trStopTime_eq_none_of_le {i k : ℕ} (h : trStopTime n ξ ε x (i + 1) = none)
    (hik : i ≤ k) : trStopTime n ξ ε x (k + 1) = none := by
  induction k, hik using Nat.le_induction with
  | base => exact h
  | succ k _ ih => exact trStopTime_succ_eq_none ih

/-- There is no stopping time beyond `⌊n/2⌋`: `τ_{⌊n/2⌋+1}(x)` is undefined. -/
theorem trStopTime_div_two_succ : trStopTime n ξ ε x (n / 2 + 1) = none := by
  rcases hτ : trStopTime n ξ ε x (n / 2 + 1) with _ | t
  · rfl
  · have h1 := le_of_trStopTime_eq_some hτ
    have h2 := trStopTime_lt hτ
    omega

/-- Some stopping time `τ_{i+1}(x)` is undefined. -/
theorem exists_trStopTime_eq_none : ∃ i, trStopTime n ξ ε x (i + 1) = none :=
  ⟨n / 2, trStopTime_div_two_succ⟩

open scoped Classical in
/-- The length `ν(x)` of the stopping sequence: the least `i` such that `τ_{i+1}(x)` is
undefined. -/
@[collatz_pos_dens "def_tr_trace"]
noncomputable def trNu (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℕ → ℤ × ℤ) : ℕ :=
  Nat.find (exists_trStopTime_eq_none (n := n) (ξ := ξ) (ε := ε) (x := x))

/-- The stopping time `τ_{ν(x)+1}(x)` is undefined. -/
theorem trStopTime_trNu_succ : trStopTime n ξ ε x (trNu n ξ ε x + 1) = none := by
  classical
  exact Nat.find_spec (exists_trStopTime_eq_none (n := n) (ξ := ξ) (ε := ε) (x := x))

/-- The stopping time `τ_i(x)` is defined iff `1 ≤ i ≤ ν(x)`. -/
theorem isSome_trStopTime_iff {i : ℕ} :
    (trStopTime n ξ ε x i).isSome ↔ 1 ≤ i ∧ i ≤ trNu n ξ ε x := by
  classical
  constructor
  · intro h
    obtain _ | i := i
    · simp at h
    refine ⟨Nat.succ_pos _, Nat.succ_le_of_lt (not_le.1 fun hle => ?_)⟩
    rw [trStopTime_eq_none_of_le trStopTime_trNu_succ hle] at h
    simp at h
  · rintro ⟨h1, h2⟩
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' h1
    rw [Option.isSome_iff_ne_none]
    exact Nat.find_min (exists_trStopTime_eq_none (n := n) (ξ := ξ) (ε := ε) (x := x))
      (Nat.lt_of_succ_le h2)

/-- The stopping time `τ_i(x)` is undefined iff `i = 0` or `ν(x) < i`. -/
theorem trStopTime_eq_none_iff {i : ℕ} :
    trStopTime n ξ ε x i = none ↔ i = 0 ∨ trNu n ξ ε x < i := by
  rw [← Option.not_isSome_iff_eq_none, isSome_trStopTime_iff]
  omega

/-- The stopping sequence has at most `⌊n/2⌋` terms. -/
theorem trNu_le : trNu n ξ ε x ≤ n / 2 := by
  classical
  exact Nat.find_min' _ trStopTime_div_two_succ

/-- `ν(x) = 0` iff no time `t < ⌊n/2⌋` is a hit of `x`. -/
theorem trNu_eq_zero_iff : trNu n ξ ε x = 0 ↔ ∀ t < n / 2, ¬IsTrHit n ξ ε x t := by
  rw [← trStopTime_one_eq_none_iff, trStopTime_eq_none_iff]
  omega

/-- `ν(x) ≥ 1` iff some time `t < ⌊n/2⌋` is a hit of `x`. -/
theorem one_le_trNu_iff : 1 ≤ trNu n ξ ε x ↔ ∃ t < n / 2, IsTrHit n ξ ε x t := by
  rw [Nat.one_le_iff_ne_zero, Ne, trNu_eq_zero_iff]
  push Not
  rfl

/-- If `τ_{i+1}(x) = t'` is defined, then `ν(x) = i + 1` iff no `t` with `t' < t < ⌊n/2⌋` is a
hit of `x` after `t'`. -/
theorem trNu_eq_iff_of_trStopTime_eq_some {i t' : ℕ}
    (h : trStopTime n ξ ε x (i + 1) = some t') :
    trNu n ξ ε x = i + 1 ↔ ∀ t < n / 2, t' < t → ¬IsTrHitAfter n ξ ε x t' t := by
  rw [← trStopTime_succ_succ_eq_none_iff h, trStopTime_eq_none_iff]
  have := (isSome_trStopTime_iff (n := n) (ξ := ξ) (ε := ε) (x := x) (i := i + 1)).1
    (by simp [h])
  omega

end CollatzPosDens
