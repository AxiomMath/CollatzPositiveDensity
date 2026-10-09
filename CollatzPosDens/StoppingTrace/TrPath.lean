/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.CharSum.ChBlockPath

/-!
# The path of a block list

For a base point `o ∈ 𝒫`, a list of blocks `β = (β¹, …, β^N) ∈ 𝔅^N` and a time `t ∈ ℕ`, the
path of `β` from `o` is `x_t(o, β) = o + Bp_{min(t, N)}(β)`: the lattice point reached after
reading the first `min(t, N)` blocks of `β` starting from `o`. It starts at `x_0(o, β) = o`,
moves by `x_{t+1}(o, β) = x_t(o, β) + bpt(β^{t+1})` while `t < N`, and stays at
`x_N(o, β)` from time `N` on. Since the first coordinate of every block path point is
nonnegative, the path never leaves `𝒫` when it starts in `𝒫`.

## Main definitions

* `CollatzPosDens.trPath`: the path point `x_t(o, β) = o + Bp_{min(t, N)}(β)`.

## Main results

* `CollatzPosDens.trPath_zero`: `x_0(o, β) = o`.
* `CollatzPosDens.trPath_succ`: `x_{t+1}(o, β) = x_t(o, β) + bpt(β^{t+1})` for `t < N`.
* `CollatzPosDens.trPath_of_length_le`: `x_t(o, β) = x_N(o, β)` for `t ≥ N`.
* `CollatzPosDens.trPath_cons_succ`: `x_{t+1}(o, b :: β) = x_t(o + bpt(b), β)`.
* `CollatzPosDens.trPath_mem_bkPoints`: if `o ∈ 𝒫` then `x_t(o, β) ∈ 𝒫`.

## Implementation notes

Following `chBlockPath`, a list `β ∈ 𝔅^N` is a `List (List ℤ × ℤ)` with `N = β.length`, and
the base point is any `o ∈ ℤ × ℤ`, so `trPath` takes values in `ℤ × ℤ`. The membership
`x_t(o, β) ∈ 𝒫` for `o ∈ 𝒫` is the separate statement `trPath_mem_bkPoints`. The truncation
`min(t, N)` is kept in the definition, although `chBlockPath` is already constant beyond the
length of the list (`trPath_eq_add_chBlockPath`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The path `x_t(o, β) = o + Bp_{min(t, N)}(β)` of a block list `β ∈ 𝔅^N` from the base
point `o`, at time `t`. -/
@[collatz_pos_dens "def_tr_path"]
def trPath (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) (t : ℕ) : ℤ × ℤ :=
  o + chBlockPath β (min t β.length)

/-- `x_t(o, β) = o + Bp_{min(t, N)}(β)`. -/
lemma trPath_def (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) (t : ℕ) :
    trPath o β t = o + chBlockPath β (min t β.length) :=
  rfl

/-- The truncation is redundant: `x_t(o, β) = o + Bp_t(β)`. -/
lemma trPath_eq_add_chBlockPath (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) (t : ℕ) :
    trPath o β t = o + chBlockPath β t := by
  rcases le_total t β.length with h | h
  · rw [trPath_def, min_eq_left h]
  · rw [trPath_def, min_eq_right h, chBlockPath_of_length_le β h,
      chBlockPath_of_length_le β le_rfl]

/-- `x_0(o, β) = o`. -/
@[simp]
lemma trPath_zero (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) : trPath o β 0 = o := by
  simp [trPath]

/-- The path of the empty list is constant. -/
@[simp]
lemma trPath_nil (o : ℤ × ℤ) (t : ℕ) : trPath o [] t = o := by
  simp [trPath]

/-- `x_{t+1}(o, β) = x_t(o, β) + bpt(β^{t+1})` for `t < N`. -/
lemma trPath_succ (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) {t : ℕ} (ht : t < β.length) :
    trPath o β (t + 1) = trPath o β t + chBlockPoint β[t] := by
  rw [trPath_eq_add_chBlockPath, trPath_eq_add_chBlockPath, chBlockPath_succ β ht, add_assoc]

/-- From time `N` on, the path stays at `x_N(o, β)`. -/
lemma trPath_of_length_le (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) {t : ℕ} (ht : β.length ≤ t) :
    trPath o β t = trPath o β β.length := by
  rw [trPath_def, trPath_def, min_eq_right ht, min_self]

/-- Reading the first block moves the base point: `x_{t+1}(o, b :: β) = x_t(o + bpt(b), β)`. -/
lemma trPath_cons_succ (o : ℤ × ℤ) (b : List ℤ × ℤ) (β : List (List ℤ × ℤ)) (t : ℕ) :
    trPath o (b :: β) (t + 1) = trPath (o + chBlockPoint b) β t := by
  rw [trPath_eq_add_chBlockPath, trPath_eq_add_chBlockPath, chBlockPath_cons_succ, add_assoc]

/-- Along a concatenation, for `t ≤ |β|`, `x_t(o, β ++ γ) = x_t(o, β)`. -/
lemma trPath_append_of_le (o : ℤ × ℤ) (β γ : List (List ℤ × ℤ)) {t : ℕ} (ht : t ≤ β.length) :
    trPath o (β ++ γ) t = trPath o β t := by
  rw [trPath_eq_add_chBlockPath, trPath_eq_add_chBlockPath, chBlockPath_append_of_le β γ ht]

/-- The first coordinate never decreases along the path: `j(o) ≤ j(x_t(o, β))`. -/
lemma trPath_fst_ge (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) (t : ℕ) : o.1 ≤ (trPath o β t).1 := by
  rw [trPath_def, Prod.fst_add]
  linarith [chBlockPath_fst_nonneg β (min t β.length)]

/-- A path starting in `𝒫` stays in `𝒫`. -/
lemma trPath_mem_bkPoints {o : ℤ × ℤ} (ho : o ∈ bkPoints) (β : List (List ℤ × ℤ)) (t : ℕ) :
    trPath o β t ∈ bkPoints :=
  le_trans ho (trPath_fst_ge o β t)

end CollatzPosDens
