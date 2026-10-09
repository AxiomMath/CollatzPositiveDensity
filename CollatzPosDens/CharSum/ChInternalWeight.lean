/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.CharSum.ChRaw3Factor

/-!
# The internal weight of a block

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and let `w₃` be the raw-three factor.
For a point `x ∈ ℕ × ℤ` and a block `β = (c, e)` with `c = (c₁, …, c_m)`, the *internal weight*
of `β` started at `x` is
`I(x; β) = ∏_{1 ≤ i ≤ m, c_i = 3} w₃(x + (i, c₁ + ⋯ + c_i))`,
the empty product being `1`. It collects the factors `w₃` charged to the nonclosing letters `3`
of the block, each evaluated at the lattice point reached by the partial sums of the block when it
is read starting from `x`.

## Main definitions

* `CollatzPosDens.chInternalWeight n ξ ε x β`: the internal weight `I(x; β)`.

## Main results

* `CollatzPosDens.chInternalWeight_nil`: a block with no nonclosing letters has internal
  weight `1`.
* `CollatzPosDens.chInternalWeight_cons`: the recursion
  `I(x; (a :: c, e)) = [a = 3 ? w₃(x + (1, a)) : 1] · I(x + (1, a); (c, e))`.
* `CollatzPosDens.chInternalWeight_pos`, `CollatzPosDens.chInternalWeight_le_one`:
  `0 < I(x; β) ≤ 1`.

## Implementation notes

A block is modelled as `β : List ℤ × ℤ`, as for `chBlockPoint`; the closing letter plays no
role. The point `x` is taken in `ℤ × ℤ`, which generalizes `x ∈ ℕ × ℤ` and matches the type of
the block path `chBlockPath`. The index `i : Fin m` is `0`-based, so the `1`-based index `i + 1`
appears as the first coordinate `i + 1` of the shift, and the partial sum `c₁ + ⋯ + c_{i+1}` is
`(c.take (i + 1)).sum`.
-/

@[expose] public section

namespace CollatzPosDens

/-- The internal weight `I(x; β) = ∏_{1 ≤ i ≤ m, c_i = 3} w₃(x + (i, c₁ + ⋯ + c_i))` of a block
`β = (c, e)` started at `x`, where `w₃` is the raw-three factor for `n, ξ, ε`. -/
@[collatz_pos_dens "def_ch_internal_weight"]
noncomputable def chInternalWeight (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) : ℝ :=
  ∏ i ∈ Finset.univ.filter (fun i : Fin β.1.length => β.1[i] = 3),
    chRaw3Factor n ξ ε (x + ((i : ℤ) + 1, (β.1.take (i + 1)).sum))

/-- The internal weight as an unfiltered product over all nonclosing positions. -/
lemma chInternalWeight_eq_prod_ite (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) :
    chInternalWeight n ξ ε x β =
      ∏ i : Fin β.1.length,
        if β.1[i] = 3 then chRaw3Factor n ξ ε (x + ((i : ℤ) + 1, (β.1.take (i + 1)).sum))
        else 1 := by
  rw [chInternalWeight, Finset.prod_filter]

/-- A block with no nonclosing letters has internal weight `1`. -/
@[simp]
lemma chInternalWeight_nil (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ) (e : ℤ) :
    chInternalWeight n ξ ε x ([], e) = 1 := by
  simp [chInternalWeight]

/-- The recursion for the internal weight: prepending a nonclosing letter `a` contributes the
factor `w₃(x + (1, a))` if `a = 3` (and `1` otherwise), and shifts the start to `x + (1, a)`. -/
lemma chInternalWeight_cons (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ) (a : ℤ)
    (c : List ℤ) (e : ℤ) :
    chInternalWeight n ξ ε x (a :: c, e) =
      (if a = 3 then chRaw3Factor n ξ ε (x + (1, a)) else 1) *
        chInternalWeight n ξ ε (x + (1, a)) (c, e) := by
  rw [chInternalWeight_eq_prod_ite, chInternalWeight_eq_prod_ite]
  simp only [List.length_cons]
  rw [Fin.prod_univ_succ]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Fin.val_succ, List.take_succ_cons, List.sum_cons]
    congr 2
    ext <;> simp <;> ring

/-- The internal weight is positive. -/
lemma chInternalWeight_pos (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) : 0 < chInternalWeight n ξ ε x β :=
  Finset.prod_pos fun _ _ => chRaw3Factor_pos _ _ _ _

/-- The internal weight is nonnegative. -/
lemma chInternalWeight_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) : 0 ≤ chInternalWeight n ξ ε x β :=
  (chInternalWeight_pos n ξ ε x β).le

/-- The internal weight is at most `1`. -/
lemma chInternalWeight_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) : chInternalWeight n ξ ε x β ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => chRaw3Factor_nonneg _ _ _ _)
    fun _ _ => chRaw3Factor_le_one _ _ _ _

/-- The internal weight does not depend on the closing letter. -/
lemma chInternalWeight_closing (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (c : List ℤ) (e e' : ℤ) :
    chInternalWeight n ξ ε x (c, e) = chInternalWeight n ξ ε x (c, e') := rfl

end CollatzPosDens
