/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.StoppingTrace.TrPath

/-!
# Horizontal growth along the path of a block list

Let `o ∈ 𝒫` and `β = (β¹, …, β^N) ∈ 𝔅^N`. Along the path `x_t(o, β) = o + Bp_{min(t, N)}(β)`
the `j`-coordinate grows by at least one per block read: for `t ≤ t'`,
`j(x_{t'}(o, β)) - j(x_t(o, β)) ≥ min(t', N) - min(t, N)`. Indeed the difference is the sum
`j(bpt(β^{min(t,N)+1})) + ⋯ + j(bpt(β^{min(t',N)}))` of `min(t', N) - min(t, N)` terms, and
each block point `bpt(c, e) = (|c| + 1, …)` has first coordinate at least `1`.

## Main results

* `CollatzPosDens.trPath_bkJ_sub_bkJ_ge`: the growth bound.

## Implementation notes

The bound uses neither the hypothesis `o ∈ 𝒫` nor that the closing letters of the blocks lie
in `{4, 5}`: only that block points have first coordinate `|c| + 1 ≥ 1`, which holds for every
block in the model `List ℤ × ℤ`. Both hypotheses are therefore dropped, so the statement holds
for every `o ∈ ℤ × ℤ` and every `β : List (List ℤ × ℤ)`, with `N = β.length`. The integer
`min(t', N) - min(t, N)` is written as a difference of casts of natural numbers.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- Along the path of a block list, the `j`-coordinate grows by at least one per block read:
for `t ≤ t'`, `j(x_{t'}(o, β)) - j(x_t(o, β)) ≥ min(t', N) - min(t, N)` where `N = |β|`. -/
@[collatz_pos_dens "lem_tr_path_growth_j"]
theorem trPath_bkJ_sub_bkJ_ge (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) {t t' : ℕ} (htt : t ≤ t') :
    ((min t' β.length : ℕ) : ℤ) - (min t β.length : ℕ) ≤
      bkJ (trPath o β t') - bkJ (trPath o β t) := by
  induction β generalizing o t t' with
  | nil => simp
  | cons b β ih =>
    have hb : 1 ≤ bkJ (chBlockPoint b) := chBlockPoint_mem_bkPoints b
    cases t' with
    | zero =>
      obtain rfl : t = 0 := by omega
      simp
    | succ t' =>
      cases t with
      | zero =>
        have := ih (o := o + chBlockPoint b) (Nat.zero_le t')
        simp only [trPath_zero, trPath_cons_succ, List.length_cons, Nat.succ_min_succ, bkJ,
          Prod.fst_add, Nat.zero_min] at this hb ⊢
        omega
      | succ t =>
        have := ih (o := o + chBlockPoint b) (Nat.le_of_succ_le_succ htt)
        simp only [trPath_cons_succ, List.length_cons, Nat.succ_min_succ] at this ⊢
        omega

end CollatzPosDens
