/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.Transfer.Kappa
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrPath
public import CollatzPosDens.StoppingTrace.TrReward

/-!
# The weighted white count dominates the number of white visits

Fix a level `n` and a residue `ξ ∈ G_n`; "white" refers to `(n, ξ, ε_*)`. For a base point
`o ∈ 𝒫`, a block list `β ∈ 𝔅^N` and a time `t ≤ N`, the weighted white count is at least the
number of white points among `x_1(o, β), …, x_t(o, β)`:
```
N^*(o, β; t) ≥ #{i ∈ {1, …, t} : x_i(o, β) is white}.
```
Indeed `x_i(o, β) = x_{i-1}(o, β) + bpt(β^i)` for `1 ≤ i ≤ N`, so the first term of the reward
`rw(x_{i-1}(o, β), β^i)` is the indicator that `x_i(o, β)` is white, and the second term is
nonnegative since `κ_* ≥ 0`; summing over `i` gives the claim.

## Main results

* `CollatzPosDens.card_white_le_trCount`: `#{i ∈ [1, t] : x_i(o, β) white} ≤ N^*(o, β; t)`
  for `t ≤ N`.

## Implementation notes

The statement holds for every base point `o ∈ ℤ × ℤ` and every block list, without the
hypotheses `o ∈ 𝒫` and that the closing letters lie in `{4, 5}`; both are therefore omitted.
The hypothesis `t ≤ N` cannot be dropped, since the path is constant from time `N` on while the
count is not.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §9.1.
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n}

/-- The weighted white count `N^*(o, β; t)` is at least the number of indices `i ∈ {1, …, t}`
for which `x_i(o, β)` is white, for every `t ≤ N`. -/
@[collatz_pos_dens "lem_tr_count_whites"]
theorem card_white_le_trCount (o : ℤ × ℤ) (β : List (List ℤ × ℤ)) {t : ℕ}
    (ht : t ≤ β.length) :
    ((((Finset.Icc 1 t).filter fun i =>
        IsBkWhite n ξ (epsStar : ℝ) (trPath o β i)).card : ℕ) : ℝ) ≤ trCount n ξ o β t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htN : t < β.length := ht
    rw [Finset.card_filter, Finset.sum_Icc_succ_top (by omega), ← Finset.card_filter,
      Nat.cast_add, trCount_succ o β htN, trPath_succ o β htN]
    gcongr
    · exact ih htN.le
    · have := indicator_le_trReward (n := n) (ξ := ξ) (trPath o β t) β[t]
      split_ifs at this ⊢ <;> simpa using this

end CollatzPosDens
