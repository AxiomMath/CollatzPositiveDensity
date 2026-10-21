/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkWhite
public import CollatzPosDens.CharSum.ChBlockPath
public import CollatzPosDens.CharSum.ChOldReward
public import CollatzPosDens.CharSum.ChPaidRewardGeOld
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
Indeed `x_i(o, β) = x_{i-1}(o, β) + bpt(β^i)` for `1 ≤ i ≤ N`, so the last term of the reward
`rw(x_{i-1}(o, β), β^i)` is the paid reward `R_e(x_i(o, β))` of the closing letter `e ∈ {4, 5}`
of `β^i`. At a white point this is at least the baseline reward `R^old_e(x_i(o, β)) = 1`, and
all other terms of the reward are nonnegative; summing over `i` gives the claim.

## Main results

* `CollatzPosDens.card_white_le_trCount`: `#{i ∈ [1, t] : x_i(o, β) white} ≤ N^*(o, β; t)`
  for `t ≤ N`.

## Implementation notes

The block list `β ∈ 𝔅^N` is a `List (List ℤ × ℤ)` with `N = β.length` whose closing letters
lie in `{4, 5}`; the base point is any `o ∈ ℤ × ℤ`, as the hypothesis `o ∈ 𝒫` plays no role.
The hypothesis `t ≤ N` cannot be dropped, since the path is constant from time `N` on while the
count is not.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

variable {n : ℕ} {ξ : ResidueGroup n}

/-- The weighted white count `N^*(o, β; t)` is at least the number of indices `i ∈ {1, …, t}`
for which `x_i(o, β)` is white, for every block list `β ∈ 𝔅^N` and every `t ≤ N`. -/
@[collatz_pos_dens "lem_tr_count_whites"]
theorem card_white_le_trCount (o : ℤ × ℤ) (β : List (List ℤ × ℤ))
    (hβ : ∀ b ∈ β, b.2 ∈ ({4, 5} : Set ℤ)) {t : ℕ} (ht : t ≤ β.length) :
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
    · have hle := chPaidReward_le_trReward (n := n) (ξ := ξ) (trPath o β t) β[t]
      split_ifs with hw
      · have he := hβ _ (List.getElem_mem htN)
        have h1 := chOldReward_of_isBkWhite (n := n) (ξ := ξ) (ε := (epsStar : ℝ)) he hw
        have h2 := chPaidReward_ge_chOldReward n ξ (epsStar : ℝ) β[t].2
          (trPath o β t + chBlockPoint β[t])
        push_cast
        linarith
      · simpa using trReward_nonneg (n := n) (ξ := ξ) (trPath o β t) β[t]

end CollatzPosDens
