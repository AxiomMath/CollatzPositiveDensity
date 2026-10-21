/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrCount
public import CollatzPosDens.StoppingTrace.TrRewardNonneg

/-!
# Monotonicity of the weighted white count

Fix a level `n` and a residue `ξ ∈ G_n`. For a base point `o ∈ 𝒫`, a block list `β ∈ 𝔅^N` and
times `t ≤ t'`, the weighted white count satisfies `N^*(o, β; t) ≤ N^*(o, β; t')`: the difference
is the sum of the rewards `rw(x_{i-1}(o, β), β^i)` for `min(t, N) < i ≤ min(t', N)`, each of
which is nonnegative.

## Main results

* `CollatzPosDens.trCount_le_trCount`: `N^*(o, β; t) ≤ N^*(o, β; t')` for `t ≤ t'`.

## Implementation notes

The inequality holds for every `o : ℤ × ℤ` and every `β : List (List ℤ × ℤ)`, not only for
`o ∈ 𝒫` and `β ∈ 𝔅^N`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **The weighted white count is nondecreasing in time.** For `t ≤ t'`,
`N^*(o, β; t) ≤ N^*(o, β; t')`. -/
@[collatz_pos_dens "lem_tr_count_mono"]
theorem trCount_le_trCount (n : ℕ) (ξ : ResidueGroup n) (o : ℤ × ℤ) (β : List (List ℤ × ℤ))
    {t t' : ℕ} (htt' : t ≤ t') : trCount n ξ o β t ≤ trCount n ξ o β t' :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (min_le_min_right _ htt'))
    fun _ _ _ => zero_le_trReward _ _ _ _

end CollatzPosDens
