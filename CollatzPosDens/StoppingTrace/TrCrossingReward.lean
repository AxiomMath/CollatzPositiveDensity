/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidRewardNonneg
public import CollatzPosDens.StoppingTrace.TrCountRaw
public import CollatzPosDens.StoppingTrace.TrRaw3Witness

/-!
# The reward collected at a first raw crossing

Fix a level `n` and a residue `ξ ∈ G_n`, and write `R_a(p)` for the paid reward of
`(n, ξ, ε_*)`. Let `π ∈ 𝒳_{c,o,r}(s)` be a first raw crossing event: with `M = j(Bp_{|π|}(π))`
and `z = raw_M(π)`, we have `r ≤ M`, `z_r = c` and `σ_r(π) = s + o`. Then the weighted white
count of all blocks of `π` from any base point `v` is at least the reward of the crossing letter:
```
N^*(v, π; |π|) ≥ R_c(v + (r, s + o)).
```
Indeed `N^*(v, π; |π|) = ∑_{i=1}^{M} R_{z_i}(v + (i, σ_i(π)))`, the term `i = r` of this sum
is `R_c(v + (r, s + o))`, and every term is nonnegative.

## Main results

* `CollatzPosDens.chPaidReward_le_trCount_of_mem_trRawThreeWitness`:
  `R_c(v + (r, s + o)) ≤ N^*(v, π; |π|)` for `π ∈ 𝒳_{c,o,r}(s)` and `r ≥ 1`.

## Implementation notes

No hypothesis `v ∈ 𝒫`, `c ≥ 2` or `1 ≤ o ≤ c` is needed, so the result is stated for every
base point `v : ℤ × ℤ` and all integers `c` and `o`. The hypothesis `r ≥ 1` is kept: it places
the index `r` in the range `{1, …, M}` of the sum.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **The reward at a first raw crossing.** For `π ∈ 𝒳_{c,o,r}(s)` with `r ≥ 1` and any base
point `v`, `N^*(v, π; |π|) ≥ R_c(v + (r, s + o))`. -/
@[collatz_pos_dens "lem_tr_crossing_reward"]
theorem chPaidReward_le_trCount_of_mem_trRawThreeWitness {n : ℕ} (ξ : ResidueGroup n)
    (v : ℤ × ℤ) {s : ℕ} {c o : ℤ} {r : ℕ} (hr : 1 ≤ r) {π : List (List ℤ × ℤ)}
    (hπ : π ∈ trRawThreeWitness s c o r) :
    chPaidReward n ξ (epsStar : ℝ) c (v + ((r : ℤ), (s : ℤ) + o)) ≤
      trCount n ξ v π π.length := by
  rw [trCount_eq_sum_chRaw]
  have hmem : r ∈ Finset.Icc 1 (chBlockPath π π.length).1.toNat :=
    Finset.mem_Icc.2 ⟨hr, trRawThreeWitness_le hπ⟩
  have hterm : chPaidReward n ξ (epsStar : ℝ)
      ((chRaw (chBlockPath π π.length).1.toNat π).getD (r - 1) 0)
      (v + ((r : ℤ), trRawSum π r)) = chPaidReward n ξ (epsStar : ℝ) c (v + ((r : ℤ), s + o)) := by
    rw [List.getD_eq_getElem?_getD, trRawThreeWitness_getElem? hπ, trRawThreeWitness_trRawSum hπ]
    rfl
  rw [← hterm]
  exact Finset.single_le_sum (f := fun i => chPaidReward n ξ (epsStar : ℝ)
      ((chRaw (chBlockPath π π.length).1.toNat π).getD (i - 1) 0)
      (v + ((i : ℤ), trRawSum π i)))
    (fun i _ => zero_le_chPaidReward _ _ _ _ _) hmem

end CollatzPosDens
