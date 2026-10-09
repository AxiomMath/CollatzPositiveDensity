/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.BlockWeight
public import CollatzPosDens.Seed.Tuples

/-!
# The weight of a central history is small

Let `M` be an odd positive integer, `n ≥ 0` and `h ∈ 𝓗_n(M)`. Then
$$\omega(h)\, 16^{b_n} \le 16^{b_0}.$$
The weight is multiplicative over the concatenation `ŵ(h) = w₀ ⋯ w_{n-1}`, each block
`w_j ∈ 𝒞(b_j, K_j)` satisfies `ω(w_j) ≤ 16^{-e_{b_j}}` (as `b_j ≥ b_0 = 9`), and
`b_{j+1} = b_j + e_{b_j}`, so the bound follows by induction on `n`.

## Main results

* `CollatzPosDens.weight_concatWord_mul_sixteen_pow_scale_le_of_forall_mem`: the bound for
  any tuple of words with `w_j ∈ 𝒞(b_j, K_j)`, for arbitrary overshoot bounds `K_j`.
* `CollatzPosDens.weight_concatWord_mul_sixteen_pow_scale_le`: `ω(h) 16^{b_n} ≤ 16^{b_0}`
  for `h ∈ 𝓗_n(M)`.

## Implementation notes

Neither the admissibility of `ŵ(h)`, nor the five-block selector, nor the oddness and positivity
of `M` is used: the bound holds for every tuple whose `j`-th word lies in a central family
`𝒞(b_j, K_j)`. The weight of a history is `ω(ŵ(h))`, and the inequality is stated in `ℚ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- If the `j`-th word of a tuple `h` lies in `𝒞(b_j, K_j)` for every `j < n`, then
`ω(ŵ(h)) 16^{b_n} ≤ 16^{b_0}`. -/
theorem weight_concatWord_mul_sixteen_pow_scale_le_of_forall_mem {n : ℕ} {K : Fin n → ℕ}
    {h : Fin n → Word} (hh : ∀ j : Fin n, h j ∈ centralFamily (scale j) (K j)) :
    (concatWord h).weight * (16 : ℚ) ^ scale n ≤ (16 : ℚ) ^ scale 0 := by
  induction n with
  | zero => rw [concatWord_zero, Word.weight_nil, one_mul]
  | succ n ih =>
    have hprev := ih (K := fun i => K i.castSucc) fun i => hh i.castSucc
    have hlast := sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily (nine_le_scale n)
      (hh (Fin.last n))
    have hlast' : (h (Fin.last n)).weight * 16 ^ eb (scale n) ≤ 1 := by
      have : (0 : ℚ) < (2 ^ (3 * scale n))⁻¹ := by positivity
      rw [mul_comm]
      linarith
    have hw0 := Word.weight_pos (concatWord fun i : Fin n => h i.castSucc)
    rw [concatWord_succ, Word.weight_append, scale_succ, pow_add]
    calc (concatWord fun i : Fin n => h i.castSucc).weight * (h (Fin.last n)).weight *
          (16 ^ scale n * 16 ^ eb (scale n))
        = (concatWord fun i : Fin n => h i.castSucc).weight * 16 ^ scale n *
            ((h (Fin.last n)).weight * 16 ^ eb (scale n)) := by ring
      _ ≤ (concatWord fun i : Fin n => h i.castSucc).weight * 16 ^ scale n * 1 := by
          gcongr
      _ ≤ 16 ^ scale 0 := by simpa using hprev

/-- **Weights of histories are small.** For `h ∈ 𝓗_n(M)`, `ω(h) 16^{b_n} ≤ 16^{b_0}`. -/
@[collatz_pos_dens "lem_history_weight_small"]
theorem weight_concatWord_mul_sixteen_pow_scale_le {M : ℚ} {n : ℕ} {h : Fin n → Word}
    (hh : h ∈ centralHistories M n) :
    (concatWord h).weight * (16 : ℚ) ^ scale n ≤ (16 : ℚ) ^ scale 0 :=
  weight_concatWord_mul_sixteen_pow_scale_le_of_forall_mem
    (selectedTuples_mem_centralFamily (centralHistories_subset_selectedTuples M n hh))

end CollatzPosDens
