/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesLinearLower
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.S05BlockWeight
public import CollatzPosDens.Seed.S05Tuples

/-!
# The weight of a central history is small

Let `t` be an odd positive integer, `n ∈ ℕ` and `h ∈ 𝓗_n(t)`. Then
$$\omega(h)\, 16^{b_n} \le 16^{b_0}.$$
Writing `h = (w_0, …, w_{n-1})`, the weight is multiplicative over the concatenation
`ŵ(h) = w_0 ⋯ w_{n-1}`, each block `w_j ∈ 𝒞(b_j, K_j)` satisfies `ω(w_j) ≤ 16^{-e_{b_j}}`
(as `b_j ≥ 16544 + 166 j ≥ 256`), and `b_{j+1} = b_j + e_{b_j}`, so the bound follows by
induction on the number of blocks.

## Main results

* `CollatzPosDens.weight_concatWord_mul_sixteen_pow_scale_le_of_forall_mem`: for any `s` and any
  tuple `(w_s, …, w_{s+m-1})` with `w_{s+k} ∈ 𝒞(b_{s+k}, K_k)`, for arbitrary overshoot bounds
  `K_k`, `ω(w_s ⋯ w_{s+m-1}) 16^{b_{s+m}} ≤ 16^{b_s}`.
* `CollatzPosDens.weight_concatWord_mul_sixteen_pow_scale_le`: `ω(h) 16^{b_n} ≤ 16^{b_0}`
  for `h ∈ 𝓗_n(t)`.

## Implementation notes

Neither the admissibility of `ŵ(h)`, nor the selector, nor the oddness and positivity of `t` is
used: the bound holds for every tuple whose words lie in the central families `𝒞(b_j, K_j)`.
The weight of a history is `ω(ŵ(h))`, and the inequality is stated in `ℚ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §16.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- If `w_{s+k} ∈ 𝒞(b_{s+k}, K_k)` for every `k < m`, then
`ω(w_s ⋯ w_{s+m-1}) 16^{b_{s+m}} ≤ 16^{b_s}`, the entry `k` of `h : Fin m → Word` being
`w_{s+k}`. -/
theorem weight_concatWord_mul_sixteen_pow_scale_le_of_forall_mem {s m : ℕ} {K : Fin m → ℕ}
    {h : Fin m → Word} (hh : ∀ k : Fin m, h k ∈ centralFamily (scale (s + k)) (K k)) :
    (concatWord h).weight * (16 : ℚ) ^ scale (s + m) ≤ (16 : ℚ) ^ scale s := by
  induction m with
  | zero => rw [concatWord_zero, Word.weight_nil, one_mul, Nat.add_zero]
  | succ m ih =>
    have hprev := ih (K := fun i => K i.castSucc) fun i => hh i.castSucc
    have hb : 256 ≤ scale (s + m) := by have := scale_linear_lower (s + m); omega
    have hlast := sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily hb (hh (Fin.last m))
    have hlast' : (h (Fin.last m)).weight * 16 ^ eb (scale (s + m)) ≤ 1 := by
      have : (0 : ℚ) < (2 ^ (3 * scale (s + m)))⁻¹ := by positivity
      rw [mul_comm]
      linarith
    have hw0 := Word.weight_pos (concatWord fun i : Fin m => h i.castSucc)
    rw [concatWord_succ, Word.weight_append, ← Nat.add_assoc, scale_succ, pow_add]
    calc (concatWord fun i : Fin m => h i.castSucc).weight * (h (Fin.last m)).weight *
          (16 ^ scale (s + m) * 16 ^ eb (scale (s + m)))
        = (concatWord fun i : Fin m => h i.castSucc).weight * 16 ^ scale (s + m) *
            ((h (Fin.last m)).weight * 16 ^ eb (scale (s + m))) := by ring
      _ ≤ (concatWord fun i : Fin m => h i.castSucc).weight * 16 ^ scale (s + m) * 1 := by
          gcongr
      _ ≤ 16 ^ scale s := by simpa using hprev

/-- **Weights of histories are small.** For `h ∈ 𝓗_n(t)`, `ω(h) 16^{b_n} ≤ 16^{b_0}`. -/
@[collatz_pos_dens "lem_history_weight_small"]
theorem weight_concatWord_mul_sixteen_pow_scale_le {t : ℚ} {n : ℕ} {h : Fin n → Word}
    (hh : h ∈ centralHistories t n) :
    (concatWord h).weight * (16 : ℚ) ^ scale n ≤ (16 : ℚ) ^ scale 0 := by
  have key := weight_concatWord_mul_sixteen_pow_scale_le_of_forall_mem (s := 0)
    (h := h) fun k => by
      simpa using selectedTuples_mem_centralFamily
        (centralHistories_subset_selectedTuples t n hh) k
  simpa using key

end CollatzPosDens
