/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.OffsetBound
public import CollatzPosDens.FirstCrossing.Caps
public import CollatzPosDens.FirstCrossing.CentralFamily
public import CollatzPosDens.FirstCrossing.EbLower
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.Seed.BlockWeight
public import CollatzPosDens.Seed.OffsetSmall

/-!
# Offset of a central suffix

Let `0 ≤ i ≤ n` and let `w_j ∈ 𝒞(b_j, K_j)` for `i ≤ j < n`. Then
$$0 \le \mathrm{off}(w_i w_{i+1} \cdots w_{n-1}) \le 2^{b_i + 1}.$$
Writing `τ_j = off(w_j ⋯ w_{n-1})`, one shows `τ_j ≤ 2^{b_j + 1}` by downward induction on `j`:
`τ_n = 0`, and for `j < n` the cocycle identity gives `τ_j = off(w_j) + ω(w_j) τ_{j+1}`, where
`off(w_j) < 2^{b_j}`, `16^{e_{b_j}} ω(w_j) < 1` and `b_{j+1} = b_j + e_{b_j}` with
`e_{b_j} ≥ 1`, so that `ω(w_j) τ_{j+1} ≤ 16^{-e_{b_j}} 2^{b_j + e_{b_j} + 1} ≤ 2^{b_j}`.

## Main results

* `CollatzPosDens.off_flatten_le_of_mem_centralFamily`: for a list of words whose `k`-th
  entry lies in `𝒞(b_{s+k}, K(s+k))`, the offset of the concatenation is at most `2^{b_s + 1}`.
* `CollatzPosDens.off_historySuffix_mem_Icc`: for `w : Fin n → Word` with
  `w_j ∈ 𝒞(b_j, K_j)` for `i ≤ j < n`, `0 ≤ off(w_i ⋯ w_{n-1}) ≤ 2^{b_i + 1}`.

## Implementation notes

The words `w_i, …, w_{n-1}` are given as the entries with index at least `i` of a tuple
`w : Fin n → Word`, and the suffix word `w_i ⋯ w_{n-1}` is the flattening of
`(List.ofFn w).drop i`; the entries with index below `i` are unconstrained. The hypothesis
`i ≤ n` is not needed: for `i > n` the suffix is empty. The downward induction on `j` is an
induction on the list of remaining words, starting at an arbitrary generation `s`; in that
auxiliary form the caps `K_j` may be replaced by an arbitrary family, since only membership in
the first-crossing family and the weight bound of a central block are used.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- The offset of the concatenation of a list of words `L`, whose `k`-th entry lies in
`𝒞(b_{s+k}, K(s+k))`, is at most `2^{b_s + 1}`. -/
theorem off_flatten_le_of_mem_centralFamily (K : ℕ → ℕ) :
    ∀ (L : List Word) (s : ℕ),
      (∀ (k : ℕ) (hk : k < L.length), L[k] ∈ centralFamily (scale (s + k)) (K (s + k))) →
      off L.flatten ≤ 2 ^ (scale s + 1)
  | [], s, _ => by
    simp [off_eq_sum]
  | w :: L, s, hL => by
    have hw : w ∈ centralFamily (scale s) (K s) := by
      have := hL 0 (by simp)
      rwa [List.getElem_cons_zero, Nat.add_zero] at this
    have ih := off_flatten_le_of_mem_centralFamily K L (s + 1) fun k hk => by
      have := hL (k + 1) (by simp; omega)
      rwa [List.getElem_cons_succ, show s + (k + 1) = s + 1 + k by omega] at this
    rw [scale_succ] at ih
    rw [List.flatten_cons, off_append]
    have hoff := off_lt_two_pow_of_mem_firstCrossing (centralFamily_subset_firstCrossing _ _ hw)
    have hwt := sixteen_pow_eb_mul_weight_lt_of_mem_centralFamily (nine_le_scale s) hw
    have hinv : (0 : ℚ) ≤ (2 ^ (3 * scale s))⁻¹ := by positivity
    have hwpos := Word.weight_pos w
    set e := eb (scale s)
    have he : 1 ≤ e := one_le_eb _
    have h2 : (2 : ℚ) ^ (scale s + e + 1) ≤ 16 ^ e * 2 ^ scale s := by
      rw [show scale s + e + 1 = (e + 1) + scale s by omega, pow_add,
        show (16 : ℚ) = 2 ^ 4 by norm_num, ← pow_mul]
      gcongr
      · norm_num
      · omega
    have h2b : (0 : ℚ) < 2 ^ scale s := by positivity
    calc off w + w.weight * off L.flatten
        ≤ 2 ^ scale s + w.weight * (16 ^ e * 2 ^ scale s) := by
          gcongr
          exact ih.trans h2
      _ = 2 ^ scale s + (16 ^ e * w.weight) * 2 ^ scale s := by ring
      _ ≤ 2 ^ scale s + 1 * 2 ^ scale s := by
          gcongr
          linarith
      _ = 2 ^ (scale s + 1) := by ring

/-- **Offset of a central suffix.** Let `w : Fin n → Word` with `w_j ∈ 𝒞(b_j, K_j)` for
`i ≤ j < n`. Then `0 ≤ off(w_i w_{i+1} ⋯ w_{n-1}) ≤ 2^{b_i + 1}`. -/
@[collatz_pos_dens "lem_history_offset"]
theorem off_historySuffix_mem_Icc {n : ℕ} (i : ℕ) (w : Fin n → Word)
    (hw : ∀ j : Fin n, i ≤ j → w j ∈ centralFamily (scale j) (cap j)) :
    0 ≤ off ((List.ofFn w).drop i).flatten ∧
      off ((List.ofFn w).drop i).flatten ≤ 2 ^ (scale i + 1) := by
  refine ⟨off_nonneg _, off_flatten_le_of_mem_centralFamily cap _ i fun k hk => ?_⟩
  have hk' : i + k < n := by simp at hk; omega
  simpa using hw ⟨i + k, hk'⟩ (by simp)

end CollatzPosDens
