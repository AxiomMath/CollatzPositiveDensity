/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidRewardCap
public import CollatzPosDens.CharSum.ChPaidRewardNonneg
public import CollatzPosDens.StoppingTrace.TrCountRaw
public import CollatzPosDens.StoppingTrace.TrEntryWord
public import CollatzPosDens.StoppingTrace.TrTreeDatum
public import CollatzPosDens.StoppingTrace.TrTreeFactor
public import CollatzPosDens.StoppingTrace.TrTreeLeaves
public import CollatzPosDens.Transfer.S02Gamma
public import CollatzPosDens.Transfer.S02Z

/-!
# The paid factors along a leaf of a tree datum

Let `v` be a point, `H ∈ ℕ` and `X` a real number such that
`ϑ(v + (r, L)) - 9^{r-1} X / 2^L ∈ ℤ` for all integers `r ≥ 1` and `0 ≤ L ≤ H`. Let
`(cut, W)` be a tree datum of height `H`, let `λ ∈ 𝔏^W(0, 0)` be a leaf with `k = |λ|`, and let
`u ∈ 𝓔(v)` be an entry list whose raw word begins with `λ`. Then
```
exp (-γ_* N^*(v, u; |u|)) ≤ ∏_{i=1}^{k} ψ^cut_{i-1, λ_1 + ⋯ + λ_{i-1}, λ_i}(X).
```
Indeed, `N^*(v, u; |u|)` is the sum of the nonnegative paid rewards of the raw letters of `u`,
so it is at least the sum over the first `k` letters `λ_i`, read at `p_i = v + (i, h_i)` with
`h_i = λ_1 + ⋯ + λ_i`. The endpoint of `u` is black, so `j(p_i) ≤ ⌊n/2⌋`. Unless
`3 ≤ λ_i ≤ cut(h_{i-1})`, the factor `e^{-z_* R_{λ_i}(p_i)}` is at most `1 = ψ^cut`. Otherwise
the depth `h_{i-1}` is the root or a depth `h + c` reached by a triple `(i - 2, h, c) ∈ W`, so
the tree datum gives `cut(h_{i-1}) ≤ 16` and `h_i ≤ h_{i-1} + cut(h_{i-1}) ≤ H`. The paid reward
cap, the hypothesis on `ϑ` and the period `1` of the packet function then give
`e^{-z_* R_{λ_i}(p_i)} ≤ Φ^cap_{λ_i}(9^{i-1} X / 2^{h_i}) = ψ^cut_{i-1, h_{i-1}, λ_i}(X)`.

## Main results

* `CollatzPosDens.exp_neg_gammaStar_mul_trCount_le_prod_trCapFactor`: the bound on the weight
  `exp (-γ_* N^*)` by the product of the retained factors along the leaf.

## Implementation notes

The result is stated for an arbitrary point `v` and an arbitrary real `X`: the argument uses
neither that `v` is black nor that `X = 2^ω m + α` with `ω = gap(v)`, `m ∈ ℤ` and `α ∈ ℝ`, which
is the case of interest. The colour scale `ε` of the entry lists is arbitrary; the weighted white
count is that of `ε_*`, as in `CollatzPosDens.trCount`. The raw word of `u` is `raw_{M_u}(u)` with
`M_u = j(Bp_{|u|}(u))`; that it has length at least `k` and begins with `λ` is the prefix
relation `λ <+: raw_{M_u}(u)`. Products and partial sums are indexed from `0`: the factor of
index `i < k` is the factor `i + 1` above, read at the natural height `Int.toNat (λ_1 + ⋯ + λ_i)`,
as in `CollatzPosDens.hasSum_trTreeLeaves_trTreeCost`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- On a leaf `λ ∈ 𝔏^W(0, 0)` of a tree datum of height `H`, the depth `h = λ_1 + ⋯ + λ_i` at
which the letter of index `i` is read is a natural number, the cutoff there is at most `16`, and
`h + cut(h) ≤ H`. -/
private theorem TreeDatum.reached_of_mem_trTreeLeaves {H : ℕ} (D : TreeDatum H) {w : List ℤ}
    (hw : w ∈ trTreeLeaves D.W 0 0) {i : ℕ} (hi : i < w.length) :
    0 ≤ (w.take i).sum ∧ D.cut (w.take i).sum.toNat ≤ 16 ∧
      (w.take i).sum.toNat + D.cut (w.take i).sum.toNat ≤ H := by
  obtain ⟨hnn, hreach⟩ : 0 ≤ (w.take i).sum ∧
      ((w.take i).sum.toNat = 0 ∨ ∃ p ∈ D.W, (w.take i).sum.toNat = p.2.1 + p.2.2) := by
    rcases i with _ | i
    · simp
    · obtain ⟨a, b, hab, ha, hb⟩ := (hw.2 i (by omega)).2 (by omega)
      rw [zero_add] at hab
      rw [Nat.cast_zero, zero_add] at ha
      rw [List.sum_take_succ w i (by omega), ← ha, ← hb]
      exact ⟨by omega, Or.inr ⟨(i, a, b), hab, by dsimp only; omega⟩⟩
  refine ⟨hnn, ?_, ?_⟩
  · rcases hreach with h0 | ⟨p, hp, hpeq⟩
    · rw [h0]
      exact D.cut_le_sixteen_of_reached (Or.inl rfl)
    · rw [hpeq]
      exact D.cut_le_sixteen_of_reached (Or.inr ⟨p, hp, rfl⟩)
  · rcases hreach with h0 | ⟨p, hp, hpeq⟩
    · rw [h0]
      simpa using D.add_cut_le_of_reached (Or.inl rfl)
    · rw [hpeq]
      exact D.add_cut_le_of_reached (Or.inr ⟨p, hp, rfl⟩)

/-- **The paid factors along a leaf.** Let `X` be a real number with
`ϑ(v + (r, L)) - 9^{r-1} X / 2^L ∈ ℤ` for all integers `r ≥ 1` and `0 ≤ L ≤ H`, let `(cut, W)`
be a tree datum of height `H`, let `λ ∈ 𝔏^W(0, 0)`, `k = |λ|`, and let `u ∈ 𝓔(v)` have a raw
word beginning with `λ`. Then
`exp (-γ_* N^*(v, u; |u|)) ≤ ∏_{i=1}^{k} ψ^cut_{i-1, λ_1 + ⋯ + λ_{i-1}, λ_i}(X)`. -/
@[collatz_pos_dens "lem_tr_tree_leaf_reward"]
theorem exp_neg_gammaStar_mul_trCount_le_prod_trCapFactor {n : ℕ} {ξ : ResidueGroup n}
    {ε : ℝ} {v : ℤ × ℤ} {H : ℕ} {X : ℝ}
    (hθ : ∀ r : ℕ, 1 ≤ r → ∀ L : ℤ, 0 ≤ L → L ≤ H →
      ∃ m : ℤ, bkTheta n ξ (v + ((r : ℤ), L)) - 9 ^ (r - 1) * X / (2 : ℝ) ^ L = m)
    (D : TreeDatum H) {w : List ℤ} (hw : w ∈ trTreeLeaves D.W 0 0) {u : List (List ℤ × ℤ)}
    (hu : u ∈ trEntryWords n ξ ε v) (hwu : w <+: chRaw (chBlockPath u u.length).1.toNat u) :
    Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length) ≤
      ∏ i : Fin w.length, trTreeFactor D.cut i (w.take i).sum.toNat w[i] X := by
  set z := u.flatMap fun b => b.1 ++ [b.2] with hz
  rw [chRaw_toNat_chBlockPath_fst] at hwu
  obtain ⟨t, ht⟩ := hwu
  rw [← hz] at ht
  have hγ : (gammaStar : ℝ) = (zStar : ℝ) := by norm_num [gammaStar_eq, zStar_eq]
  have hzpos : (0 : ℝ) < zStar := by exact_mod_cast zStar_pos
  set f : ℕ → ℝ := fun i => chPaidReward n ξ (epsStar : ℝ) (z.getD i 0)
    (v + ((i : ℤ) + 1, (z.take (i + 1)).sum)) with hf
  have hk : w.length ≤ z.length := by rw [← ht, List.length_append]; omega
  have hcount : ∑ i ∈ Finset.range w.length, f i ≤ trCount n ξ v u u.length := by
    rw [trCount_eq_sum_flatMap]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
      fun i _ _ => zero_le_chPaidReward _ _ _ _ _
  have hJ : v.1 + (z.length : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by
    have hb := (trEntryWords_bkBlack hu).bkJ_le
    rw [trPath_eq_add_chBlockPath] at hb
    have h1 := toNat_chBlockPath_fst u
    have h2 := chBlockPath_fst_nonneg u u.length
    simp only [bkJ, Prod.fst_add] at hb
    rw [← hz] at h1
    omega
  calc Real.exp (-(gammaStar : ℝ) * trCount n ξ v u u.length)
      ≤ Real.exp (-(zStar : ℝ) * ∑ i : Fin w.length, f i) := by
        rw [hγ, ← Finset.sum_range]
        exact Real.exp_le_exp.2 (by nlinarith)
    _ = ∏ i : Fin w.length, Real.exp (-(zStar : ℝ) * f i) := by
        rw [Finset.mul_sum, Real.exp_sum]
    _ ≤ _ := by
        refine Finset.prod_le_prod₀ (fun i _ => (Real.exp_pos _).le) fun i _ => ?_
        obtain ⟨i, hi⟩ := i
        simp only [Fin.getElem_fin]
        have hgetD : z.getD i 0 = w[i] := by
          rw [← ht, List.getD_append _ _ _ _ hi, List.getD_eq_getElem]
        have htake : z.take (i + 1) = w.take (i + 1) := by
          rw [← ht, List.take_append_of_le_length (by omega)]
        have hsum : (w.take (i + 1)).sum = (w.take i).sum + w[i] := List.sum_take_succ w i hi
        simp only [hf, hgetD, htake, hsum]
        obtain ⟨hnn, hcut16, hcutH⟩ := D.reached_of_mem_trTreeLeaves hw hi
        set c := w[i]
        set h := (w.take i).sum
        by_cases hc : 3 ≤ c ∧ c ≤ (D.cut h.toNat : ℤ)
        · have hc16 : c ≤ 16 := by omega
          have hp : bkJ (v + ((i : ℤ) + 1, h + c)) ≤ ((n / 2 : ℕ) : ℤ) := by
            simp only [bkJ, Prod.fst_add]
            omega
          refine (exp_neg_zStar_mul_chPaidReward_le hc.1 hc16 hp).trans_eq ?_
          rw [trTreeFactor_of_mem (by omega) hc.2, Int.toNat_of_nonneg hnn,
            trCapFactor_of_mem hc.1 hc16, chRawFactor_of_two_le n ξ (by omega)]
          obtain ⟨m, hm⟩ := hθ (i + 1) (by omega) (h + c) (by omega) (by omega)
          have hθeq : bkTheta n ξ (v + ((i : ℤ) + 1, h + c)) =
              9 ^ i * X / (2 : ℝ) ^ (h + c) + m := by
            push_cast at hm
            linarith
          rw [hθeq, chPacketFn_add_intCast]
        · have hψ : trTreeFactor D.cut i h.toNat c X = 1 := by
            unfold trTreeFactor
            split_ifs with h2
            · exact trCapFactor_of_not_mem (by omega) _
            · rfl
          rw [hψ]
          refine Real.exp_le_one_iff.2 ?_
          have := zero_le_chPaidReward n ξ (epsStar : ℝ) c (v + ((i : ℤ) + 1, h + c))
          nlinarith

end CollatzPosDens
