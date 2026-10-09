/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxHeadGate
public import CollatzPosDens.Mixing.MxLevel
public import CollatzPosDens.Mixing.MxWindowCount

/-!
# Entropy weights of the head gates

For an integer `n` write `V = Lv_n` for the crossing level. A pair `(k, l)` whose head gate
`Hd(n, k, l)` is nonempty has `q^-_n < k + 1 ≤ q^+_n` and `l > V`. There are at most
`n^{2049/4096}` such `k`, and summing the geometric series over `l > V` gives
$$\sum_{\substack{0\le k<n,\ 0\le l<2n\\ \mathrm{Hd}(n,k,l)\neq\emptyset}} 3^n 2^{-l}
  \le n^{2049/4096} \cdot 2 \cdot 3^n 2^{-V} = 8\, n^{5633/2048},$$
using `3^n 2^{-V} = 4 n^{9217/4096}`.

## Main results

* `CollatzPosDens.mxGateWeightSum_le_of_sixteen_le`: the bound for every `n ≥ 16`.
* `CollatzPosDens.mxGateWeightSum_le`: the bound for `n ≥ 2^131072`.
* `CollatzPosDens.mxGateWeightSum_three_pow_mul_rpow_neg_mxLevel`:
  `3^n 2^{-Lv_n} = 4 n^{9217/4096}` for `n ≥ 1`.

## Implementation notes

The argument only needs the window-width bound `q^+_n - q^-_n ≤ n^{2049/4096}`, which holds
for `n ≥ 16`, so the bound is proved under that hypothesis and the form for `n ≥ 2^131072` is
deduced from it. The weight `2^{-l}` is the integer
power `(2 : ℝ) ^ (-(l : ℤ))`, and the sum runs over the pairs of
`range n ×ˢ range (2n)` whose head gate is nonempty.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

/-- For `n ≥ 1`, `3^n 2^{-Lv_n} = 4 n^{9217/4096}`. -/
theorem mxGateWeightSum_three_pow_mul_rpow_neg_mxLevel {n : ℕ} (hn : 1 ≤ n) :
    (3 : ℝ) ^ n * (2 : ℝ) ^ (-mxLevel n) = 4 * (n : ℝ) ^ ((9217 : ℝ) / 4096) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : (2 : ℝ) ^ ((n : ℝ) * Real.logb 2 3) = (3 : ℝ) ^ n := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
      (by norm_num), Real.rpow_natCast]
  have hN : (2 : ℝ) ^ (Real.logb 2 n * ((9217 : ℝ) / 4096)) =
      (n : ℝ) ^ ((9217 : ℝ) / 4096) := by
    rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn']
  have hsplit : -mxLevel n =
      -((n : ℝ) * Real.logb 2 3) + (Real.logb 2 n * ((9217 : ℝ) / 4096) + 2) := by
    rw [mxLevel_def]
    ring
  rw [hsplit, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_neg
    (by norm_num), h3, hN]
  have : (3 : ℝ) ^ n ≠ 0 := by positivity
  norm_num
  field_simp

/-- The geometric tail `∑_{⌈V⌉ ≤ l < N} 2^{-l}` is at most `2 · 2^{-V}`. -/
theorem sum_filter_ceil_le_half_pow_le (V : ℝ) (N : ℕ) :
    ∑ l ∈ (Finset.range N).filter (fun l => ⌈V⌉₊ ≤ l), (1 / 2 : ℝ) ^ l ≤
      2 * (2 : ℝ) ^ (-V) := by
  set m := ⌈V⌉₊
  have himg : (Finset.range N).filter (fun l => m ≤ l) ⊆
      (Finset.range N).image (fun i => m + i) := by
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_range] at hl
    exact Finset.mem_image.2 ⟨l - m, Finset.mem_range.2 (by omega), by omega⟩
  calc ∑ l ∈ (Finset.range N).filter (fun l => m ≤ l), (1 / 2 : ℝ) ^ l
      ≤ ∑ l ∈ (Finset.range N).image (fun i => m + i), (1 / 2 : ℝ) ^ l :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun _ _ _ => by positivity)
    _ ≤ ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ (m + i) :=
        Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
    _ = (1 / 2 : ℝ) ^ m * ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ^ i := by
        rw [Finset.mul_sum]
        simp [pow_add]
    _ ≤ (1 / 2 : ℝ) ^ m * 2 :=
        mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by positivity)
    _ ≤ 2 * (2 : ℝ) ^ (-V) := by
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        rw [one_div, inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (neg_le_neg (Nat.le_ceil V))

/-- For `n ≥ 16`, at most `n^{2049/4096}` indices `k < n` satisfy `q^-_n < k + 1 ≤ q^+_n`. -/
theorem card_filter_mxWindow_le_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) :
    (((Finset.range n).filter (fun k : ℕ => mxWindowLow n < (k : ℤ) + 1 ∧
      (k : ℤ) + 1 ≤ mxWindowHigh n)).card : ℝ) ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) := by
  have hinj : ((Finset.range n).filter (fun k : ℕ => mxWindowLow n < (k : ℤ) + 1 ∧
      (k : ℤ) + 1 ≤ mxWindowHigh n)).card ≤
      (Finset.Ioc (mxWindowLow n - 1) (mxWindowHigh n - 1)).card := by
    refine Finset.card_le_card_of_injOn (fun k => (k : ℤ)) ?_ fun _ _ _ _ h => Int.ofNat_inj.1 h
    intro k hk
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hk
    simp only [Finset.coe_Ioc, Set.mem_Ioc]
    omega
  rw [Int.card_Ioc] at hinj
  refine (Nat.cast_le (α := ℝ)).2 hinj |>.trans ?_
  rcases le_or_gt 0 (mxWindowHigh n - mxWindowLow n) with h0 | h0
  · rw [sub_sub_sub_cancel_right, ← Int.cast_natCast, Int.toNat_of_nonneg h0]
    exact mxWindowHigh_sub_mxWindowLow_le_of_sixteen_le hn
  · rw [show (mxWindowHigh n - 1 - (mxWindowLow n - 1)).toNat = 0 by omega, Nat.cast_zero]
    positivity

open Classical in
/-- **Entropy weights of the head gates**, for `n ≥ 16`. -/
theorem mxGateWeightSum_le_of_sixteen_le {n : ℕ} (hn : 16 ≤ n) :
    ∑ p ∈ (Finset.range n ×ˢ Finset.range (2 * n)).filter
        (fun p : ℕ × ℕ => (mxHeadGate n p.1 p.2).Nonempty),
      (3 : ℝ) ^ n * (2 : ℝ) ^ (-(p.2 : ℤ)) ≤ 8 * (n : ℝ) ^ ((5633 : ℝ) / 2048) := by
  set V := mxLevel n with hV
  set m : ℕ := ⌈V⌉₊ with hm
  set K : Finset ℕ := (Finset.range n).filter
    (fun k => mxWindowLow n < (k : ℤ) + 1 ∧ (k : ℤ) + 1 ≤ mxWindowHigh n) with hK
  set L : Finset ℕ := (Finset.range (2 * n)).filter (fun l => m ≤ l) with hL
  have hsub : (Finset.range n ×ˢ Finset.range (2 * n)).filter
      (fun p : ℕ × ℕ => (mxHeadGate n p.1 p.2).Nonempty) ⊆ K ×ˢ L := by
    rintro ⟨k, l⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hk, hl⟩, h, hh⟩ := hp
    rw [mem_mxHeadGate] at hh
    obtain ⟨-, hwin, ⟨-, hlt, hsum⟩, -⟩ := hh
    rw [hsum] at hlt
    simp only [hK, hL, Finset.mem_product, Finset.mem_filter]
    exact ⟨⟨hk, hwin⟩, hl, Nat.ceil_le.2 hlt.le⟩
  have hterm : ∀ l : ℕ, (2 : ℝ) ^ (-(l : ℤ)) = (1 / 2 : ℝ) ^ l := fun l => by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  have hLsum : ∑ l ∈ L, (1 / 2 : ℝ) ^ l ≤ 2 * (2 : ℝ) ^ (-V) :=
    sum_filter_ceil_le_half_pow_le V (2 * n)
  have hKcard : (K.card : ℝ) ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) :=
    card_filter_mxWindow_le_of_sixteen_le hn
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  calc ∑ p ∈ (Finset.range n ×ˢ Finset.range (2 * n)).filter
        (fun p : ℕ × ℕ => (mxHeadGate n p.1 p.2).Nonempty),
        (3 : ℝ) ^ n * (2 : ℝ) ^ (-(p.2 : ℤ))
      ≤ ∑ p ∈ K ×ˢ L, (3 : ℝ) ^ n * (2 : ℝ) ^ (-(p.2 : ℤ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (K.card : ℝ) * ((3 : ℝ) ^ n * ∑ l ∈ L, (1 / 2 : ℝ) ^ l) := by
        rw [Finset.sum_product]
        simp only [hterm, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ (n : ℝ) ^ ((2049 : ℝ) / 4096) * ((3 : ℝ) ^ n * (2 * (2 : ℝ) ^ (-V))) := by
        gcongr
    _ = 2 * (n : ℝ) ^ ((2049 : ℝ) / 4096) * ((3 : ℝ) ^ n * (2 : ℝ) ^ (-V)) := by ring
    _ = 8 * (n : ℝ) ^ ((5633 : ℝ) / 2048) := by
        rw [hV, mxGateWeightSum_three_pow_mul_rpow_neg_mxLevel hn1,
          show (8 : ℝ) * (n : ℝ) ^ ((5633 : ℝ) / 2048) =
            8 * ((n : ℝ) ^ ((2049 : ℝ) / 4096) * (n : ℝ) ^ ((9217 : ℝ) / 4096)) by
          rw [← Real.rpow_add hnpos]
          norm_num]
        ring

open Classical in
/-- **Entropy weights of the head gates.** For every integer `n ≥ 2^131072`,
`∑_{0 ≤ k < n, 0 ≤ l < 2n, Hd(n,k,l) ≠ ∅} 3^n 2^{-l} ≤ 8 n^{5633/2048}`. -/
@[collatz_pos_dens "lem_mx_gate_weight_sum"]
theorem mxGateWeightSum_le {n : ℕ} (hn : 2 ^ 131072 ≤ n) :
    ∑ p ∈ (Finset.range n ×ˢ Finset.range (2 * n)).filter
        (fun p : ℕ × ℕ => (mxHeadGate n p.1 p.2).Nonempty),
      (3 : ℝ) ^ n * (2 : ℝ) ^ (-(p.2 : ℤ)) ≤ 8 * (n : ℝ) ^ ((5633 : ℝ) / 2048) :=
  mxGateWeightSum_le_of_sixteen_le
    ((pow_le_pow_right₀ (by norm_num : 1 ≤ 2) (by norm_num : 4 ≤ 131072)).trans hn)

end CollatzPosDens
