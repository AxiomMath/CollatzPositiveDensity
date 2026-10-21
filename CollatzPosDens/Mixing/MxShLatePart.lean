/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShHalfMoment
public import CollatzPosDens.Mixing.MxShHypergeomPgf
public import CollatzPosDens.Mixing.MxShRatio
public import CollatzPosDens.Mixing.MxShSplitBij
public import CollatzPosDens.Mixing.MxShSubsetOffset

/-!
# The late part of the degree cut

Let `N, d, q` be natural numbers with `q + 2 ≤ N` and `100 d ≤ 51 (N - q - 1)`. Split a
`d`-subset `S ⊆ {1, …, N}` at `q` into its early part `β = S ∩ {1, …, q}` and its late part
`T = {s - q : s ∈ S, s > q} ⊆ {1, …, N - q}`. We show
$$\sum_{S \subseteq \{1, \dots, N\},\ |S| = d}
  \sqrt{3^{|S \cap \{1, \dots, q\}|}\, 2^{-q}\, \operatorname{Of}(T)}
  \le 40 \Bigl(\frac{39}{40}\Bigr)^q \binom N d,$$
where `Of` is the offset `CollatzPosDens.setOffset`.

Grouping the subsets `S` by their early part `β`, the subsets with early part `β` correspond to
the `(d - |β|)`-subsets `T` of `{1, …, N - q}` (`CollatzPosDens.bijOn_splitAt`), so the half
moment bound `CollatzPosDens.sum_powersetCard_sqrt_setOffset_le_forty` bounds the sum of
`√Of(T)` over them by `40` times their number. What remains is
`40 · 2^{-q/2} ∑_S (√3)^{|S ∩ {1, …, q}|}`, which the factorial-moment bound
`CollatzPosDens.sum_powersetCard_Icc_pow_card_inter_le` bounds by
`40 binom N d (2^{-1/2} (1 + (√3 - 1) d / N))^q`; since `d / N ≤ 51/100`, the base is below
`39/40` by `CollatzPosDens.mx_sh_ratio_lt`.

## Main results

* `CollatzPosDens.sum_filter_inter_Icc_eq_sum_powersetCard`: the `d`-subsets of `{1, …, N}` with
  early part `β` are in bijection with the `(d - |β|)`-subsets of `{1, …, N - q}` via their late
  part.
* `CollatzPosDens.sum_powersetCard_sqrt_late_le`: the late-part bound.

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- For `q ≤ N` and `β ⊆ {1, …, q}` with `|β| ≤ d`, summing a function of the late part
`{s - q : s ∈ S, s > q}` over the `d`-subsets `S ⊆ {1, …, N}` with `S ∩ {1, …, q} = β` is summing
it over the `(d - |β|)`-subsets of `{1, …, N - q}`. -/
theorem sum_filter_inter_Icc_eq_sum_powersetCard {M : Type*} [AddCommMonoid M] {N q d : ℕ}
    (hq : q ≤ N) {β : Finset ℕ} (hβ : β ⊆ Icc 1 q) (hβd : #β ≤ d) (φ : Finset ℕ → M) :
    ∑ S ∈ (Icc 1 N).powersetCard d with S ∩ Icc 1 q = β, φ (splitAt q S).2 =
      ∑ T ∈ (Icc 1 (N - q)).powersetCard (d - #β), φ T := by
  have hbij := bijOn_splitAt d hq
  refine sum_nbij' (fun S => (splitAt q S).2) (joinAt q β) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro S hS
    rw [mem_filter] at hS
    obtain ⟨h1, h2, h3⟩ := hbij.mapsTo (mem_coe.2 hS.1)
    rw [splitAt_fst, hS.2] at h1 h3
    rw [mem_powersetCard]
    exact ⟨h2, by omega⟩
  · intro T hT
    rw [mem_powersetCard] at hT
    obtain ⟨S, hS, hSeq⟩ := hbij.surjOn
      (show (β, T) ∈ {p : Finset ℕ × Finset ℕ |
        p.1 ⊆ Icc 1 q ∧ p.2 ⊆ Icc 1 (N - q) ∧ p.1.card + p.2.card = d} from
        ⟨hβ, hT.1, by simp only; omega⟩)
    have hS' := mem_powersetCard.1 (mem_coe.1 hS)
    have hS0 : 0 ∉ S := fun h => by simpa using (mem_Icc.1 (hS'.1 h)).1
    have hj : joinAt q β T = S := by
      rw [← joinAt_splitAt (q := q) hS0, hSeq]
    rw [mem_filter, hj]
    refine ⟨mem_coe.1 hS, ?_⟩
    have := congrArg Prod.fst hSeq
    rwa [splitAt_fst] at this
  · intro S hS
    rw [mem_filter, mem_powersetCard] at hS
    have hS0 : 0 ∉ S := fun h => by simpa using (mem_Icc.1 (hS.1.1 h)).1
    have := joinAt_splitAt (q := q) hS0
    rw [splitAt_fst, hS.2] at this
    exact this
  · intro T hT
    rw [mem_powersetCard] at hT
    have hT0 : 0 ∉ T := fun h => by simpa using (mem_Icc.1 (hT.1 h)).1
    simp only [splitAt_joinAt hβ hT0]

/-- **The late part of the degree cut.** For `q + 2 ≤ N` and `100 d ≤ 51 (N - q - 1)`,
$$\sum_{S \subseteq \{1, \dots, N\},\ |S| = d}
  \sqrt{3^{|S \cap \{1, \dots, q\}|}\, 2^{-q}\, \operatorname{Of}(\{s - q : s \in S,\ s > q\})}
  \le 40 \Bigl(\frac{39}{40}\Bigr)^q \binom N d.$$ -/
@[collatz_pos_dens "lem_mx_sh_late_part"]
theorem sum_powersetCard_sqrt_late_le {N d q : ℕ} (hq : q + 2 ≤ N)
    (hd : 100 * d ≤ 51 * (N - q - 1)) :
    ∑ S ∈ (Icc 1 N).powersetCard d,
        √((3 : ℝ) ^ #(S ∩ Icc 1 q) * ((2 : ℝ) ^ q)⁻¹ *
          (setOffset ((S.filter (q < ·)).image (· - q)) : ℝ)) ≤
      40 * (39 / 40 : ℝ) ^ q * N.choose d := by
  set P := (Icc 1 N).powersetCard d with hP
  set c : ℝ := √(((2 : ℝ) ^ q)⁻¹) with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hsqrtpow : ∀ x : ℝ, 0 ≤ x → ∀ n : ℕ, √(x ^ n) = √x ^ n := by
    intro x hx n
    rw [show x ^ n = (√x ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]]
    exact Real.sqrt_sq (by positivity)
  have hsplit : ∀ S ∈ P,
      √((3 : ℝ) ^ #(S ∩ Icc 1 q) * ((2 : ℝ) ^ q)⁻¹ *
          (setOffset ((S.filter (q < ·)).image (· - q)) : ℝ)) =
        √3 ^ #(S ∩ Icc 1 q) * c * √(setOffset (splitAt q S).2 : ℝ) := by
    intro S _
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      hsqrtpow 3 (by norm_num), splitAt_snd]
  rw [sum_congr rfl hsplit]
  have hfib : ∀ β ∈ (Icc 1 q).powerset,
      ∑ S ∈ P with S ∩ Icc 1 q = β, √(setOffset (splitAt q S).2 : ℝ) ≤
        ∑ S ∈ P with S ∩ Icc 1 q = β, (40 : ℝ) := by
    intro β hβ
    rw [mem_powerset] at hβ
    by_cases hβd : #β ≤ d
    · have hqN : q ≤ N := by omega
      have h1 := sum_filter_inter_Icc_eq_sum_powersetCard hqN hβ hβd
        (fun T => √(setOffset T : ℝ))
      have h2 := sum_filter_inter_Icc_eq_sum_powersetCard hqN hβ hβd (fun _ => (40 : ℝ))
      simp only at h1 h2
      rw [hP, h1, h2,
        sum_const, card_powersetCard, Nat.card_Icc, nsmul_eq_mul]
      refine (sum_powersetCard_sqrt_setOffset_le_forty ?_).trans_eq ?_
      · omega
      · rw [Nat.add_sub_cancel]; ring
    · have : (P.filter fun S => S ∩ Icc 1 q = β) = ∅ := by
        refine filter_false_of_mem fun S hS hSβ => hβd ?_
        rw [← hSβ, ← (mem_powersetCard.1 hS).2]
        exact card_le_card inter_subset_left
      simp [this]
  have hmaps : ∀ S ∈ P, S ∩ Icc 1 q ∈ (Icc 1 q).powerset := fun S _ =>
    mem_powerset.2 inter_subset_right
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h3 : 1 ≤ √3 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpgf := sum_powersetCard_Icc_pow_card_inter_le N d q h3
  have hdN : (d : ℝ) / N ≤ 51 / 100 := by
    rw [div_le_iff₀ hN]
    have : 100 * d ≤ 51 * N := hd.trans (by omega)
    have : (100 : ℝ) * d ≤ 51 * N := by exact_mod_cast this
    linarith
  have h2 : 0 < √2 := by positivity
  have hbase0 : 0 ≤ 1 + (√3 - 1) * d / N := by
    have : 0 ≤ (√3 - 1) * d / N := by
      have : 0 ≤ √3 - 1 := by linarith
      positivity
    linarith
  have hρ : (1 + (√3 - 1) * d / N) / √2 ≤ 39 / 40 := by
    refine le_of_lt (lt_of_le_of_lt ?_ mx_sh_ratio_lt)
    have : (√3 - 1) * d / N ≤ (√3 - 1) * (51 / 100) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hdN (by linarith)
    exact div_le_div_of_nonneg_right (by linarith) h2.le
  have hcpow : c * (1 + (√3 - 1) * d / N) ^ q ≤ (39 / 40) ^ q := by
    have : c = ((√2)⁻¹) ^ q := by
      rw [hc, Real.sqrt_inv, hsqrtpow 2 (by norm_num), inv_pow]
    rw [this, ← mul_pow, ← div_eq_inv_mul]
    exact pow_le_pow_left₀ (by positivity) hρ q
  calc ∑ S ∈ P, √3 ^ #(S ∩ Icc 1 q) * c * √(setOffset (splitAt q S).2 : ℝ)
      = ∑ β ∈ (Icc 1 q).powerset, √3 ^ #β * c *
          ∑ S ∈ P with S ∩ Icc 1 q = β, √(setOffset (splitAt q S).2 : ℝ) := by
        rw [← sum_fiberwise_of_maps_to hmaps]
        refine sum_congr rfl fun β _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun S hS => ?_
        rw [(mem_filter.1 hS).2]
    _ ≤ ∑ β ∈ (Icc 1 q).powerset, √3 ^ #β * c * ∑ S ∈ P with S ∩ Icc 1 q = β, (40 : ℝ) := by
        refine sum_le_sum fun β hβ => ?_
        exact mul_le_mul_of_nonneg_left (hfib β hβ) (by positivity)
    _ = 40 * c * ∑ S ∈ P, √3 ^ #(S ∩ Icc 1 q) := by
        rw [← sum_fiberwise_of_maps_to hmaps, mul_sum]
        refine sum_congr rfl fun β _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun S hS => ?_
        rw [(mem_filter.1 hS).2]
        ring
    _ ≤ 40 * c * (N.choose d * (1 + (√3 - 1) * d / N) ^ q) := by
        gcongr
    _ = 40 * (c * (1 + (√3 - 1) * d / N) ^ q) * N.choose d := by ring
    _ ≤ 40 * (39 / 40 : ℝ) ^ q * N.choose d := by
        gcongr

end CollatzPosDens
