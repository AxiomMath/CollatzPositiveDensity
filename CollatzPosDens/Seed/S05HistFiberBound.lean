/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.Int.Interval
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.AffineIdentity
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.Weight
public import CollatzPosDens.Maps.WordDetermined
public import CollatzPosDens.Recipe.NstarRange
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesLinearLower
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.HistoryDetermined
public import CollatzPosDens.Seed.HistoryWeightSmall
public import CollatzPosDens.Seed.S05SelectedOffset
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# A fibre of the residue histogram

Let `t` be an odd positive integer, let `N_* = generationThreshold` and `b_n = scale n`, and let
`n ≥ N_*`, `0 ≤ q ≤ 2 b_n`, `y ∈ G_q = ResidueGroup q`, and let `D, A` be integers. Write
`𝓗_n(t) = centralHistories t n`, and for a history `h` write `D(h) = historyDepth h`,
`A(h) = valSum (concatWord h)`, `R_h = historyEndpoint t h` and `ω(h) = weight (concatWord h)`.
Then
$$3^q \sum_{h ∈ 𝓗_n(t),\ D(h) = D,\ A(h) = A,\ R_h ≡ y \ (3^q)} ω(h) < \tfrac{97}{128}.$$

All histories in the fibre share the weight `W = 3^D 2^{-A}`. By the affine identity
`t = W R_h + off(h)`, where `off(h) = off (concatWord h)`, and the offset bound
`0 ≤ off(h) ≤ c = 3/4 + 2^{-8}` for selected tuples (valid as `n ≥ N_* ≥ selEnd`), the
endpoints `R_h` lie in an interval of length `c/W`. They are pairwise distinct: words of equal
length admissible from `t` with equal sources are equal, and a history is determined by its
concatenated word. Hence at most `c/(W 3^q) + 1` of them are congruent to `y`, and the left side
is at most `c + 3^q W`.

Finally `W 16^{b_n} ≤ 16^{b_0}` with `b_0 = 16544` and `3^q ≤ 9^{b_n}`, so
`3^q W ≤ 2^{66176} (9/16)^{b_n}`. With `f = ⌊b_n/5⌋`, the integer inequality
`16 · 9^5 < 16^5` gives `(9/16)^{b_n} ≤ 16^{-f}`, and `b_n ≥ 16544 + 166 · 9853 = 1652142`
gives `f ≥ 330428`, so `3^q W ≤ 2^{66176 - 4f} < 2^{-8}`, and the left side is less than
`3/4 + 2^{-8} + 2^{-8} = 97/128`.

## Main results

* `CollatzPosDens.three_pow_mul_finsum_weight_histFiber_le`: the fibre bound.

## Implementation notes

As in `CollatzPosDens.residueHistogram`, the sum is a `finsum` over the fibre and the
congruence `R_h ≡ y (mod 3^q)` reads "`R_h` is an integer `r` with `r ≡ y (mod 3^q)`". The
fibre is finite, so the `finsum` is a finite sum. The depth and valuation sum of a history are
natural numbers; the conditions `D(h) = D` and `A(h) = A` are stated after casting them to `ℤ`,
so `D` and `A` are arbitrary integers. The comparison `2^{8} 16^{16544} 9^{b_n} < 16^{b_n}` is
proved in `ℕ` with `b_n` a variable, from `16 · 9^5 < 16^5` and `16546 < ⌊b_n/5⌋`, so no large
power is evaluated.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- A nonempty finite set mapped injectively into the integers of `[a / c, b / c]` has at most
`(b - a) / c + 1` elements. -/
private theorem card_toFinset_le_of_injOn_Icc {α : Type*} {S : Set α} (hfin : S.Finite)
    (hne : S.Nonempty) {a b c : ℚ} {f : α → ℤ}
    (hmaps : ∀ x ∈ S, f x ∈ Finset.Icc ⌈a / c⌉ ⌊b / c⌋) (hinj : Set.InjOn f S) :
    (hfin.toFinset.card : ℚ) ≤ (b - a) / c + 1 := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hcard : (hfin.toFinset.card : ℤ) ≤ ⌊b / c⌋ + 1 - ⌈a / c⌉ := by
    have := Finset.card_le_card_of_injOn f (s := hfin.toFinset)
      (fun x hx => hmaps x (hfin.mem_toFinset.mp hx))
      (fun x hx y hy => hinj (hfin.mem_toFinset.mp hx) (hfin.mem_toFinset.mp hy))
    have hpos : 0 < hfin.toFinset.card := Finset.card_pos.mpr ⟨x₀, hfin.mem_toFinset.mpr hx₀⟩
    rw [Int.card_Icc] at this
    omega
  have h₁ : (⌊b / c⌋ : ℚ) ≤ b / c := Int.floor_le _
  have h₂ : a / c ≤ ⌈a / c⌉ := Int.le_ceil _
  have : (hfin.toFinset.card : ℚ) ≤ ⌊b / c⌋ + 1 - ⌈a / c⌉ := by exact_mod_cast hcard
  rw [sub_div]
  linarith

/-- An integer `r` reducing to `y ∈ G_q` is `ỹ + 3^q ((r - ỹ) / 3^q)`, with `ỹ` the
representative of `y`. -/
private theorem eq_val_add_three_pow_mul_ediv {q : ℕ} {y : ResidueGroup q} {r : ℤ}
    (hry : (r : ResidueGroup q) = y) : r = (y.val : ℤ) + 3 ^ q * ((r - y.val) / 3 ^ q) := by
  have hdvd : ((3 ^ q : ℕ) : ℤ) ∣ r - y.val := by
    have : ((r : ℤ) : ZMod (3 ^ q)) = ((y.val : ℤ) : ZMod (3 ^ q)) := by
      rw [hry]
      simp
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ r (3 ^ q)).mp this.symm
  push_cast at hdvd
  rw [Int.mul_ediv_cancel' hdvd, add_sub_cancel]

/-- For a central history `h` of generation `n ≥ j_e`,
`t - (3/4 + 2^{-8}) ≤ ω(h) R_h ≤ t`. -/
private theorem weight_mul_historyEndpoint_mem_Icc {t : ℚ} {n : ℕ} (hn : selEnd ≤ n)
    {h : Fin n → Word} (hh : h ∈ centralHistories t n) :
    t - (3 / 4 + 1 / 2 ^ 8) ≤ (concatWord h).weight * historyEndpoint t h ∧
      (concatWord h).weight * historyEndpoint t h ≤ t := by
  have haff := eq_weight_mul_src_add_off (concatWord h) t
  rw [← historyEndpoint_eq_src] at haff
  obtain ⟨h₀, h₁⟩ := off_concatWord_mem_Icc_of_mem_selectedTuples hn hh.1
  constructor <;> linarith

/-- For an odd `t > 0`, a central history is determined by its depth and its endpoint. -/
private theorem eq_of_historyEndpoint_eq {t : ℤ} (hodd : Odd t) (htpos : 0 < t) {n : ℕ}
    {h h' : Fin n → Word} (hh : h ∈ centralHistories t n)
    (hh' : h' ∈ centralHistories t n)
    (hd : historyDepth h = historyDepth h') (he : historyEndpoint t h = historyEndpoint t h') :
    h = h' := by
  rw [historyEndpoint_eq_src, historyEndpoint_eq_src] at he
  have hw := Admissible.eq_of_src_eq htpos hodd hd hh.2 hh'.2 he
  exact (historyDetermined (w' := []) (w'' := []) scale cap
    (selectedTuples_mem_centralFamily hh.1) (selectedTuples_mem_centralFamily hh'.1)
    (by rw [hw])).1

/-- If `16546 < ⌊b/5⌋`, then `2^8 · 16^{16544} · 9^b < 16^b`: write `b = 5f + r` with `r < 5`;
then `16^f 9^{5f} ≤ 16^{5f}` by `16 · 9^5 < 16^5`, and `9^r ≤ 16^r`. -/
private theorem two_pow_eight_mul_sixteen_pow_mul_nine_pow_lt {b : ℕ} (hb : 16546 < b / 5) :
    256 * 16 ^ 16544 * 9 ^ b < 16 ^ b := by
  set f := b / 5
  set r := b % 5
  have hbfr : b = 5 * f + r := (Nat.div_add_mod b 5).symm
  have h256 : 256 * 16 ^ 16544 = 16 ^ 16546 := by
    rw [show (256 : ℕ) = 16 ^ 2 by norm_num, ← pow_add]
  have hf : 16 ^ 16546 < 16 ^ f := pow_lt_pow_right₀ (by norm_num : (1 : ℕ) < 16) hb
  have h95 : 16 ^ f * (9 ^ 5) ^ f ≤ (16 ^ 5) ^ f := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by norm_num) f
  have hr : 9 ^ r ≤ 16 ^ r := Nat.pow_le_pow_left (by norm_num) r
  have h9 : 9 ^ b = (9 ^ 5) ^ f * 9 ^ r := by rw [hbfr, pow_add, pow_mul]
  have h16 : 16 ^ b = (16 ^ 5) ^ f * 16 ^ r := by rw [hbfr, pow_add, pow_mul]
  rw [h256, h9, h16]
  have hpos : 0 < (9 ^ 5) ^ f * 9 ^ r := by positivity
  calc 16 ^ 16546 * ((9 ^ 5) ^ f * 9 ^ r) < 16 ^ f * ((9 ^ 5) ^ f * 9 ^ r) :=
        Nat.mul_lt_mul_of_pos_right hf hpos
    _ = (16 ^ f * (9 ^ 5) ^ f) * 9 ^ r := by ring
    _ ≤ (16 ^ 5) ^ f * 16 ^ r := Nat.mul_le_mul h95 hr

/-- For `n ≥ N_*`, `⌊b_n/5⌋ ≥ 330428`, by `b_n ≥ 16544 + 166 · 9853 = 1652142`. -/
private theorem le_scale_div_five_of_generationThreshold_le {n : ℕ}
    (hn : generationThreshold ≤ n) :
    330428 ≤ scale n / 5 := by
  have h := scale_linear_lower n
  rw [generationThreshold_def] at hn
  omega

/-- For `n ≥ N_*`, `q ≤ 2 b_n` and a central history `h`, `3^q ω(h) < 2^{-8}`. -/
private theorem three_pow_mul_weight_lt {t : ℚ} {n q : ℕ} (hn : generationThreshold ≤ n)
    (hq : q ≤ 2 * scale n) {h : Fin n → Word} (hh : h ∈ centralHistories t n) :
    (3 : ℚ) ^ q * (concatWord h).weight < 1 / 256 := by
  have hW := weight_concatWord_mul_sixteen_pow_scale_le hh
  rw [scale_zero] at hW
  have hWpos := Word.weight_pos (concatWord h)
  have hnat : 256 * 16 ^ 16544 * 9 ^ scale n < 16 ^ scale n :=
    two_pow_eight_mul_sixteen_pow_mul_nine_pow_lt
      (lt_of_lt_of_le (by norm_num) (le_scale_div_five_of_generationThreshold_le hn))
  have hrat : (256 : ℚ) * 16 ^ 16544 * 9 ^ scale n < 16 ^ scale n := by exact_mod_cast hnat
  set b := scale n
  generalize (16 : ℚ) ^ 16544 = K at hrat hW
  have h3 : (3 : ℚ) ^ q ≤ 9 ^ b :=
    calc (3 : ℚ) ^ q ≤ 3 ^ (2 * b) := pow_le_pow_right₀ (by norm_num) hq
      _ = 9 ^ b := by rw [pow_mul]; norm_num
  have h16 : (0 : ℚ) < 16 ^ b := by positivity
  have h1 : (3 : ℚ) ^ q * (concatWord h).weight * 16 ^ b ≤ 9 ^ b * K :=
    calc (3 : ℚ) ^ q * (concatWord h).weight * 16 ^ b
        = 3 ^ q * ((concatWord h).weight * 16 ^ b) := by ring
      _ ≤ 9 ^ b * K := by gcongr
  have h2 : (3 : ℚ) ^ q * (concatWord h).weight * 16 ^ b < 1 / 256 * 16 ^ b := by
    linarith
  exact lt_of_mul_lt_mul_right h2 h16.le

/-- **A fibre of the histogram.** For an odd positive integer `t`, `n ≥ N_*`, `q ≤ 2 b_n`,
`y ∈ G_q` and integers `D, A`, the histories `h ∈ 𝓗_n(t)` with `D(h) = D`, `A(h) = A` and
`R_h ≡ y (mod 3^q)` satisfy `3^q ∑ ω(h) < 97/128`. -/
@[collatz_pos_dens "lem_s05_hist_fiber_bound"]
theorem three_pow_mul_finsum_weight_histFiber_le {t : ℤ} (hodd : Odd t) (htpos : 0 < t)
    {n q : ℕ} (hn : generationThreshold ≤ n) (hq : q ≤ 2 * scale n) (y : ResidueGroup q) (D A : ℤ) :
    (3 : ℝ) ^ q * ∑ᶠ (h : Fin n → Word) (_ : h ∈ centralHistories t n ∧
        (historyDepth h : ℤ) = D ∧ ((concatWord h).valSum : ℤ) = A ∧
        ∃ r : ℤ, (r : ℚ) = historyEndpoint t h ∧ (r : ResidueGroup q) = y),
      ((concatWord h).weight : ℝ) < 97 / 128 := by
  set S : Set (Fin n → Word) := {h | h ∈ centralHistories t n ∧
        (historyDepth h : ℤ) = D ∧ ((concatWord h).valSum : ℤ) = A ∧
        ∃ r : ℤ, (r : ℚ) = historyEndpoint t h ∧ (r : ResidueGroup q) = y}
  change (3 : ℝ) ^ q * ∑ᶠ h ∈ S, ((concatWord h).weight : ℝ) < 97 / 128
  rcases S.eq_empty_or_nonempty with hSe | ⟨h₀, hh₀⟩
  · rw [hSe, finsum_mem_empty, mul_zero]
    norm_num
  set W : ℚ := (concatWord h₀).weight
  have hWpos : 0 < W := Word.weight_pos _
  have hwt : ∀ h ∈ S, (concatWord h).weight = W := by
    rintro h ⟨-, hD, hA, -⟩
    have hl : (concatWord h).length = (concatWord h₀).length := by
      have := hD.trans hh₀.2.1.symm
      exact_mod_cast this
    have hv : (concatWord h).valSum = (concatWord h₀).valSum := by
      exact_mod_cast hA.trans hh₀.2.2.1.symm
    simp only [W, Word.weight, hl, hv]
  set c : ℚ := W * 3 ^ q with hc
  have hcpos : 0 < c := by positivity
  set yt : ℤ := (y.val : ℤ)
  set k : (Fin n → Word) → ℤ := fun h => ((historyEndpoint t h).num - yt) / 3 ^ q
    with hk
  have hrt : ∀ h ∈ S, historyEndpoint t h = ((yt + 3 ^ q * k h : ℤ) : ℚ) := by
    rintro h ⟨-, -, -, r, hr, hry⟩
    simp only [hk]
    rw [← hr, Rat.num_intCast]
    exact congrArg _ (eq_val_add_three_pow_mul_ediv hry)
  have hsel : selEnd ≤ n := selEnd_le_generationThreshold_range.1.trans hn
  set lo : ℤ := ⌈((t : ℚ) - (3 / 4 + 1 / 2 ^ 8) - W * yt) / c⌉
  set hi : ℤ := ⌊((t : ℚ) - W * yt) / c⌋
  have hmaps : ∀ h ∈ S, k h ∈ Finset.Icc lo hi := by
    intro h hh
    obtain ⟨hlo, hhi⟩ := weight_mul_historyEndpoint_mem_Icc hsel hh.1
    rw [hrt h hh, hwt h hh] at hlo hhi
    push_cast at hlo hhi
    rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hcpos, le_div_iff₀ hcpos, hc]
    constructor <;> nlinarith
  have hinj : Set.InjOn k S := fun h hh h' hh' heq =>
    eq_of_historyEndpoint_eq hodd htpos hh.1 hh'.1
      (by exact_mod_cast hh.2.1.trans hh'.2.1.symm) (by rw [hrt h hh, hrt h' hh', heq])
  have hfin : S.Finite := Set.Finite.of_finite_image
    ((Finset.Icc lo hi).finite_toSet.subset (Set.image_subset_iff.mpr hmaps)) hinj
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_congr rfl (fun h hh => by rw [hwt h (hfin.mem_toFinset.mp hh)]),
    Finset.sum_const, nsmul_eq_mul]
  have hcard := card_toFinset_le_of_injOn_Icc hfin ⟨h₀, hh₀⟩
    (a := (t : ℚ) - (3 / 4 + 1 / 2 ^ 8) - W * yt) (b := (t : ℚ) - W * yt) hmaps hinj
  have hsmall : c < 1 / 256 := by
    have := three_pow_mul_weight_lt hn hq hh₀.1
    rw [hc, mul_comm]
    exact this
  have key : (3 : ℚ) ^ q * (hfin.toFinset.card * W) < 97 / 128 := by
    calc (3 : ℚ) ^ q * (hfin.toFinset.card * W) = c * hfin.toFinset.card := by ring
      _ ≤ c * ((((t : ℚ) - W * yt) - ((t : ℚ) - (3 / 4 + 1 / 2 ^ 8) - W * yt)) / c + 1) := by
          gcongr
      _ = (3 / 4 + 1 / 2 ^ 8) + c := by field_simp; ring
      _ < 97 / 128 := by norm_num at hsmall ⊢; linarith
  have key' := (Rat.cast_lt (K := ℝ)).mpr key
  push_cast at key'
  exact key'

end CollatzPosDens
