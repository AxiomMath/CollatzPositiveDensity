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
public import CollatzPosDens.FirstCrossing.Scales
public import CollatzPosDens.FirstCrossing.ScalesB444
public import CollatzPosDens.Seed.History
public import CollatzPosDens.Seed.HistoryDetermined
public import CollatzPosDens.Seed.HistoryWeightSmall
public import CollatzPosDens.Seed.SelectedOffset
public import CollatzPosDens.Transfer.ResidueGroup

/-!
# A fibre of the residue histogram

Let `M` be an odd positive integer, `n ≥ 444`, `0 ≤ q ≤ 2 b_n`, `y ∈ G_q`, and let `D, A` be
integers. Then
$$3^q \sum_{h ∈ 𝓗_n(M),\ D(h) = D,\ A(h) = A,\ R_h ≡ y \ (3^q)} ω(h) ≤ \tfrac{277}{128}.$$

All histories in the fibre share the weight `W = 3^D 2^{-A}`. By the affine identity
`M = W R_h + off(h)` and the offset bound `85/256 ≤ off(h) ≤ 637/256` for selected tuples, the
endpoints `R_h` lie in an interval of length `(69/32)/W`. They are pairwise distinct: words of
equal length admissible from `M` with equal sources are equal, and a history is determined by
its concatenated word. Hence at most `(69/32)/(W 3^q) + 1` of them are congruent to `y`, and the
left side is at most `69/32 + 3^q W`. Finally `W 16^{b_n} ≤ 16^{b_0}`, `3^q ≤ 9^{b_n}` and
`b_n ≥ b_{444} = 16544` give `3^q W < 1/128`.

## Main results

* `CollatzPosDens.three_pow_mul_finsum_weight_histFiber_le`: the fibre bound.

## Implementation notes

As in `CollatzPosDens.residueHistogram`, the sum is a `finsum` over the fibre and the
congruence `R_h ≡ y (mod 3^q)` reads "`R_h` is an integer `r` with `r ≡ y (mod 3^q)`". The
proof shows that the fibre is finite, so the `finsum` is a finite sum. The depth and valuation
sum of a history are natural numbers; the conditions `D(h) = D` and `A(h) = A` are stated after
casting them to `ℤ`, so `D` and `A` are arbitrary integers.

## References

* [Mazur, *Collatz positive density*], §17.4.
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

/-- For a central history `h` of generation `n ≥ 5`,
`M - 637/256 ≤ ω(h) R_h ≤ M - 85/256`. -/
private theorem weight_mul_historyEndpoint_mem_Icc {M : ℚ} {n : ℕ} (hn : 5 ≤ n)
    {h : Fin n → Word} (hh : h ∈ centralHistories M n) :
    M - 637 / 256 ≤ (concatWord h).weight * historyEndpoint M h ∧
      (concatWord h).weight * historyEndpoint M h ≤ M - 85 / 256 := by
  have haff := eq_weight_mul_src_add_off (concatWord h) M
  rw [← historyEndpoint_eq_src] at haff
  obtain ⟨h₀, h₁⟩ := off_concatWord_mem_Icc_of_mem_selectedTuples hn hh.1
  constructor <;> linarith

/-- For an odd `M > 0`, a central history is determined by its depth and its endpoint. -/
private theorem eq_of_historyEndpoint_eq {M : ℤ} (hodd : Odd M) (hM : 0 < M) {n : ℕ}
    {h h' : Fin n → Word} (hh : h ∈ centralHistories M n) (hh' : h' ∈ centralHistories M n)
    (hd : historyDepth h = historyDepth h') (he : historyEndpoint M h = historyEndpoint M h') :
    h = h' := by
  rw [historyEndpoint_eq_src, historyEndpoint_eq_src] at he
  have hw := Admissible.eq_of_src_eq hM hodd hd hh.2 hh'.2 he
  exact (historyDetermined (w' := []) (w'' := []) scale cap
    (selectedTuples_mem_centralFamily hh.1) (selectedTuples_mem_centralFamily hh'.1)
    (by rw [hw])).1

/-- For `n ≥ 444`, `q ≤ 2 b_n` and a central history `h`, `3^q ω(h) < 1/128`. -/
private theorem three_pow_mul_weight_lt {M : ℚ} {n q : ℕ} (hn : 444 ≤ n) (hq : q ≤ 2 * scale n)
    {h : Fin n → Word} (hh : h ∈ centralHistories M n) :
    (3 : ℚ) ^ q * (concatWord h).weight < 1 / 128 := by
  have hW := weight_concatWord_mul_sixteen_pow_scale_le hh
  have hWpos := Word.weight_pos (concatWord h)
  have hb : 60 ≤ scale n := by
    have := scale_monotone hn
    rw [scale_444] at this
    omega
  set b := scale n
  have h3 : (3 : ℚ) ^ q ≤ 9 ^ b :=
    calc (3 : ℚ) ^ q ≤ 3 ^ (2 * b) := pow_le_pow_right₀ (by norm_num) hq
      _ = 9 ^ b := by rw [pow_mul]; norm_num
  have h916 : ((9 : ℚ) / 16) ^ b ≤ (9 / 16) ^ 60 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hb
  have h16 : (0 : ℚ) < 16 ^ b := by positivity
  rw [scale_zero] at hW
  have key : (3 : ℚ) ^ q * (concatWord h).weight * 16 ^ b ≤ 16 ^ 9 * 9 ^ b :=
    calc (3 : ℚ) ^ q * (concatWord h).weight * 16 ^ b
        = 3 ^ q * ((concatWord h).weight * 16 ^ b) := by ring
      _ ≤ 9 ^ b * 16 ^ 9 := by gcongr
      _ = 16 ^ 9 * 9 ^ b := by ring
  have : (16 : ℚ) ^ 9 * 9 ^ b < 1 / 128 * 16 ^ b := by
    have e : (9 : ℚ) ^ b = (9 / 16) ^ b * 16 ^ b := by rw [div_pow]; field_simp
    rw [e]
    have : (16 : ℚ) ^ 9 * (9 / 16) ^ 60 < 1 / 128 := by norm_num
    nlinarith
  exact lt_of_mul_lt_mul_right (key.trans_lt this) h16.le

/-- **A fibre of the histogram.** For an odd positive integer `M`, `n ≥ 444`, `q ≤ 2 b_n`,
`y ∈ G_q` and integers `D, A`, the histories `h ∈ 𝓗_n(M)` with `D(h) = D`, `A(h) = A` and
`R_h ≡ y (mod 3^q)` satisfy `3^q ∑ ω(h) ≤ 277/128`. -/
@[collatz_pos_dens "lem_s05_hist_fiber_bound"]
theorem three_pow_mul_finsum_weight_histFiber_le {M : ℤ} (hodd : Odd M) (hMpos : 0 < M)
    {n q : ℕ} (hn : 444 ≤ n) (hq : q ≤ 2 * scale n) (y : ResidueGroup q) (D A : ℤ) :
    (3 : ℝ) ^ q * ∑ᶠ (h : Fin n → Word) (_ : h ∈ centralHistories M n ∧
        (historyDepth h : ℤ) = D ∧ ((concatWord h).valSum : ℤ) = A ∧
        ∃ r : ℤ, (r : ℚ) = historyEndpoint M h ∧ (r : ResidueGroup q) = y),
      ((concatWord h).weight : ℝ) ≤ 277 / 128 := by
  set S : Set (Fin n → Word) := {h | h ∈ centralHistories M n ∧
        (historyDepth h : ℤ) = D ∧ ((concatWord h).valSum : ℤ) = A ∧
        ∃ r : ℤ, (r : ℚ) = historyEndpoint M h ∧ (r : ResidueGroup q) = y}
  change (3 : ℝ) ^ q * ∑ᶠ h ∈ S, ((concatWord h).weight : ℝ) ≤ 277 / 128
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
  set t : (Fin n → Word) → ℤ := fun h => ((historyEndpoint M h).num - yt) / 3 ^ q with ht
  have hrt : ∀ h ∈ S, historyEndpoint M h = ((yt + 3 ^ q * t h : ℤ) : ℚ) := by
    rintro h ⟨-, -, -, r, hr, hry⟩
    simp only [ht]
    rw [← hr, Rat.num_intCast]
    exact congrArg _ (eq_val_add_three_pow_mul_ediv hry)
  have hn5 : 5 ≤ n := by omega
  set lo : ℤ := ⌈((M : ℚ) - 637 / 256 - W * yt) / c⌉
  set hi : ℤ := ⌊((M : ℚ) - 85 / 256 - W * yt) / c⌋
  have hmaps : ∀ h ∈ S, t h ∈ Finset.Icc lo hi := by
    intro h hh
    obtain ⟨hlo, hhi⟩ := weight_mul_historyEndpoint_mem_Icc hn5 hh.1
    rw [hrt h hh, hwt h hh] at hlo hhi
    push_cast at hlo hhi
    rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hcpos, le_div_iff₀ hcpos, hc]
    constructor <;> nlinarith
  have hinj : Set.InjOn t S := fun h hh h' hh' heq =>
    eq_of_historyEndpoint_eq hodd hMpos hh.1 hh'.1
      (by exact_mod_cast hh.2.1.trans hh'.2.1.symm) (by rw [hrt h hh, hrt h' hh', heq])
  have hfin : S.Finite := Set.Finite.of_finite_image
    ((Finset.Icc lo hi).finite_toSet.subset (Set.image_subset_iff.mpr hmaps)) hinj
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_congr rfl (fun h hh => by rw [hwt h (hfin.mem_toFinset.mp hh)]),
    Finset.sum_const, nsmul_eq_mul]
  have hcard := card_toFinset_le_of_injOn_Icc hfin ⟨h₀, hh₀⟩
    (a := (M : ℚ) - 637 / 256 - W * yt) (b := (M : ℚ) - 85 / 256 - W * yt) hmaps hinj
  have hsmall : c < 1 / 128 := by
    have := three_pow_mul_weight_lt hn hq hh₀.1
    rw [hc, mul_comm]
    exact this
  have key : (3 : ℚ) ^ q * (hfin.toFinset.card * W) ≤ 277 / 128 := by
    calc (3 : ℚ) ^ q * (hfin.toFinset.card * W) = c * hfin.toFinset.card := by ring
      _ ≤ c * ((((M : ℚ) - 85 / 256 - W * yt) - ((M : ℚ) - 637 / 256 - W * yt)) / c + 1) := by
          gcongr
      _ = 69 / 32 + c := by field_simp; ring
      _ ≤ 277 / 128 := by linarith
  have key' := (Rat.cast_le (K := ℝ)).mpr key
  push_cast at key'
  exact key'

end CollatzPosDens
