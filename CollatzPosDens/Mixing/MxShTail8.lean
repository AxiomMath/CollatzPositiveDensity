/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Transfer.MxGate
public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxShExposedPart
public import CollatzPosDens.Mixing.MxShLatePart
public import CollatzPosDens.Mixing.MxShLikelihood
public import CollatzPosDens.Mixing.MxShSplitOffset
public import CollatzPosDens.Mixing.MxShWidthSmall

/-!
# The tail of the offset of a random `d`-subset

Let `n ≥ n₀`, where `n₀ = CollatzPosDens.mxGateLevel = 2 ^ 80`, let `N, d ∈ ℕ` with `3 n ≤ 2 N`
and `|2 d - N| ≤ 2 h^sh_n + 4`, and let `x` be real with `0 < x ≤ 2 n ^ 2`. Then
$$\#\{S \subseteq \{1, \dots, N\} : |S| = d,\ \operatorname{Of}(S) \ge x\}
  \le \frac 8x \binom N d.$$

With `q = ν^sh_n`, split `S` at `q` (`CollatzPosDens.setOffset_eq_add_of_one_le`):
`Of(S) = Of(S ∩ {1, …, q}) + Y(S)` with `Y(S) = 3^{|S ∩ {1, …, q}|} 2^{-q} Of(T)`, where `T` is the
late part of `S`. So `Of(S) ≥ x` forces `Of(S ∩ {1, …, q}) ≥ 99x/100` or `Y(S) ≥ x/100`.

* The first event is bounded by the exposed-part bound
  `CollatzPosDens.card_setOffset_inter_Icc_ge_le` with `Λ = 100/99`, which applies by the
  likelihood bound `CollatzPosDens.shLikelihood_le`; it gives at most `70000 / (9801 x) · C(N, d)`
  sets.
* The second event is bounded by Markov's inequality applied to `√Y` and the late-part bound
  `CollatzPosDens.sum_powersetCard_sqrt_late_le`, giving at most `400 / √x · (39/40)^q C(N, d)`
  sets. Since `(39/40)^q ≤ e^{-q/40} ≤ n^{-2}` and `√x ≤ 2 n`, this is at most `C(N, d) / (100 x)`.

Finally `70000/9801 + 1/100 < 8`.

## Main results

* `CollatzPosDens.card_setOffset_ge_le_eight_div`: the tail bound above.

## Implementation notes

The bound `(39/40)^q ≤ n^{-256/5}` also holds; the weaker bound `n^{-2}` suffices and is what is
proved here. The hypothesis `|2 d - N| ≤ 2 h^sh_n + 4` is stated in `ℤ`.

## References

* [Mazur, *Collatz positive density*], §12.11.
-/

@[expose] public section

open Finset

namespace CollatzPosDens

/-- For `n ≥ 2 ^ 80` and `q = ν^sh_n`, `(39/40)^q n^2 ≤ 1`. -/
theorem thirtyNine_div_forty_pow_shNu_mul_sq_le {n : ℕ} (hn : 2 ^ 80 ≤ n) :
    (39 / 40 : ℝ) ^ shNu n * (n : ℝ) ^ 2 ≤ 1 := by
  have hn' : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn'
  have hL : (0 : ℝ) ≤ Real.log n :=
    le_trans (by norm_num) (le_log_of_two_pow_eighty_le (by exact_mod_cast hn))
  have hq := le_shNu n
  have h1 : (39 / 40 : ℝ) ^ shNu n ≤ Real.exp (-(shNu n : ℝ) / 40) := by
    rw [show -(shNu n : ℝ) / 40 = (shNu n : ℝ) * (-1 / 40) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (-1 / 40 : ℝ)]) _
  have h2 : (n : ℝ) ^ 2 = Real.exp (2 * Real.log n) := by
    rw [show (2 : ℝ) * Real.log n = ((2 : ℕ) : ℝ) * Real.log n by norm_num, Real.exp_nat_mul,
      Real.exp_log hn0]
  calc (39 / 40 : ℝ) ^ shNu n * (n : ℝ) ^ 2
      ≤ Real.exp (-(shNu n : ℝ) / 40) * Real.exp (2 * Real.log n) := by
        rw [← h2]; gcongr
    _ = Real.exp (-(shNu n : ℝ) / 40 + 2 * Real.log n) := (Real.exp_add _ _).symm
    _ ≤ Real.exp 0 := Real.exp_le_exp.2 (by linarith)
    _ = 1 := Real.exp_zero

/-- **The tail of the offset of a random `d`-subset.** Let `n ≥ n₀`, `N, d ∈ ℕ` with
`3 n ≤ 2 N` and `|2 d - N| ≤ 2 h^sh_n + 4`, and `0 < x ≤ 2 n ^ 2`. Then the number of `d`-subsets
`S` of `{1, …, N}` with `Of(S) ≥ x` is at most `8 / x · C(N, d)`. -/
@[collatz_pos_dens "lem_mx_sh_tail8"]
theorem card_setOffset_ge_le_eight_div {n N d : ℕ} (hn : mxGateLevel ≤ n) (hN : 3 * n ≤ 2 * N)
    (hd : |2 * (d : ℤ) - N| ≤ 2 * shWidth n + 4) {x : ℝ} (hx0 : 0 < x)
    (hx : x ≤ 2 * (n : ℝ) ^ 2) :
    (#{S ∈ powersetCard d (Icc 1 N) | x ≤ (setOffset S : ℝ)} : ℝ) ≤ 8 / x * N.choose d := by
  rw [mxGateLevel_def] at hn
  set q := shNu n with hqdef
  set h := shWidth n with hhdef
  set C : ℝ := (N.choose d : ℝ) with hC
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have hn' : (2 : ℝ) ^ 80 ≤ n := by exact_mod_cast hn
  have hnbig : 80000 ≤ n := le_trans (by norm_num) hn
  have hh : 21600 * h ≤ n := mul_shWidth_le hn
  have hq1 : 1 ≤ q := shNu_pos (le_trans (by norm_num) hn)
  have hq400 : 400 * q ≤ n := by
    have hE := shNu_mul_le hn
    rw [← hqdef, ← hhdef] at hE
    have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have : (400 : ℝ) * q ≤ n := by
      have h0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      nlinarith
    exact_mod_cast this
  obtain ⟨hd1, hd2⟩ := abs_le.1 hd
  have hqN : q + 2 ≤ N := by omega
  have hdN : d ≤ N := by omega
  have hlate : 100 * d ≤ 51 * (N - q - 1) := by omega
  have hM2 : 2 * max d (N - d) ≤ N + 2 * h + 4 := by omega
  have hM : ((max d (N - d) : ℕ) : ℝ) ≤ N / 2 + h + 2 := by
    have : (2 * max d (N - d) : ℝ) ≤ N + 2 * h + 4 := by exact_mod_cast hM2
    linarith
  have hlik := shLikelihood_le hn hN (Nat.cast_nonneg _) hM
  rw [← hqdef] at hlik
  have hΛ : ((max d (N - d) : ℕ) : ℝ) ^ q ≤ 100 / 99 * (2 : ℝ)⁻¹ ^ q * ((N - q : ℕ) : ℝ) ^ q := by
    rwa [Nat.cast_sub (by omega), inv_pow]
  have hexp := card_setOffset_inter_Icc_ge_le (y := 99 / 100 * x) (by omega) hdN hΛ (by positivity)
  set Y : Finset ℕ → ℝ := fun S => (3 : ℝ) ^ #(S ∩ Icc 1 q) * ((2 : ℝ) ^ q)⁻¹ *
    (setOffset ((S.filter (q < ·)).image (· - q)) : ℝ) with hY
  have hlatesum := sum_powersetCard_sqrt_late_le hqN hlate
  set P := powersetCard d (Icc 1 N) with hP
  set A₂ := {S ∈ P | x / 100 ≤ Y S} with hA₂
  set s := √x with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hx0
  have hsx : s ^ 2 = x := Real.sq_sqrt hx0.le
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs2n : s ≤ 2 * n := by nlinarith
  have hmarkov : (#A₂ : ℝ) * (s / 10) ≤ 40 * (39 / 40 : ℝ) ^ q * C := by
    calc (#A₂ : ℝ) * (s / 10) = ∑ _S ∈ A₂, √(x / 100) := by
          rw [sum_const, nsmul_eq_mul, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 100),
            show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      _ ≤ ∑ S ∈ A₂, √(Y S) := sum_le_sum fun S hS => Real.sqrt_le_sqrt (mem_filter.1 hS).2
      _ ≤ ∑ S ∈ P, √(Y S) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Real.sqrt_nonneg _
      _ ≤ 40 * (39 / 40 : ℝ) ^ q * C := hlatesum
  have hr := thirtyNine_div_forty_pow_shNu_mul_sq_le hn
  rw [← hqdef] at hr
  set r : ℝ := (39 / 40 : ℝ) ^ q with hr_def
  have hr0 : 0 ≤ r := by positivity
  have hnr : 80000 * n * r ≤ 1 := by
    have h80 : (80000 : ℝ) ≤ n := by exact_mod_cast hnbig
    nlinarith
  have hA₂ : (#A₂ : ℝ) ≤ 1 / (100 * x) * C := by
    rw [← hsx, div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    have hA0 : (0 : ℝ) ≤ #A₂ := Nat.cast_nonneg _
    calc (#A₂ : ℝ) * (100 * s ^ 2) = 1000 * s * ((#A₂ : ℝ) * (s / 10)) := by ring
      _ ≤ 1000 * s * (40 * r * C) := by gcongr
      _ = 40000 * s * r * C := by ring
      _ ≤ 40000 * (2 * n) * r * C := by gcongr
      _ = (80000 * n * r) * C := by ring
      _ ≤ 1 * C := by gcongr
      _ = C := one_mul C
  have hsub : {S ∈ P | x ≤ (setOffset S : ℝ)} ⊆
      {S ∈ P | 99 / 100 * x ≤ (setOffset (S ∩ Icc 1 q) : ℝ)} ∪ A₂ := by
    intro S hS
    rw [mem_filter] at hS
    have hS1 : ∀ s ∈ S, 1 ≤ s := fun s hs =>
      (mem_Icc.1 ((mem_powersetCard.1 hS.1).1 hs)).1
    have hsplit := setOffset_eq_add_of_one_le hS1 q
    have hsplitR : (setOffset S : ℝ) = (setOffset (S ∩ Icc 1 q) : ℝ) + Y S := by
      rw [hY, hsplit]; push_cast; ring
    rw [mem_union, mem_filter, mem_filter]
    by_contra hcon
    push Not at hcon
    have h1 := hcon.1 hS.1
    have h2 := hcon.2 hS.1
    linarith [hS.2]
  have hcard : (#{S ∈ P | x ≤ (setOffset S : ℝ)} : ℝ) ≤
      #{S ∈ P | 99 / 100 * x ≤ (setOffset (S ∩ Icc 1 q) : ℝ)} + #A₂ := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have hexp' : 7 * (100 / 99 : ℝ) / (99 / 100 * x + 2) * C ≤ 70000 / (9801 * x) * C := by
    refine mul_le_mul_of_nonneg_right ?_ hC0
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc (#{S ∈ P | x ≤ (setOffset S : ℝ)} : ℝ)
      ≤ 70000 / (9801 * x) * C + 1 / (100 * x) * C := by linarith
    _ = (70000 / 9801 + 1 / 100) / x * C := by field_simp
    _ ≤ 8 / x * C := by gcongr; norm_num

end CollatzPosDens
