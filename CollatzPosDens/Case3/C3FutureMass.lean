/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CrossingMass
public import CollatzPosDens.Case3.C3CrossingPartition
public import CollatzPosDens.Case3.C3CycRow
public import CollatzPosDens.Case3.C3H17RowCost
public import CollatzPosDens.Case3.C3H17TablePeriod
public import CollatzPosDens.Case3.C3H17TableRange
public import CollatzPosDens.Case3.C3H17Values
public import CollatzPosDens.Case3.C3InitialMass
public import CollatzPosDens.Case3.C3NineOrbit
public import CollatzPosDens.Case3.C3NineValuation
public import CollatzPosDens.Case3.C3PaidPassage
public import CollatzPosDens.Case3.C3RowTailExp
public import CollatzPosDens.StoppingTrace.TrPassageDeficit
public import CollatzPosDens.Transfer.S02StageRate

/-!
# Paid passage over a gap of at least `4096`

Let `ξ` be a unit and `e ∈ 𝒫` black (for `ε_*`) with gap `ω = gap(e) ≥ 4096`. Then the total
paid passage mass satisfies `∑_{x ∈ ℤ × ℤ} F̃_e(x) < b_* = 333407/10^6`.

By definition, `∑_x F̃_e(x) = ∑_{π ∈ Π_ω} bw^⊗(π) exp(-z_* N^*(e, π; |π|))`, the weights
`bw^⊗(π)`, `π ∈ Π_ω`, sum to `1`, and the first raw crossing sets `𝒞_ω(c, o, r)`, `c ≥ 2`,
`1 ≤ o ≤ c`, `r ≥ 1`, partition `Π_ω` and have mass `ϖ(c) 𝖱(r - 1, ω + o - c)`. Let `M₀` be an
integer with `2^{17} ∣ 3^n M₀ + 3^n ϑ(j(e), l_Δ)`; it is odd, and `s ∈ {1, 3, 5, 7}` is its class
modulo `8`. Put `g = ⌊9ω/32⌋`. On the crossing sets with `2 ≤ c ≤ 16` and `1 ≤ r ≤ g` the
discounted mass is at most `ϖ(c) 𝖱(r - 1, ω + o - c) ct_{c,o}(9^r M₀)`, so
```
∑_x F̃_e(x) ≤ 1 - ∑_{c=2}^{16} ϖ(c) ∑_{o=1}^{c} ∑_{r=1}^{g} 𝖱(r - 1, ω + o - c)
                    · (1 - ct_{c,o}(9^r M₀)).
```
Along a row `l = ω + o - c`, the sequence `k ↦ 1 - ct_{c,o}(9^k s)` has period `2^{14}`, mean
`1 - μʰ_{c,o,s}` and centred partial sums of range `rg_{c,o,s}`, and `M₀ ≡ 9^a s (mod 2^{17})`.
The periodic cost against a renewal row and the exponential tail of the row give
`∑_{r=1}^{g} 𝖱(r - 1, l)(1 - ct_{c,o}(9^r M₀)) ≥ (1 - μʰ_{c,o,s})/4 - rg_{c,o,s}/√(2(3l - 1))
- e^{-2ω/289}`. Summing with `W = ∑_{c=2}^{16} c ϖ(c) = 65459/16384`,
```
∑_x F̃_e(x) ≤ 1 - Sʰ_s/4 + Dʰ_s/√(2(3ω - 46)) + W e^{-2ω/289}
           ≤ 1 - Sʰ_s/4 + Dʰ_s/156 + W 2^{-40} < b_*,
```
since `2(3ω - 46) ≥ 156²` and `e^{2ω/289} ≥ e^{28} > 2^{40}`; the last comparison is exact
rational arithmetic with the values of `Sʰ_s`, `Dʰ_s`.

## Main results

* `CollatzPosDens.sub_le_sum_rawMass_mul_one_sub_c3H17Table_of_tail`: the deficit of one row,
  with the range term and the exponential tail.
* `CollatzPosDens.tsum_c3PaidPassage_lt_stageRate`: the paid passage bound
  `∑_x F̃_e(x) < b_*` at gaps `≥ 4096`.

## Implementation notes

The paid passage mass takes values in `[0, ∞]`, and `b_* ∈ ℚ` is embedded there through
`ENNReal.ofReal`. The standing assumption that `ξ` is a unit is an explicit hypothesis. The
decomposition of the passage mass is run directly against the total mass `1` of `Π_ω`: on a list
lying in one of the selected crossing sets the discount is bounded by that set's cost, and
elsewhere by `1`; so the full identity `∑ ϖ(c) 𝖱(r - 1, ω + o - c) = 1` over all triples is not
needed. The bound `e^{28} > 2^{40}` is obtained from `e^{28} = (e^1)^{28}` and the
partial sum `e ≥ ∑_{i=0}^{5} 1/i! = 163/60` of the exponential series, rather than from the partial
sum `∑_{i=0}^{40} 28^i/i!` at `28`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026],
  §10.4.
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

open Finset

/-- **The deficit of one row, with the range term.** Let `ω ≥ 680`, `o ≤ 17`,
`ω - 127 ≤ l ≤ ω`, and let `M₀`, `s` be integers with `s` odd and `M₀ ≡ s (mod 8)`. Then, with
`g = ⌊9ω/32⌋`,
`∑_{r=1}^{g} 𝖱(r - 1, l)(1 - ct_{c,o}(9^r M₀)) ≥
(1 - μʰ_{c,o,s})/4 - rg_{c,o,s}/√(2(3l - 1)) - e^{-2ω/289}`. -/
theorem sub_le_sum_rawMass_mul_one_sub_c3H17Table_of_tail {ω : ℕ} (hω : 680 ≤ ω) {c o : ℤ}
    (ho : o ≤ 17) {l : ℤ} (hl : (ω : ℤ) - 127 ≤ l) (hlω : l ≤ ω) {M₀ s : ℤ} (hs : Odd s)
    (hMs : M₀ ≡ s [ZMOD 8]) :
    ((1 - c3H17Mean c o s : ℚ) : ℝ) / 4 - (c3H17Range c o s : ℝ) / √(2 * (3 * (l : ℝ) - 1)) -
        Real.exp (-(2 * (ω : ℝ) / 289)) ≤
      ∑ r ∈ Icc 1 (9 * ω / 32),
        rawMass (r - 1) l * (1 - (c3H17Table c o (9 ^ r * M₀) : ℝ)) := by
  set f : ℕ → ℝ := fun r ↦ 1 - (c3H17Table c o (9 ^ r * M₀) : ℝ) with hf
  have hf1 : ∀ r, f r ≤ 1 := fun r ↦ by
    have := (c3H17Table_mem_Icc c o (9 ^ r * M₀)).1
    simp only [hf, sub_le_self_iff]
    exact_mod_cast this
  -- the orbit of `s` and the shift `a`
  have hM₀ : Odd M₀ := by
    have h := hMs
    rw [Int.ModEq] at h
    obtain ⟨k, hk⟩ := hs
    rw [Int.odd_iff]
    omega
  obtain ⟨a, -, ha⟩ := exists_nine_pow_mul_modEq hM₀ hs hMs
  set h : ℕ → ℝ := fun k ↦ 1 - (c3H17Table c o (9 ^ k * s) : ℝ) with hh
  have hshift : ∀ r, f r = h (r + a) := fun r ↦ by
    simp only [hf, hh]
    rw [c3H17Table_congr_two_pow ho (y := 9 ^ (r + a) * s)
      (by rw [pow_add, mul_assoc]; exact ha.mul_left _)]
  have hper : ∀ k, h (k + 2 ^ 14) = h k := fun k ↦ by
    simp only [hh, c3H17Table_nine_pow_add ho]
  set μ : ℝ := ((1 - c3H17Mean c o s : ℚ) : ℝ) with hμdef
  have hμ : μ = (1 / ((2 ^ 14 : ℕ) : ℝ)) * ∑ k ∈ range (2 ^ 14), h k := by
    have hmul := c3H17Mean_mul c o s
    simp only [hh, hμdef, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [← Rat.cast_sum, ← hmul]
    push_cast
    ring
  -- the centred partial sums of `h` are the negatives of those of the cost table
  set F : ℕ → ℝ := fun k ↦ ∑ j ∈ range k, (h j - μ) with hF
  have hFP : ∀ k, F k = -(c3H17CentredSum c o s k : ℝ) := fun k ↦ by
    simp only [hF, hh, hμdef, c3H17CentredSum]
    push_cast
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun j _ ↦ by ring
  set D : ℝ := (range (2 ^ 14 + 1)).sup' nonempty_range_add_one F -
    (range (2 ^ 14 + 1)).inf' nonempty_range_add_one F with hD
  have hDrg : D ≤ (c3H17Range c o s : ℝ) := by
    obtain ⟨k, hk, hkeq⟩ := exists_mem_eq_sup' nonempty_range_add_one F
    obtain ⟨m, hm, hmeq⟩ := exists_mem_eq_inf' nonempty_range_add_one F
    rw [hD, hkeq, hmeq, hFP, hFP]
    have := c3H17CentredSum_sub_le_c3H17Range c o s (k := m) (l := k)
      (Nat.lt_succ_iff.1 (mem_range.1 hm)) (Nat.lt_succ_iff.1 (mem_range.1 hk))
    have hc : ((c3H17CentredSum c o s m - c3H17CentredSum c o s k : ℚ) : ℝ) ≤
        (c3H17Range c o s : ℝ) := by exact_mod_cast this
    push_cast at hc
    linarith
  -- the periodic cost against the row `l`
  obtain ⟨L, hL⟩ : ∃ L : ℕ, (L : ℤ) = l := ⟨l.toNat, Int.toNat_of_nonneg (by omega)⟩
  subst hL
  have hL2 : 2 ≤ L := by omega
  obtain ⟨-, hcyc⟩ := tsum_rawMass_mul_periodic_ge hL2 (L := 2 ^ 14) (by norm_num) a hper hμ hD
  have hcastL : ((L : ℤ) : ℝ) = (L : ℝ) := Int.cast_natCast L
  rw [hcastL]
  have hsq : 0 ≤ √(2 * (3 * (L : ℝ) - 1)) := Real.sqrt_nonneg _
  have hDdiv : D / √(2 * (3 * (L : ℝ) - 1)) ≤
      (c3H17Range c o s : ℝ) / √(2 * (3 * (L : ℝ) - 1)) :=
    div_le_div_of_nonneg_right hDrg hsq
  -- the row as a finite sum over `1 ≤ r ≤ K`
  set g := 9 * ω / 32 with hg
  set K := g + L + 2 with hK
  have hzero : ∀ r ∉ range K, rawMass r (L : ℤ) * h (r + 1 + a) = 0 := fun r hr ↦ by
    have := rawMass_pred_eq_zero (l := L) (k := r + 1) (by simp at hr; omega)
    simp only [Nat.add_sub_cancel] at this
    rw [this, zero_mul]
  rw [tsum_eq_sum hzero] at hcyc
  have hreindex : ∑ r ∈ range K, rawMass r (L : ℤ) * h (r + 1 + a) =
      ∑ r ∈ Icc 1 K, rawMass (r - 1) (L : ℤ) * f r := by
    refine sum_nbij' (· + 1) (· - 1) (fun r hr ↦ ?_) (fun r hr ↦ ?_) (fun r _ ↦ by simp)
      (fun r hr ↦ ?_) (fun r _ ↦ ?_)
    · simp only [mem_range, mem_Icc] at hr ⊢
      omega
    · simp only [mem_range, mem_Icc] at hr ⊢
      omega
    · simp only [mem_Icc] at hr
      omega
    · simp only [Nat.add_sub_cancel, hshift]
  rw [hreindex] at hcyc
  -- the late tail
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 K) (fun r ↦ r ≤ g)
    (fun r ↦ rawMass (r - 1) (L : ℤ) * f r)
  have hfilt : (Icc 1 K).filter (fun r ↦ r ≤ g) = Icc 1 g := by
    ext r
    simp only [mem_filter, mem_Icc]
    omega
  rw [hfilt] at hsplit
  have hfloor : ⌊9 * (((ω : ℤ) : ℝ)) / 32⌋₊ = g := by
    rw [hg, Int.cast_natCast, ← Nat.floor_div_eq_div (K := ℝ)]
    push_cast
    rfl
  have htail : ∑ r ∈ (Icc 1 K).filter (fun r ↦ ¬ r ≤ g), rawMass (r - 1) (L : ℤ) * f r ≤
      Real.exp (-(2 * (ω : ℝ) / 289)) := by
    have hω' : (680 : ℤ) ≤ ω := by omega
    have hexp := sum_rawMass_late_tail_le_exp hω' hl hlω ((Icc 1 K).filter (fun r ↦ ¬ r ≤ g))
      fun r hr ↦ by
        rw [hfloor]
        simp only [mem_filter] at hr
        omega
    rw [Int.cast_natCast] at hexp
    calc ∑ r ∈ (Icc 1 K).filter (fun r ↦ ¬ r ≤ g), rawMass (r - 1) (L : ℤ) * f r
        ≤ ∑ r ∈ (Icc 1 K).filter (fun r ↦ ¬ r ≤ g), rawMass (r - 1) (L : ℤ) :=
          sum_le_sum fun r _ ↦ mul_le_of_le_one_right (rawMass_nonneg _ _) (hf1 r)
      _ ≤ _ := hexp
  have hsub : ∑ r ∈ Icc 1 g, rawMass (r - 1) (L : ℤ) * f r =
      ∑ r ∈ Icc 1 g, rawMass (r - 1) (L : ℤ) * (1 - (c3H17Table c o (9 ^ r * M₀) : ℝ)) := rfl
  rw [← hsub]
  linarith

/-- `e^{-2ω/289} ≤ 2^{-40}` for `ω ≥ 4096`. -/
private theorem exp_neg_two_mul_div_le_of_le {ω : ℝ} (hω : 4096 ≤ ω) :
    Real.exp (-(2 * ω / 289)) ≤ 1 / 2 ^ 40 := by
  have he : ∑ i ∈ range 6, (1 : ℝ) ^ i / i.factorial ≤ Real.exp 1 :=
    Real.sum_le_exp_of_nonneg zero_le_one 6
  norm_num [sum_range_succ, Nat.factorial] at he
  have h28 : (2 : ℝ) ^ 40 ≤ Real.exp 1 ^ 28 :=
    le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) he 28)
  rw [← Real.exp_nat_mul, mul_one] at h28
  calc Real.exp (-(2 * ω / 289)) ≤ Real.exp (-((28 : ℕ) : ℝ)) :=
        Real.exp_le_exp.2 (by push_cast; linarith)
    _ = 1 / Real.exp ((28 : ℕ) : ℝ) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / 2 ^ 40 := one_div_le_one_div_of_le (by positivity) h28

/-- **Paid passage over a gap of at least `4096`.** Let `ξ` be a unit and `e ∈ 𝒫` black (for
`ε_*`) with `ω = gap(e) ≥ 4096`. Then `∑_{x ∈ ℤ × ℤ} F̃_e(x) < b_* = 333407/10^6`. -/
@[collatz_pos_dens "lem_c3_future_mass"]
theorem tsum_c3PaidPassage_lt_stageRate {n : ℕ} {ξ : ResidueGroup n} {e : ℤ × ℤ}
    (hξ : IsResidueUnit ξ) (he : e ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) e)
    (hgap : 4096 ≤ trGap n ξ (epsStar : ℝ) e) :
    ∑' x : ℤ × ℤ, c3PaidPassage n ξ e x < ENNReal.ofReal (stageRate : ℝ) := by
  rw [tsum_c3PaidPassage_eq]
  obtain ⟨ω, hω⟩ : ∃ ω : ℕ, (ω : ℤ) = trGap n ξ (epsStar : ℝ) e :=
    ⟨_, Int.toNat_of_nonneg (by omega)⟩
  rw [← hω, Int.toNat_natCast]
  have hω4096 : 4096 ≤ ω := by omega
  have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
  set d : List (List ℤ × ℤ) → ℝ := fun π ↦ Real.exp (-(zStar : ℝ) * trCount n ξ e π π.length)
    with hd
  have hd0 : ∀ π, 0 ≤ d π := fun π ↦ (Real.exp_pos _).le
  have hd1 : ∀ π, d π ≤ 1 := fun π ↦
    Real.exp_le_one_iff.mpr (by nlinarith [trCount_nonneg (n := n) (ξ := ξ) e π π.length])
  have hdnn : ∀ π : trPassage ω, 0 ≤ trListWeight π.1 * d π.1 :=
    fun π ↦ mul_nonneg (trListWeight_nonneg _) (hd0 _)
  have hsum : Summable fun π : trPassage ω ↦ trListWeight π.1 * d π.1 :=
    (hasSum_trListWeight_trPassage ω).summable.of_nonneg_of_le hdnn
      fun π ↦ mul_le_of_le_one_right (trListWeight_nonneg _) (hd1 π.1)
  rw [← ENNReal.ofReal_tsum_of_nonneg hdnn hsum]
  refine (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast stageRate_pos)).mpr ?_
  -- the integer `M₀` and its class `s` modulo `8`
  set θ := bkTheta n ξ (bkJ e, (bkCanonTriangle n ξ (epsStar : ℝ) e he).l) with hθ
  have hε := epsStar_mem_bkRange (K := ℝ)
  obtain ⟨N, hN, hNodd⟩ := odd_three_pow_mul_bkTheta_bkColTop hξ hε.1 hε.2 he hb
  obtain ⟨u, v, huv⟩ : IsCoprime ((3 : ℤ) ^ n) (2 ^ 17) :=
    (Int.isCoprime_iff_gcd_eq_one.2 (by norm_num)).pow
  set M₀ : ℤ := -N * u with hM₀
  have hkZ : 3 ^ n * M₀ + N = 2 ^ 17 * (N * v) := by
    rw [hM₀]
    linear_combination (-N) * huv
  have hdvd : ∃ k : ℤ, (3 : ℝ) ^ n * M₀ + 3 ^ n * θ = 2 ^ 17 * k :=
    ⟨N * v, by rw [← hN]; exact_mod_cast hkZ⟩
  have hM₀odd : Odd M₀ := by
    have h3 : Odd (3 ^ n * M₀) := by
      rw [show 3 ^ n * M₀ = 2 * (2 ^ 16 * (N * v)) - N by linarith]
      exact (even_two_mul _).sub_odd hNodd
    exact (Int.odd_mul.1 h3).2
  set s : ℤ := M₀ % 8 with hs
  have hs7 : s ∈ ({1, 3, 5, 7} : Finset ℤ) := by
    rw [Int.odd_iff] at hM₀odd
    simp only [mem_insert, mem_singleton, hs]
    omega
  have hsodd : Odd s := by
    rw [Int.odd_iff]
    simp only [mem_insert, mem_singleton] at hs7
    omega
  have hMs : M₀ ≡ s [ZMOD 8] := (Int.mod_modEq M₀ 8).symm
  -- the decomposition along the crossing sets
  set g := 9 * ω / 32 with hg
  set I : Finset (ℤ × ℤ × ℕ) := (Icc (2 : ℤ) 16 ×ˢ (Icc (1 : ℤ) 16 ×ˢ Icc 1 g)).filter
    (fun t ↦ t.2.1 ≤ t.1) with hIdef
  have hI : ∀ t ∈ I, 2 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2 := by
    intro t ht
    simp only [hIdef, mem_filter, mem_product, mem_Icc] at ht
    omega
  set b : ℤ × ℤ × ℕ → ℝ := fun t ↦ (c3H17Table t.1 t.2.1 (9 ^ t.2.2 * M₀) : ℝ) with hbdef
  have hbound : ∀ t ∈ I, ∑' π : c3CrossingSet ω t.1 t.2.1 t.2.2, trListWeight π.1 * d π.1 ≤
      varpi t.1 * rawMass (t.2.2 - 1) (ω + t.2.1 - t.1) * b t := by
    intro t ht
    have ht' := ht
    simp only [hIdef, mem_filter, mem_product, mem_Icc] at ht'
    exact hb.tsum_c3CrossingSet_mul_exp_le_c3H17Table hξ he hω (by omega) M₀ hdvd ht'.1.1.1
      ht'.1.1.2 ht'.1.2.1.1 ht'.2 ht'.1.2.2.1 ht'.1.2.2.2
  have hmain := tsum_trPassage_mul_le_one_sub_sum ω hd0 hd1 I b hI hbound
  -- the deficit collected by the rows
  set E : ℝ := Real.exp (-(2 * (ω : ℝ) / 289)) with hE
  set Y : ℝ := √(2 * (3 * (ω : ℝ) - 46)) with hY
  have hωR : (4096 : ℝ) ≤ ω := by exact_mod_cast hω4096
  have hY156 : (156 : ℝ) ≤ Y := Real.le_sqrt_of_sq_le (by nlinarith)
  have hY0 : 0 < Y := by linarith
  have hrow : ∀ c ∈ Icc (2 : ℤ) 16, ∀ o ∈ Icc (1 : ℤ) c,
      ((1 - c3H17Mean c o s : ℚ) : ℝ) / 4 - (c3H17Range c o s : ℝ) / Y - E ≤
        ∑ r ∈ Icc 1 g,
          rawMass (r - 1) (ω + o - c) * (1 - (c3H17Table c o (9 ^ r * M₀) : ℝ)) := by
    intro c hc o ho
    rw [mem_Icc] at hc ho
    refine le_trans ?_ (sub_le_sum_rawMass_mul_one_sub_c3H17Table_of_tail (by omega)
      (by omega) (by omega) (by omega) hsodd hMs)
    have hl : 3 * (ω : ℝ) - 46 ≤ 3 * (((ω : ℤ) + o - c : ℤ) : ℝ) - 1 := by
      have : (3 * (ω : ℤ) - 46 : ℤ) ≤ 3 * ((ω : ℤ) + o - c) - 1 := by omega
      exact_mod_cast this
    have hsqle : Y ≤ √(2 * (3 * (((ω : ℤ) + o - c : ℤ) : ℝ) - 1)) :=
      Real.sqrt_le_sqrt (by linarith)
    have hdiv : (c3H17Range c o s : ℝ) / √(2 * (3 * (((ω : ℤ) + o - c : ℤ) : ℝ) - 1)) ≤
        (c3H17Range c o s : ℝ) / Y :=
      div_le_div_of_nonneg_left (by exact_mod_cast c3H17Range_nonneg c o s) hY0 hsqle
    linarith
  have hiter : ∑ t ∈ I, (1 - b t) * (varpi t.1 * rawMass (t.2.2 - 1) (ω + t.2.1 - t.1)) =
      ∑ c ∈ Icc (2 : ℤ) 16, varpi c * ∑ o ∈ Icc (1 : ℤ) c, ∑ r ∈ Icc 1 g,
        rawMass (r - 1) (ω + o - c) * (1 - (c3H17Table c o (9 ^ r * M₀) : ℝ)) := by
    rw [hIdef, sum_filter, sum_product]
    refine sum_congr rfl fun c hc ↦ ?_
    rw [sum_product, mul_sum]
    have hc' : c ≤ 16 := (mem_Icc.mp hc).2
    have hset : Icc (1 : ℤ) c = (Icc (1 : ℤ) 16).filter fun o ↦ o ≤ c := by
      ext o
      simp only [mem_Icc, mem_filter]
      omega
    rw [hset, sum_filter]
    refine sum_congr rfl fun o _ ↦ ?_
    split_ifs
    · rw [mul_sum]
      exact sum_congr rfl fun r _ ↦ by simp only [hbdef]; ring
    · simp
  have hlow : (c3H17S s : ℝ) / 4 - (c3H17Delta s : ℝ) / Y - 65459 / 16384 * E ≤
      ∑ t ∈ I, (1 - b t) * (varpi t.1 * rawMass (t.2.2 - 1) (ω + t.2.1 - t.1)) := by
    rw [hiter]
    have hSc := c3H17S_cast s
    have hDc := c3H17Delta_cast s
    calc (c3H17S s : ℝ) / 4 - (c3H17Delta s : ℝ) / Y - 65459 / 16384 * E
        = ∑ c ∈ Icc (2 : ℤ) 16, varpi c * ∑ o ∈ Icc (1 : ℤ) c,
            (((1 - c3H17Mean c o s : ℚ) : ℝ) / 4 - (c3H17Range c o s : ℝ) / Y - E) := by
          rw [hSc, hDc, ← sum_Icc_mul_varpi_eq, sum_div, sum_div, sum_mul, ← sum_sub_distrib,
            ← sum_sub_distrib]
          refine sum_congr rfl fun c hc ↦ ?_
          have hc0 : ((c + 1 - 1).toNat : ℝ) = (c : ℝ) := by
            have : ((c + 1 - 1).toNat : ℤ) = c := by
              have := (mem_Icc.1 hc).1
              omega
            exact_mod_cast this
          rw [sum_sub_distrib, sum_sub_distrib, ← sum_div, ← sum_div, sum_const, Int.card_Icc,
            nsmul_eq_mul, hc0]
          ring
      _ ≤ _ := sum_le_sum fun c hc ↦ mul_le_mul_of_nonneg_left (sum_le_sum (hrow c hc))
            (varpi_nonneg c)
  -- the final numerical comparison
  have hE40 : E ≤ 1 / 2 ^ 40 := exp_neg_two_mul_div_le_of_le hωR
  have hD0 : (0 : ℝ) ≤ (c3H17Delta s : ℝ) := by exact_mod_cast c3H17Delta_nonneg s
  have hDY : (c3H17Delta s : ℝ) / Y ≤ (c3H17Delta s : ℝ) / 156 :=
    div_le_div_of_nonneg_left hD0 (by norm_num) hY156
  have hfin : 1 - (c3H17S s : ℝ) / 4 + (c3H17Delta s : ℝ) / 156 + 65459 / 16384 * (1 / 2 ^ 40) <
      (stageRate : ℝ) := by
    have h := c3H17S_c3H17Delta_eq hs7
    rw [stageRate_cast]
    split_ifs at h with h17
    · rw [Prod.mk.injEq] at h
      rw [h.1, h.2]
      norm_num
    · rw [Prod.mk.injEq] at h
      rw [h.1, h.2]
      norm_num
  change ∑' π : trPassage ω, trListWeight π.1 * d π.1 < _
  nlinarith

end CollatzPosDens
