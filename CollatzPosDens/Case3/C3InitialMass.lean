/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3CrossingMass
public import CollatzPosDens.Case3.C3CrossingPartition
public import CollatzPosDens.Case3.C3H17RowCost
public import CollatzPosDens.Case3.C3H17TablePeriod
public import CollatzPosDens.Case3.C3H17TableRange
public import CollatzPosDens.Case3.C3H17Values
public import CollatzPosDens.Case3.C3NarrowRow
public import CollatzPosDens.Case3.C3NineOrbit
public import CollatzPosDens.Case3.C3NineValuation
public import CollatzPosDens.Case3.C3PaidPassage
public import CollatzPosDens.Case3.C3RowResidue
public import CollatzPosDens.StoppingTrace.TrPassageDeficit
public import CollatzPosDens.Transfer.S02Qmass

/-!
# Orbit-averaged initial mass

Let `ξ` be a unit and `e ∈ 𝒫` black (for `ε_*`) with gap `ω = gap(e) ≥ 2^{34}`. Then the total
paid passage mass satisfies `∑_{x ∈ ℤ × ℤ} F̃_e(x) < q_mass = 38177/125000`.

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
Along a row, `r ↦ 1 - ct_{c,o}(9^r M₀)` has period `2^{14}` and, since `M₀ ≡ 9^a s (mod 2^{17})`,
its mean over a period is `1 - μʰ_{c,o,s}`. The crossing-index residue weights and the late tail
of the row give `∑_{r=1}^{g} 𝖱(r - 1, l)(1 - ct_{c,o}(9^r M₀)) ≥ (1 - μʰ_{c,o,s})/4 - E` with
`E = 8192 (3/8)^{31} + 37/2^{34}`, and since `∑_{c=2}^{16} c ϖ(c) ≤ 4` and `Sʰ_s` is at least
`149160843578876007/53687091200000000`,
`∑_x F̃_e(x) ≤ 1 - Sʰ_s/4 + 4E < q_mass`.

## Main results

* `CollatzPosDens.tsum_c3PaidPassage_eq`:
  `∑_x F̃_e(x) = ∑_{π ∈ Π_ω} bw^⊗(π) exp(-z_* N^*(e, π; |π|))`.
* `CollatzPosDens.tsum_trPassage_mul_le_one_sub_sum`: the deficit of a passage collected from
  bounds on finitely many first raw crossing sets.
* `CollatzPosDens.c3H17Table_nine_pow_add`: the cost table along the orbit `9^k x` has period
  `2^{14}`.
* `CollatzPosDens.sum_Icc_mul_varpi_eq`: `∑_{c=2}^{16} c ϖ(c) = 65459/16384`.
* `CollatzPosDens.sub_le_sum_rawMass_mul_one_sub_c3H17Table`: the deficit of one row.
* `CollatzPosDens.tsum_c3PaidPassage_lt_qMass`: the initial paid mass bound
  `∑_x F̃_e(x) < q_mass`.

## Implementation notes

The paid passage mass takes values in `[0, ∞]`, and `q_mass ∈ ℚ` is embedded there through
`ENNReal.ofReal`. The standing assumption that `ξ` is a unit is an explicit hypothesis. The
decomposition of the passage mass is run directly against the total mass `1` of `Π_ω`: on a list
lying in one of the selected crossing sets the discount is bounded by that set's cost, and
elsewhere by `1`; so the full identity `∑ ϖ(c) 𝖱(r - 1, ω + o - c) = 1` over all triples is not
needed. The error term `8192 e^{-(l-1)/2^{29}}` is bounded through `e^{-1} ≤ 3/8`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The total paid passage mass is the discounted weight of the passage lists above the gap:
`∑_x F̃_e(x) = ∑_{π ∈ Π_ω} bw^⊗(π) exp(-z_* N^*(e, π; |π|))`, `ω = gap(e)`. -/
theorem tsum_c3PaidPassage_eq (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) :
    ∑' x : ℤ × ℤ, c3PaidPassage n ξ e x =
      ∑' π : trPassage (trGap n ξ (epsStar : ℝ) e).toNat,
        ENNReal.ofReal
          (trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length)) := by
  simp only [c3PaidPassage]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun π ↦ ?_
  rw [tsum_eq_single (chBlockPath π.1 π.1.length)]
  · simp
  · intro x hx
    simp [Ne.symm hx]

/-- **Deficit of a passage from first raw crossing sets.** Let `ω ∈ ℕ`, let `d` be a function on
lists with values in `[0, 1]`, let `I` be a finite set of triples `(c, o, r)` with `c ≥ 2`,
`1 ≤ o ≤ c` and `r ≥ 1`, and let `b_{c,o,r}` be reals with
`∑_{π ∈ 𝒞_ω(c,o,r)} bw^⊗(π) d(π) ≤ ϖ(c) 𝖱(r - 1, ω + o - c) b_{c,o,r}` for `(c, o, r) ∈ I`. Then
`∑_{π ∈ Π_ω} bw^⊗(π) d(π) ≤ 1 - ∑_{(c,o,r) ∈ I} (1 - b_{c,o,r}) ϖ(c) 𝖱(r - 1, ω + o - c)`. -/
theorem tsum_trPassage_mul_le_one_sub_sum (ω : ℕ) {d : List (List ℤ × ℤ) → ℝ}
    (hd0 : ∀ π, 0 ≤ d π) (hd1 : ∀ π, d π ≤ 1) (I : Finset (ℤ × ℤ × ℕ)) (b : ℤ × ℤ × ℕ → ℝ)
    (hI : ∀ t ∈ I, 2 ≤ t.1 ∧ 1 ≤ t.2.1 ∧ t.2.1 ≤ t.1 ∧ 1 ≤ t.2.2)
    (hb : ∀ t ∈ I, ∑' π : c3CrossingSet ω t.1 t.2.1 t.2.2, trListWeight π.1 * d π.1 ≤
      varpi t.1 * rawMass (t.2.2 - 1) (ω + t.2.1 - t.1) * b t) :
    ∑' π : trPassage ω, trListWeight π.1 * d π.1 ≤
      1 - ∑ t ∈ I, (1 - b t) * (varpi t.1 * rawMass (t.2.2 - 1) (ω + t.2.1 - t.1)) := by
  set D : List (List ℤ × ℤ) → ℝ := fun π ↦ trListWeight π * d π with hD
  set X : ℤ × ℤ × ℕ → Set (List (List ℤ × ℤ)) := fun t ↦ c3CrossingSet ω t.1 t.2.1 t.2.2
    with hX
  set m : ℤ × ℤ × ℕ → ℝ := fun t ↦ varpi t.1 * rawMass (t.2.2 - 1) (ω + t.2.1 - t.1) with hm
  have hW0 : ∀ π, 0 ≤ trListWeight π := trListWeight_nonneg
  have hD0 : ∀ π, 0 ≤ D π := fun π ↦ mul_nonneg (hW0 π) (hd0 π)
  have hDW : ∀ π, D π ≤ trListWeight π := fun π ↦ mul_le_of_le_one_right (hW0 π) (hd1 π)
  have hP : HasSum ((trPassage ω).indicator trListWeight) 1 :=
    hasSum_subtype_iff_indicator.1 (hasSum_trListWeight_trPassage ω)
  have hXW : ∀ t ∈ I, HasSum ((X t).indicator trListWeight) (m t) := fun t ht ↦
    hasSum_subtype_iff_indicator.1
      (hasSum_trListWeight_c3CrossingSet ω (hI t ht).2.1 (hI t ht).2.2.1 (hI t ht).2.2.2)
  have hsumm : ∀ S : Set (List (List ℤ × ℤ)), Summable (S.indicator trListWeight) →
      Summable (S.indicator D) := fun S hS ↦
    hS.of_nonneg_of_le (fun π ↦ Set.indicator_nonneg (fun π _ ↦ hD0 π) π)
      (fun π ↦ Set.indicator_le_indicator (hDW π))
  have hXD : ∀ t ∈ I, HasSum ((X t).indicator D) (∑' π : X t, D π) := fun t ht ↦ by
    rw [_root_.tsum_subtype]
    exact (hsumm _ (hXW t ht).summable).hasSum
  have hPD : HasSum ((trPassage ω).indicator D) (∑' π : trPassage ω, D π) := by
    rw [_root_.tsum_subtype]
    exact (hsumm _ hP.summable).hasSum
  have hpt : ∀ π, (trPassage ω).indicator D π ≤ ∑ t ∈ I, (X t).indicator D π +
      ((trPassage ω).indicator trListWeight π - ∑ t ∈ I, (X t).indicator trListWeight π) := by
    intro π
    by_cases hex : ∃ t₀ ∈ I, π ∈ X t₀
    · obtain ⟨t₀, ht₀, hπ₀⟩ := hex
      have hπP : π ∈ trPassage ω := c3CrossingSet_subset_trPassage _ _ _ _ hπ₀
      have hne : ∀ t ∈ I, t ≠ t₀ → π ∉ X t := fun t ht hne hπ ↦ hne <|
        (existsUnique_mem_c3CrossingSet hπP).unique
          ⟨(hI t ht).1, (hI t ht).2.1, (hI t ht).2.2.1, (hI t ht).2.2.2, hπ⟩
          ⟨(hI t₀ ht₀).1, (hI t₀ ht₀).2.1, (hI t₀ ht₀).2.2.1, (hI t₀ ht₀).2.2.2, hπ₀⟩
      rw [sum_eq_single_of_mem t₀ ht₀ fun t ht h ↦ Set.indicator_of_notMem (hne t ht h) _,
        sum_eq_single_of_mem t₀ ht₀ fun t ht h ↦ Set.indicator_of_notMem (hne t ht h) _,
        Set.indicator_of_mem hπ₀, Set.indicator_of_mem hπ₀, Set.indicator_of_mem hπP,
        Set.indicator_of_mem hπP]
      linarith
    · push Not at hex
      rw [sum_eq_zero fun t ht ↦ Set.indicator_of_notMem (hex t ht) _,
        sum_eq_zero fun t ht ↦ Set.indicator_of_notMem (hex t ht) _]
      simpa using Set.indicator_le_indicator (s := trPassage ω) (hDW π)
  have hle := hasSum_le hpt hPD ((hasSum_sum hXD).add (hP.sub (hasSum_sum hXW)))
  have hA : ∑ t ∈ I, ∑' π : X t, D π ≤ ∑ t ∈ I, m t * b t := sum_le_sum hb
  have hsplit : ∑ t ∈ I, (1 - b t) * m t = ∑ t ∈ I, m t - ∑ t ∈ I, m t * b t := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun t _ ↦ by ring
  change ∑' π : trPassage ω, D π ≤ 1 - ∑ t ∈ I, (1 - b t) * m t
  linarith

/-- The sum of a function of period `L` over `L` consecutive naturals does not depend on the
starting point. -/
private theorem sum_range_add_of_periodic {M : Type*} [AddCommMonoid M] {g : ℕ → M} {L : ℕ}
    (h : ∀ k, g (k + L) = g k) (a : ℕ) :
    ∑ k ∈ range L, g (k + a) = ∑ k ∈ range L, g k := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [← ih]
    rcases L with _ | L
    · simp
    · rw [sum_range_succ, sum_range_succ' (fun k ↦ g (k + a))]
      simp only [add_assoc, add_comm 1 a, zero_add]
      rw [show L + (a + 1) = a + (L + 1) by ring, h]

/-- The cost table only depends on its argument modulo `2^{17}`, for `o ≤ 17`. -/
theorem c3H17Table_congr_two_pow {c o : ℤ} (ho : o ≤ 17) {x y : ℤ}
    (h : x ≡ y [ZMOD 2 ^ 17]) : c3H17Table c o x = c3H17Table c o y := by
  obtain ⟨k, hk⟩ := h.dvd
  rw [show y = x + k * 2 ^ 17 by linarith, c3H17Table_add_mul_two_pow c ho]

/-- `9^{2^{14}} ≡ 1 (mod 2^{17})`. -/
theorem nine_pow_two_pow_fourteen_modEq_one : (9 : ℤ) ^ 2 ^ 14 ≡ 1 [ZMOD 2 ^ 17] := by
  have h := two_pow_dvd_nine_pow_two_pow_sub_one 14
  have h1 : 1 ≤ 9 ^ 2 ^ 14 := Nat.one_le_pow (2 ^ 14) 9 (by norm_num)
  have h' : 9 ^ 2 ^ 14 ≡ 1 [MOD 2 ^ 17] := ((Nat.modEq_iff_dvd' h1).2 h).symm
  exact_mod_cast h'

/-- Multiplying by `9^{2^{14}}` does not change the cost table, for `o ≤ 17`:
`ct_{c,o}(9^{k + 2^{14}} x) = ct_{c,o}(9^k x)`. -/
theorem c3H17Table_nine_pow_add {c o : ℤ} (ho : o ≤ 17) (k : ℕ) (x : ℤ) :
    c3H17Table c o (9 ^ (k + 2 ^ 14) * x) = c3H17Table c o (9 ^ k * x) :=
  c3H17Table_congr_two_pow ho (by
    rw [pow_add, mul_comm ((9 : ℤ) ^ k), mul_assoc]
    calc (9 : ℤ) ^ 2 ^ 14 * (9 ^ k * x) ≡ 1 * (9 ^ k * x) [ZMOD 2 ^ 17] :=
          nine_pow_two_pow_fourteen_modEq_one.mul_right _
      _ = 9 ^ k * x := one_mul _)

/-- **The deficit of one row.** Let `ω ≥ 2^{34}`, `o ≤ 17`, `ω - 127 ≤ l ≤ ω`, and let `M₀`, `s`
be integers with `s` odd and `M₀ ≡ s (mod 8)`. Then, with `g = ⌊9ω/32⌋`,
`∑_{r=1}^{g} 𝖱(r - 1, l)(1 - ct_{c,o}(9^r M₀)) ≥ (1 - μʰ_{c,o,s})/4 - E` with
`E = 8192 (3/8)^{31} + 37/2^{34}`. -/
theorem sub_le_sum_rawMass_mul_one_sub_c3H17Table {ω : ℕ} (hω : 2 ^ 34 ≤ ω) {c o : ℤ}
    (ho : o ≤ 17) {l : ℤ} (hl : (ω : ℤ) - 127 ≤ l) (hlω : l ≤ ω) {M₀ s : ℤ} (hs : Odd s)
    (hMs : M₀ ≡ s [ZMOD 8]) :
    ((1 - c3H17Mean c o s : ℚ) : ℝ) / 4 - (8192 * (3 / 8) ^ 31 + 37 / 2 ^ 34) ≤
      ∑ r ∈ Icc 1 (9 * ω / 32),
        rawMass (r - 1) l * (1 - (c3H17Table c o (9 ^ r * M₀) : ℝ)) := by
  set f : ℕ → ℝ := fun r ↦ 1 - (c3H17Table c o (9 ^ r * M₀) : ℝ) with hf
  have hf0 : ∀ r, 0 ≤ f r := fun r ↦ by
    have := (c3H17Table_mem_Icc c o (9 ^ r * M₀)).2
    simp only [hf, sub_nonneg]
    exact_mod_cast this
  have hf1 : ∀ r, f r ≤ 1 := fun r ↦ by
    have := (c3H17Table_mem_Icc c o (9 ^ r * M₀)).1
    simp only [hf, sub_le_self_iff]
    exact_mod_cast this
  have hper : ∀ r, f (r + 2 ^ 14) = f r := fun r ↦ by
    simp only [hf, c3H17Table_nine_pow_add ho]
  -- the mean of `f` over a period
  have hM₀ : Odd M₀ := by
    have h := hMs
    rw [Int.ModEq] at h
    obtain ⟨k, hk⟩ := hs
    rw [Int.odd_iff]
    omega
  obtain ⟨a, -, ha⟩ := exists_nine_pow_mul_modEq hM₀ hs hMs
  have hshift : ∀ r, c3H17Table c o (9 ^ r * M₀) = c3H17Table c o (9 ^ (r + a) * s) := fun r ↦
    c3H17Table_congr_two_pow ho (by rw [pow_add, mul_assoc]; exact ha.mul_left _)
  have hmean : ∑ k ∈ range (2 ^ 14), f k = 2 ^ 14 * ((1 - c3H17Mean c o s : ℚ) : ℝ) := by
    have hg : ∀ k, c3H17Table c o (9 ^ (k + 2 ^ 14) * s) = c3H17Table c o (9 ^ k * s) :=
      fun k ↦ c3H17Table_nine_pow_add ho k s
    have hsum := sum_range_add_of_periodic (g := fun k ↦ c3H17Table c o (9 ^ k * s)) hg a
    have hmul := c3H17Mean_mul c o s
    simp only [hf, hshift, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, mul_one]
    rw [← Rat.cast_sum, hsum, ← hmul]
    push_cast
    ring
  -- the residue weights over a large range of indices
  set g := 9 * ω / 32 with hg
  set N := g + l.toNat + 2 with hN
  have hres := le_sum_rawMass_pred_mul (l := l) hf0 hf1 hper (Icc 1 N) fun r hr1 hr2 ↦
    mem_Icc.2 ⟨hr1, by omega⟩
  rw [hmean] at hres
  -- the late tail
  have hsplit := sum_filter_add_sum_filter_not (Icc 1 N) (fun r ↦ r ≤ g)
    (fun r ↦ rawMass (r - 1) l * f r)
  have hfilt : (Icc 1 N).filter (fun r ↦ r ≤ g) = Icc 1 g := by
    ext r
    simp only [mem_filter, mem_Icc]
    omega
  rw [hfilt] at hsplit
  have hfloor : ⌊9 * (((ω : ℤ) : ℝ)) / 32⌋₊ = g := by
    rw [hg, Int.cast_natCast, ← Nat.floor_div_eq_div (K := ℝ)]
    push_cast
    rfl
  have htail : ∑ r ∈ (Icc 1 N).filter (fun r ↦ ¬ r ≤ g), rawMass (r - 1) l * f r ≤
      37 / 2 ^ 34 := by
    have hω' : (12500000 : ℤ) ≤ ω := by omega
    have h37 := sum_rawMass_late_tail_le hω' hl hlω ((Icc 1 N).filter (fun r ↦ ¬ r ≤ g))
      fun r hr ↦ by
        rw [hfloor]
        simp only [mem_filter] at hr
        omega
    have hωR : (2 : ℝ) ^ 34 ≤ ((ω : ℤ) : ℝ) := by exact_mod_cast hω
    calc ∑ r ∈ (Icc 1 N).filter (fun r ↦ ¬ r ≤ g), rawMass (r - 1) l * f r
        ≤ ∑ r ∈ (Icc 1 N).filter (fun r ↦ ¬ r ≤ g), rawMass (r - 1) l :=
          sum_le_sum fun r _ ↦ mul_le_of_le_one_right (rawMass_nonneg _ _) (hf1 r)
      _ ≤ 37 / ((ω : ℤ) : ℝ) := h37
      _ ≤ 37 / 2 ^ 34 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hωR
  -- the exponential error
  have hexp : Real.exp (-((l : ℝ) - 1) / 2 ^ 29) ≤ (3 / 8) ^ 31 := by
    have hlR : (31 * 2 ^ 29 : ℝ) ≤ (l : ℝ) - 1 := by
      have : (31 * 2 ^ 29 : ℤ) ≤ l - 1 := by push_cast at hl ⊢; omega
      exact_mod_cast this
    have he1 : Real.exp (-1) ≤ 3 / 8 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.sum_le_exp_of_nonneg zero_le_one 4
      norm_num [sum_range_succ, Nat.factorial] at this
      linarith
    calc Real.exp (-((l : ℝ) - 1) / 2 ^ 29) ≤ Real.exp ((31 : ℕ) * (-1)) :=
          Real.exp_le_exp.2 (by
            rw [div_le_iff₀ (by positivity)]
            push_cast
            linarith)
      _ = Real.exp (-1) ^ 31 := Real.exp_nat_mul _ _
      _ ≤ (3 / 8) ^ 31 := pow_le_pow_left₀ (Real.exp_pos _).le he1 _
  have hsub : ∑ r ∈ Icc 1 g, rawMass (r - 1) l * f r =
      ∑ r ∈ Icc 1 g, rawMass (r - 1) l * (1 - (c3H17Table c o (9 ^ r * M₀) : ℝ)) := rfl
  rw [← hsub]
  have : 1 / (4 * 2 ^ 14) * (2 ^ 14 * ((1 - c3H17Mean c o s : ℚ) : ℝ)) =
      ((1 - c3H17Mean c o s : ℚ) : ℝ) / 4 := by ring
  rw [this] at hres
  nlinarith

/-- `∑_{c=2}^{16} c ϖ(c) = 65459/16384`. -/
theorem sum_Icc_mul_varpi_eq :
    ∑ c ∈ Icc (2 : ℤ) 16, (c : ℝ) * varpi c = 65459 / 16384 := by
  have hset : Icc (2 : ℤ) 16 = {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} := by
    decide
  rw [sum_congr rfl fun c hc ↦ by rw [varpi_of_two_le (mem_Icc.1 hc).1], hset]
  norm_num [sum_insert]

/-- **Orbit-averaged initial mass.** Let `ξ` be a unit and `e ∈ 𝒫` black (for `ε_*`) with
`ω = gap(e) ≥ 2^{34}`. Then `∑_{x ∈ ℤ × ℤ} F̃_e(x) < q_mass = 38177/125000`. -/
@[collatz_pos_dens "lem_c3_initial_mass"]
theorem tsum_c3PaidPassage_lt_qMass {n : ℕ} {ξ : ResidueGroup n} {e : ℤ × ℤ}
    (hξ : IsResidueUnit ξ) (he : e ∈ bkPoints) (hb : BkBlack n ξ (epsStar : ℝ) e)
    (hgap : 2 ^ 34 ≤ trGap n ξ (epsStar : ℝ) e) :
    ∑' x : ℤ × ℤ, c3PaidPassage n ξ e x < ENNReal.ofReal (qMass : ℝ) := by
  rw [tsum_c3PaidPassage_eq]
  obtain ⟨ω, hω⟩ : ∃ ω : ℕ, (ω : ℤ) = trGap n ξ (epsStar : ℝ) e :=
    ⟨_, Int.toNat_of_nonneg (by omega)⟩
  rw [← hω, Int.toNat_natCast]
  have hω34 : 2 ^ 34 ≤ ω := by omega
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
  refine (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast qMass_pos)).mpr ?_
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
  -- the lower bound on the aggregate deficit
  have hS : ((149160843578876007 / 53687091200000000 : ℚ) : ℝ) ≤ (c3H17S s : ℝ) := by
    have h := congrArg Prod.fst (c3H17S_c3H17Delta_eq hs7)
    simp only at h
    rw [h]
    split_ifs <;> norm_num
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
  set E : ℝ := 8192 * (3 / 8) ^ 31 + 37 / 2 ^ 34 with hE
  have hrow : ∀ c ∈ Icc (2 : ℤ) 16, ∀ o ∈ Icc (1 : ℤ) c,
      ((1 - c3H17Mean c o s : ℚ) : ℝ) / 4 - E ≤ ∑ r ∈ Icc 1 g,
        rawMass (r - 1) (ω + o - c) * (1 - (c3H17Table c o (9 ^ r * M₀) : ℝ)) := by
    intro c hc o ho
    rw [mem_Icc] at hc ho
    exact sub_le_sum_rawMass_mul_one_sub_c3H17Table hω34 (by omega) (by omega) (by omega)
      hsodd hMs
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
  have hlow : (c3H17S s : ℝ) / 4 - 4 * E ≤
      ∑ t ∈ I, (1 - b t) * (varpi t.1 * rawMass (t.2.2 - 1) (ω + t.2.1 - t.1)) := by
    rw [hiter]
    have hE0 : 0 ≤ E := by positivity
    have hcv : ∑ c ∈ Icc (2 : ℤ) 16, (c : ℝ) * varpi c * E ≤ 4 * E := by
      rw [← sum_mul, sum_Icc_mul_varpi_eq]
      exact mul_le_mul_of_nonneg_right (by norm_num) hE0
    have hSc := c3H17S_cast s
    calc (c3H17S s : ℝ) / 4 - 4 * E
        ≤ (c3H17S s : ℝ) / 4 - ∑ c ∈ Icc (2 : ℤ) 16, (c : ℝ) * varpi c * E :=
          sub_le_sub_left hcv _
      _ = ∑ c ∈ Icc (2 : ℤ) 16, varpi c *
            ∑ o ∈ Icc (1 : ℤ) c, (((1 - c3H17Mean c o s : ℚ) : ℝ) / 4 - E) := by
          rw [hSc, sum_div, ← sum_sub_distrib]
          refine sum_congr rfl fun c hc ↦ ?_
          have hc0 : ((c + 1 - 1).toNat : ℝ) = (c : ℝ) := by
            have : ((c + 1 - 1).toNat : ℤ) = c := by
              have := (mem_Icc.1 hc).1
              omega
            exact_mod_cast this
          rw [sum_sub_distrib, ← sum_div, sum_const, Int.card_Icc, nsmul_eq_mul, hc0]
          ring
      _ ≤ _ := sum_le_sum fun c hc ↦ mul_le_mul_of_nonneg_left (sum_le_sum (hrow c hc))
            (varpi_nonneg c)
  have hfin : 1 - ((149160843578876007 / 53687091200000000 : ℚ) : ℝ) / 4 + 4 * E <
      (qMass : ℝ) := by
    rw [qMass_cast, hE]
    norm_num
  change ∑' π : trPassage ω, trListWeight π.1 * d π.1 < _
  linarith

end CollatzPosDens
