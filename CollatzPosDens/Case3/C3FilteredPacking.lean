/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3AffineEnvelope
public import CollatzPosDens.Case3.C3CrossingMass
public import CollatzPosDens.Case3.C3CrossingPartition
public import CollatzPosDens.Case3.C3GoodMarginal
public import CollatzPosDens.Case3.C3H17Delta
public import CollatzPosDens.Case3.C3H17Range
public import CollatzPosDens.Case3.C3H17RowCost
public import CollatzPosDens.Case3.C3H17S
public import CollatzPosDens.Case3.C3H17TablePeriod
public import CollatzPosDens.Case3.C3H17TableRange
public import CollatzPosDens.Case3.C3NineOrbit
public import CollatzPosDens.Case3.C3NineValuation
public import CollatzPosDens.Case3.C3PascalSecondTail
public import CollatzPosDens.Case3.C3RowPack

/-!
# Conditional packing of the filtered marginal

Let `ι ∈ 𝔍` be a Fourier index, `ξ ∈ G_n` a unit and `e ∈ 𝒫` black (for `ε_*`) with gap
`ω = gap(e) ≥ 2^{34}`. Let `t ∈ ℕ`, let `B` and `d₀` be reals with `t < B` and
`B + H_pk(ι) ≤ d₀`, let `Z ⊆ ℤ` have distinct points at distance at least `d₀`, and let
`U = {z + i : z ∈ Z, 0 ≤ i < t}`. Then
```
∑_{r ∈ U} ∑_{ℓ ∈ ℤ} F^gd_{e,ι}(r, ℓ) ≤ (q_pack (B + H_pk(ι)) + Γ_pk / 4) / d₀
  + 49/120 · (4 q_pack (B + H_pk(ι)) + Γ_pk) (1 + (B + H_pk(ι)) / d₀) / √ω.
```

Write `H = H_pk(ι)`, `N = t + H` and `g = ⌊9ω/32⌋`. Every list `π` counted on the left lies in
exactly one first raw crossing set `𝒞_ω(c, o, r)`, and since `π ∉ 𝓑_init(ι, ω)` we have
`c ≤ 128`, `r ≤ g` and `0 ≤ j(Bp_{|π|}(π)) - r ≤ H`; so `r` lies in the union `U⁻` of the blocks
`{z - H, …, z - H + N - 1}`, `z ∈ Z`. The paid mass of `𝒞_ω(c, o, r)` is at most
`ϖ(c) 𝖱(r - 1, ω + o - c) ct_{c,o}(9^{r+a} s)` for `c ≤ 16` (with `s ∈ {1, 3, 5, 7}` and `a ∈ ℕ`
read off from the column top of `e`), and at most `ϖ(c) 𝖱(r - 1, ω + o - c)` for `c ≥ 17`. The
row packing bound, with the periodic weight `k ↦ ct_{c,o}(9^k s)` of period `2^{14}` (or the
constant weight `1`), bounds each row by `ϖ(c) ρ (μʰ_{c,o,s} N + rg_{c,o,s})` (or `ϖ(c) ρ N`)
with `ρ = 49/(120√ω) · (1 + (N - 2)/d₀) + 1/(4 d₀)`: every row has `l = ω + o - c ≥ ω - 127`,
and then `1/√(2(3l - 1)) ≤ 49/(120√ω)` since `(49/120)² (6ω - 764) - ω = (6ω - 1834364)/14400 > 0`
for `ω ≥ 2^{34}`. Summing, with `∑_{c ≥ 2} c ϖ(c) = 4`, the left side is at most
`ρ ((4 - Sʰ_s) N + Dʰ_s) ≤ ρ (4 q_pack N + Γ_pk) ≤ ρ (4 q_pack (B + H) + Γ_pk)` by the affine
envelope, and `N - 2 < B + H` bounds `ρ` by `49/(120√ω) · (1 + (B + H)/d₀) + 1/(4 d₀)`.

## Main results

* `CollatzPosDens.BkBlack.tsum_tsum_c3GoodMarginal_le`: the packing bound.
* `CollatzPosDens.tsum_tsum_tsum_ite_chBlockPath_eq`: summing a marginal over the points `(r, ℓ)`
  with `r ∈ U` is summing the underlying mass over the lists whose end column lies in `U`.
* `CollatzPosDens.tsum_le_ofReal_of_le_rawMass_mul_periodic`: the row packing bound in `ℝ≥0∞`.
* `CollatzPosDens.sum_c3Row_bound_le`: the summation of the row bounds over `2 ≤ c ≤ 128`.

## Implementation notes

The filtered marginal is `ℝ≥0∞`-valued, so the left side is an unconditional sum in `ℝ≥0∞`
over the subtype `U` and the right side is read through `ENNReal.ofReal`; the bound in
particular shows that the left side is finite. As for
`CollatzPosDens.BkBlack.tsum_c3CrossingSet_mul_exp_le_c3H17Table`, the gap is a natural number
`ω` with `(ω : ℤ) = gap(e)`, and the standing hypothesis that `ξ` is a unit is explicit. The
nonnegativity of the paid counts is used through `CollatzPosDens.trCount_nonneg`, which rests
on the nonnegativity of the paid rewards (`CollatzPosDens.zero_le_chPaidReward`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

open scoped ENNReal

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For `ω ≥ 2^{34}` and `l ≥ ω - 127`, `1 / √(2(3l - 1)) ≤ 49 / (120 √ω)`. -/
theorem one_div_sqrt_le_of_le_add {l ω : ℕ} (hω : 2 ^ 34 ≤ ω) (hl : ω ≤ l + 127) :
    1 / √(2 * (3 * (l : ℝ) - 1)) ≤ 49 / (120 * √ω) := by
  have hω' : (2 : ℝ) ^ 34 ≤ ω := by exact_mod_cast hω
  have hl' : (ω : ℝ) ≤ l + 127 := by exact_mod_cast hl
  have hX : 0 < 2 * (3 * (l : ℝ) - 1) := by nlinarith
  have hωpos : 0 < √(ω : ℝ) := Real.sqrt_pos.2 (by linarith)
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hX) (by positivity)]
  have h := Real.sqrt_le_sqrt (show 14400 * (ω : ℝ) ≤ 2401 * (2 * (3 * (l : ℝ) - 1)) by
    nlinarith)
  rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num),
    show (14400 : ℝ) = 120 ^ 2 by norm_num, show (2401 : ℝ) = 49 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)] at h
  linarith

/-- The row packing bound read in `ℝ≥0∞`: if `F r ≤ v 𝖱(r - 1, l) g(r + a)` on the integers
`r ≥ 1` of a union of separated blocks of length `N`, then `∑ F ≤ v (μ N + D) κ`, for every
`κ ≥ (1 + (N - 2)/d₀) / √(2(3l - 1)) + 1/(4 d₀)`. -/
theorem tsum_le_ofReal_of_le_rawMass_mul_periodic {l L N : ℕ} (hl : 2 ≤ l) (hL : 1 ≤ L)
    (hN : 1 ≤ N) (a : ℕ) {g : ℕ → ℝ} (hg0 : ∀ k, 0 ≤ g k) (hg : ∀ k, g (k + L) = g k)
    {μ D : ℝ} (hμ : μ = (1 / L) * ∑ k ∈ range L, g k)
    (hD : D = (range (L + 1)).sup' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)) -
      (range (L + 1)).inf' nonempty_range_add_one (fun k => ∑ j ∈ range k, (g j - μ)))
    {d₀ : ℝ} (hNd : (N : ℝ) ≤ d₀) {Z : Set ℤ}
    (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → d₀ ≤ |(z : ℝ) - z'|) {κ : ℝ}
    (hκ : (1 + ((N : ℝ) - 2) / d₀) * (1 / √(2 * (3 * l - 1))) + 1 / (4 * d₀) ≤ κ)
    {v : ℝ} (hv : 0 ≤ v)
    (F : {r : ℤ // (∃ z ∈ Z, ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r} → ℝ≥0∞)
    (hF : ∀ r, F r ≤ ENNReal.ofReal (v * (rawMass ((r : ℤ) - 1).toNat l * g ((r : ℤ) + a).toNat))) :
    ∑' r, F r ≤ ENNReal.ofReal (v * ((μ * N + D) * κ)) := by
  obtain ⟨hs, hle⟩ := tsum_rawMass_mul_periodic_le hl hL hN a hg0 hg hμ hD hNd hZ
  have hC : 0 ≤ μ * N + D := by
    have := (tsum_nonneg fun r => mul_nonneg (rawMass_nonneg _ _) (hg0 _)).trans hle
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hd₀ : 0 < d₀ := lt_of_lt_of_le one_pos (hN1.trans hNd)
    have hfac : 0 ≤ 1 + ((N : ℝ) - 2) / d₀ := by
      have : -1 ≤ ((N : ℝ) - 2) / d₀ := by rw [le_div_iff₀ hd₀]; linarith
      linarith
    have : 0 < (1 + ((N : ℝ) - 2) / d₀) * (1 / √(2 * (3 * l - 1))) + 1 / (4 * d₀) := by
      have : 0 ≤ (1 + ((N : ℝ) - 2) / d₀) * (1 / √(2 * (3 * l - 1))) := by positivity
      have : 0 < 1 / (4 * d₀) := by positivity
      linarith
    nlinarith
  calc ∑' r, F r ≤ ∑' r : {r : ℤ // (∃ z ∈ Z, ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
        ENNReal.ofReal (v * (rawMass ((r : ℤ) - 1).toNat l * g ((r : ℤ) + a).toNat)) :=
        ENNReal.tsum_le_tsum hF
    _ = ENNReal.ofReal (v * ∑' r : {r : ℤ // (∃ z ∈ Z, ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
        rawMass ((r : ℤ) - 1).toNat l * g ((r : ℤ) + a).toNat) := by
        rw [← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg
          (fun r => mul_nonneg hv (mul_nonneg (rawMass_nonneg _ _) (hg0 _))) (hs.mul_left v)]
    _ ≤ ENNReal.ofReal (v * ((μ * N + D) * κ)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (hle.trans (mul_le_mul_of_nonneg_left hκ hC)) hv)

/-- In `ℝ≥0∞`, the sums over `r ∈ U` and `ℓ ∈ ℤ` of the masses of the lists `π ∈ S` with
`Bp_{|π|}(π) = (r, ℓ)` add up to the mass of the lists `π ∈ S` with `j(Bp_{|π|}(π)) ∈ U`. -/
theorem tsum_tsum_tsum_ite_chBlockPath_eq (S : Set (List (List ℤ × ℤ))) (U : Set ℤ)
    [DecidablePred (· ∈ U)] (W : List (List ℤ × ℤ) → ℝ≥0∞) :
    ∑' r : U, ∑' ℓ : ℤ, ∑' π : S,
        (if chBlockPath π.1 π.1.length = ((r : ℤ), ℓ) then W π.1 else 0) =
      ∑' π : S, if (chBlockPath π.1 π.1.length).1 ∈ U then W π.1 else 0 := by
  classical
  simp_rw [ENNReal.tsum_comm (α := ℤ) (β := S)]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun π => ?_
  set p := chBlockPath π.1 π.1.length
  have hℓ : ∀ r : ℤ, ∑' ℓ : ℤ, (if p = (r, ℓ) then W π.1 else 0) =
      if p.1 = r then W π.1 else 0 := by
    intro r
    split_ifs with h
    · refine Eq.trans (tsum_congr fun ℓ => ?_) (tsum_ite_eq p.2 (fun _ => W π.1))
      by_cases hl : ℓ = p.2
      · rw [ite_eq_left hl, ite_eq_left (Prod.ext h hl.symm)]
      · rw [ite_eq_right hl, ite_eq_right fun h' => hl (by rw [h'])]
    · exact ENNReal.tsum_eq_zero.2 fun ℓ => by
        rw [ite_eq_right fun h' => h (by rw [h'])]
  simp_rw [hℓ]
  split_ifs with hU
  · refine Eq.trans (tsum_congr fun r => ?_) (tsum_ite_eq (⟨p.1, hU⟩ : U) (fun _ => W π.1))
    by_cases h : r = ⟨p.1, hU⟩
    · rw [ite_eq_left h, ite_eq_left (by rw [h])]
    · rw [ite_eq_right h, ite_eq_right fun h' => h (Subtype.ext h'.symm)]
  · exact ENNReal.tsum_eq_zero.2 fun r => by
      rw [ite_eq_right fun (h' : p.1 = r) => hU (h' ▸ r.2)]

/-- The algebra of the summation: the row bounds `ϖ(c) ρ (μʰ_{c,o,s} N + rg_{c,o,s})` for
`c ≤ 16` and `ϖ(c) ρ N` for `17 ≤ c ≤ 128` add up to at most `ρ ((4 - Sʰ_s) N + Dʰ_s)`. -/
theorem sum_c3Row_bound_le (s : ℤ) {N ρ : ℝ} (hN : 0 ≤ N) (hρ : 0 ≤ ρ) :
    ∑ c ∈ Icc (2 : ℤ) 128, ∑ o ∈ Icc (1 : ℤ) c,
        (if c ≤ 16 then varpi c * (((c3H17Mean c o s : ℚ) : ℝ) * N + (c3H17Range c o s : ℝ)) * ρ
          else varpi c * N * ρ) ≤
      ((4 - (c3H17S s : ℝ)) * N + (c3H17Delta s : ℝ)) * ρ := by
  have hcard : ∀ c : ℤ, 0 ≤ c → ∑ _o ∈ Icc (1 : ℤ) c, (1 : ℝ) = c := by
    intro c hc
    rw [sum_const, Int.card_Icc, nsmul_eq_mul, mul_one, show c + 1 - 1 = c by ring]
    exact_mod_cast Int.toNat_of_nonneg hc
  set A : ℤ → ℝ := fun c => if c ≤ 16 then
    varpi c * ∑ o ∈ Icc (1 : ℤ) c, ((1 - c3H17Mean c o s : ℚ) : ℝ) else 0 with hA
  set E : ℤ → ℝ := fun c => if c ≤ 16 then
    varpi c * ∑ o ∈ Icc (1 : ℤ) c, (c3H17Range c o s : ℝ) else 0 with hE
  have key : ∀ c ∈ Icc (2 : ℤ) 128, ∑ o ∈ Icc (1 : ℤ) c,
      (if c ≤ 16 then varpi c * (((c3H17Mean c o s : ℚ) : ℝ) * N + (c3H17Range c o s : ℝ)) * ρ
        else varpi c * N * ρ) = (c * varpi c * N - A c * N + E c) * ρ := by
    intro c hc
    have hc0 : (0 : ℤ) ≤ c := by rw [mem_Icc] at hc; omega
    simp only [hA, hE]
    split_ifs with h16
    · have : ∀ o ∈ Icc (1 : ℤ) c,
          varpi c * (((c3H17Mean c o s : ℚ) : ℝ) * N + (c3H17Range c o s : ℝ)) * ρ =
            (varpi c * N * ρ) * 1 - (varpi c * ρ * N) * ((1 - c3H17Mean c o s : ℚ) : ℝ) +
              (varpi c * ρ) * (c3H17Range c o s : ℝ) := fun o _ => by push_cast; ring
      rw [sum_congr rfl this, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum,
        hcard c hc0]
      ring
    · rw [sum_const, Int.card_Icc, nsmul_eq_mul, show c + 1 - 1 = c by ring,
        show ((c.toNat : ℕ) : ℝ) = c by exact_mod_cast Int.toNat_of_nonneg hc0]
      ring
  rw [sum_congr rfl key, ← sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ hρ
  have hS : ∑ c ∈ Icc (2 : ℤ) 128, A c = c3H17S s := by
    rw [c3H17S_cast, ← sum_filter, show (Icc (2 : ℤ) 128).filter (· ≤ 16) = Icc 2 16 by
      ext c; simp only [mem_filter, mem_Icc]; omega]
  have hΔ : ∑ c ∈ Icc (2 : ℤ) 128, E c = c3H17Delta s := by
    rw [c3H17Delta_cast, ← sum_filter, show (Icc (2 : ℤ) 128).filter (· ≤ 16) = Icc 2 16 by
      ext c; simp only [mem_filter, mem_Icc]; omega]
  have h4 : ∑ c ∈ Icc (2 : ℤ) 128, (c : ℝ) * varpi c ≤ 4 := by
    refine sum_le_hasSum _ (fun c _ => ?_) hasSum_mul_varpi
    rcases le_or_gt c 1 with h | h
    · rw [varpi_of_le_one h, mul_zero]
    · exact mul_nonneg (by exact_mod_cast (show (0 : ℤ) ≤ c by omega)) (varpi_nonneg c)
  rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul, hS, hΔ]
  nlinarith

/-- `9^{2^j} ≡ 1 (mod 2^{j+3})`, as an identity in `ℤ`. -/
theorem exists_nine_pow_two_pow_eq (j : ℕ) : ∃ q : ℤ, (9 : ℤ) ^ 2 ^ j = 1 + 2 ^ (j + 3) * q := by
  obtain ⟨q, hq⟩ := two_pow_dvd_nine_pow_two_pow_sub_one j
  have key : ∀ m : ℕ, 1 ≤ m → m - 1 = 2 ^ (j + 3) * q → (m : ℤ) = 1 + 2 ^ (j + 3) * q :=
    fun m h1 h => by
      have : ((m - 1 : ℕ) : ℤ) = ((2 ^ (j + 3) * q : ℕ) : ℤ) := by rw [h]
      push_cast [h1] at this
      linarith
  refine ⟨q, ?_⟩
  have := key _ (Nat.one_le_pow _ _ (by norm_num)) hq
  rwa [Nat.cast_pow, Nat.cast_ofNat] at this

/-- The paid masses `bw^⊗(π) exp(-z_* N^*(e, π; |π|))` over a first raw crossing set
`𝒞_ω(c, o, r)` with `1 ≤ o ≤ c` and `r ≥ 1` are summable and add up to at most
`ϖ(c) 𝖱(r - 1, ω + o - c)`, the total weight of `𝒞_ω(c, o, r)`. -/
theorem summable_paid_c3CrossingSet (n : ℕ) (ξ : ResidueGroup n) (e : ℤ × ℤ) (ω : ℕ)
    {c o : ℤ} {r : ℕ} (ho : 1 ≤ o) (hoc : o ≤ c) (hr : 1 ≤ r) :
    Summable (fun π : c3CrossingSet ω c o r ↦
        trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length)) ∧
      ∑' π : c3CrossingSet ω c o r,
          trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length) ≤
        varpi c * rawMass (r - 1) (ω + o - c) := by
  have hmass := hasSum_trListWeight_c3CrossingSet ω ho hoc hr
  have h0 (π : c3CrossingSet ω c o r) :
      0 ≤ trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length) :=
    mul_nonneg (trListWeight_nonneg _) (Real.exp_pos _).le
  have hle (π : c3CrossingSet ω c o r) :
      trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length) ≤
        trListWeight π.1 := by
    refine mul_le_of_le_one_right (trListWeight_nonneg _) (Real.exp_le_one_iff.2 ?_)
    have := trCount_nonneg (n := n) (ξ := ξ) e π.1 π.1.length
    have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_nonneg
    nlinarith
  have hs := hmass.summable.of_nonneg_of_le h0 hle
  exact ⟨hs, (hs.tsum_le_tsum hle hmass.summable).trans_eq hmass.tsum_eq⟩

/-- **Conditional packing of the filtered marginal.** Let `ι` be a Fourier index, `ξ` a unit and
`e ∈ 𝒫` black (for `ε_*`) with gap `ω = gap(e) ≥ 2^{34}`. Let `t ∈ ℕ`, let `B, d₀` be reals
with `t < B` and `B + H_pk(ι) ≤ d₀`, let the distinct points of `Z ⊆ ℤ` be at distance at
least `d₀`, and let `U = {z + i : z ∈ Z, 0 ≤ i < t}`. Then
`∑_{r ∈ U} ∑_{ℓ ∈ ℤ} F^gd_{e,ι}(r, ℓ) ≤ (q_pack (B + H_pk(ι)) + Γ_pk / 4) / d₀ +
49/120 · (4 q_pack (B + H_pk(ι)) + Γ_pk) (1 + (B + H_pk(ι)) / d₀) / √ω`. -/
@[collatz_pos_dens "lem_c3_filtered_packing"]
theorem BkBlack.tsum_tsum_c3GoodMarginal_le (ι : FIndex) {n : ℕ} {ξ : ResidueGroup n}
    {e : ℤ × ℤ}
    (hb : BkBlack n ξ (epsStar : ℝ) e) (hξ : IsResidueUnit ξ) (he : e ∈ bkPoints)
    {ω : ℕ} (hω : (ω : ℤ) = trGap n ξ (epsStar : ℝ) e) (hω34 : 2 ^ 34 ≤ ω)
    (t : ℕ) {B d₀ : ℝ} (htB : (t : ℝ) < B) (hBd : B + Hpack ι ≤ d₀) {Z : Set ℤ}
    (hZ : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → d₀ ≤ |(z : ℝ) - z'|) :
    ∑' r : {r : ℤ | ∃ z ∈ Z, ∃ i : ℕ, i < t ∧ r = z + i}, ∑' ℓ : ℤ,
        c3GoodMarginal ι n ξ e ((r : ℤ), ℓ) ≤
      ENNReal.ofReal ((qPack * (B + Hpack ι) + Gammapk / 4) / d₀ +
        49 / 120 * ((4 * qPack * (B + Hpack ι) + Gammapk) * (1 + (B + Hpack ι) / d₀) / √ω)) := by
  classical
  set U : Set ℤ := {r | ∃ z ∈ Z, ∃ i : ℕ, i < t ∧ r = z + i} with hUdef
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have : IsEmpty U := ⟨fun ⟨_, _, _, _, hi, _⟩ => by omega⟩
    rw [tsum_empty]
    exact zero_le
  /- The column-top data: an odd `M₀` with `2^17 ∣ 3^n M₀ + 3^n ϑ(j(e), l_Δ)`, its class
  `s ∈ {1, 3, 5, 7}` modulo `8`, and `a` with `M₀ ≡ 9^a s (mod 2^17)`. -/
  set θ := bkTheta n ξ (bkJ e, (bkCanonTriangle n ξ (epsStar : ℝ) e he).l) with hθ
  have hε := epsStar_mem_bkRange (K := ℝ)
  obtain ⟨Nθ, hNθ, hNodd⟩ := odd_three_pow_mul_bkTheta_bkColTop hξ hε.1 hε.2 he hb
  obtain ⟨u, v, huv⟩ : IsCoprime ((3 : ℤ) ^ n) (2 ^ 17) :=
    (Int.isCoprime_iff_gcd_eq_one.2 rfl : IsCoprime (3 : ℤ) 2).pow
  set M₀ : ℤ := -(u * Nθ) with hM₀
  have hkZ : 3 ^ n * M₀ + Nθ = 2 ^ 17 * (v * Nθ) := by
    rw [hM₀]; linear_combination (-Nθ) * huv
  have hdvd : ∃ k : ℤ, (3 : ℝ) ^ n * M₀ + 3 ^ n * θ = 2 ^ 17 * k :=
    ⟨v * Nθ, by rw [← hNθ]; exact_mod_cast hkZ⟩
  have hM₀odd : Odd M₀ := by
    have h3 : Odd (3 ^ n * M₀) := by
      rw [show 3 ^ n * M₀ = 2 * (2 ^ 16 * (v * Nθ)) - Nθ by linear_combination hkZ]
      exact (even_two_mul _).sub_odd hNodd
    exact (Int.odd_mul.1 h3).2
  set s : ℤ := M₀ % 8 with hsdef
  have hs8 : M₀ ≡ s [ZMOD 8] := (Int.mod_modEq M₀ 8).symm
  have hsodd : Odd s := by
    rw [Int.odd_iff] at hM₀odd ⊢
    omega
  have hs : s ∈ ({1, 3, 5, 7} : Finset ℤ) := by
    rw [Int.odd_iff] at hsodd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  obtain ⟨a, -, ha⟩ := exists_nine_pow_mul_modEq hM₀odd hsodd hs8
  obtain ⟨k, hk⟩ := ha.symm.dvd
  have htable : ∀ c o : ℤ, o ≤ 17 → ∀ r : ℕ,
      c3H17Table c o (9 ^ r * M₀) = c3H17Table c o (9 ^ (r + a) * s) := by
    intro c o ho r
    rw [show (9 : ℤ) ^ r * M₀ = 9 ^ (r + a) * s + 9 ^ r * k * 2 ^ 17 by
      rw [pow_add]; linear_combination (9 : ℤ) ^ r * hk]
    exact c3H17Table_add_mul_two_pow c ho _ _
  -- the period `2^14` of `k ↦ ct_{c,o}(9^k s)`
  -- basic sizes
  set N : ℕ := t + Hpack ι with hNdef
  have hN1 : 1 ≤ N := by omega
  have hNd : (N : ℝ) ≤ d₀ := by
    rw [hNdef]; push_cast; linarith
  have hNB : (N : ℝ) < B + Hpack ι := by
    rw [hNdef]; push_cast; linarith
  have hd₀ : 0 < d₀ := by
    have : (0 : ℝ) ≤ t := t.cast_nonneg
    linarith
  have hωpos : 0 < √(ω : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < ω))
  have hfac : 0 ≤ 1 + ((N : ℝ) - 2) / d₀ := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have : -1 ≤ ((N : ℝ) - 2) / d₀ := by rw [le_div_iff₀ hd₀]; linarith
    linarith
  set ρ : ℝ := 49 / (120 * √ω) * (1 + ((N : ℝ) - 2) / d₀) + 1 / (4 * d₀) with hρdef
  have hρ : 0 ≤ ρ := by positivity
  -- the shifted block starts `Z - H`
  set Z' : Set ℤ := (fun z => z - (Hpack ι : ℤ)) '' Z with hZ'def
  have hZ' : ∀ z ∈ Z', ∀ z' ∈ Z', z ≠ z' → d₀ ≤ |(z : ℝ) - z'| := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ hne
    have := hZ z hz z' hz' fun h => hne (by rw [h])
    push_cast
    rwa [sub_sub_sub_cancel_right]
  set g : ℕ := 9 * ω / 32 with hgdef
  set P : Set (List (List ℤ × ℤ)) := trPassage ω \ c3InitException ι ω with hPdef
  set W : List (List ℤ × ℤ) → ℝ≥0∞ := fun π =>
    ENNReal.ofReal (trListWeight π * Real.exp (-(zStar : ℝ) * trCount n ξ e π π.length)) with hW
  set T : ℤ → ℤ → ℤ → ℝ≥0∞ := fun c o r =>
    if r ≤ (g : ℤ) then ∑' π : c3CrossingSet ω c o r.toNat, W π.1 else 0 with hT
  -- Step 1: the left side is the mass of the lists `π ∈ P` with `j(Bp_{|π|}(π)) ∈ U`
  have hωt : (trGap n ξ (epsStar : ℝ) e).toNat = ω := by omega
  have e1 : ∀ x, c3GoodMarginal ι n ξ e x = ∑' π : P, c3PaidTerm n ξ e x π := by
    intro x
    rw [c3GoodMarginal_eq_tsum, hωt]
  simp_rw [e1]
  -- Step 2: each such list lies in a crossing set `𝒞_ω(c, o, r)`, `c ≤ 128`, `r ≤ g`, `r ∈ U⁻`
  have hpt : ∀ π : P, (if (chBlockPath π.1 π.1.length).1 ∈ U then W π.1 else 0) ≤
      ∑ c ∈ Icc (2 : ℤ) 128, ∑ o ∈ Icc (1 : ℤ) c,
        ∑' r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
          if ((r : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c o (r : ℤ).toNat) then W π.1 else 0 := by
    intro π
    split_ifs with hU
    swap
    · exact zero_le
    obtain ⟨hπP, hπB⟩ := π.2
    obtain ⟨⟨c₀, o₀, r₀⟩, ⟨hc2, ho1, hoc, hr1, hmem⟩, -⟩ := existsUnique_mem_c3CrossingSet hπP
    dsimp only at hc2 ho1 hoc hr1 hmem
    have hnot : ¬((Hpack ι : ℤ) < (chBlockPath π.1 π.1.length).1 - r₀ ∨ 128 < c₀ ∨
        9 * ω / 32 < r₀) :=
      fun h => hπB (mem_c3InitException_of_mem_c3CrossingSet hc2 ho1 hoc hr1 hmem h)
    simp only [not_or, not_lt] at hnot
    obtain ⟨hMH, hc128, hrg⟩ := hnot
    have hrM := le_chBlockPath_fst_of_mem_c3CrossingSet hmem
    obtain ⟨z, hz, i, hi, hMi⟩ := hU
    have hR : (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ (r₀ : ℤ) = z + i) ∧ 1 ≤ (r₀ : ℤ) :=
      ⟨⟨z - Hpack ι, ⟨z, hz, rfl⟩,
        ((i : ℤ) + Hpack ι - ((chBlockPath π.1 π.1.length).1 - r₀)).toNat,
        by omega, by omega⟩, by omega⟩
    calc W π.1 = if ((r₀ : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c₀ o₀ ((r₀ : ℤ)).toNat) then W π.1
          else 0 := by
          rw [ite_eq_left ⟨by omega, by rwa [Int.toNat_natCast]⟩]
      _ ≤ ∑' r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
          if ((r : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c₀ o₀ (r : ℤ).toNat) then W π.1 else 0 :=
          ENNReal.le_tsum (f := fun r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r} =>
            if ((r : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c₀ o₀ (r : ℤ).toNat) then W π.1 else 0)
            ⟨r₀, hR⟩
      _ ≤ ∑ o ∈ Icc (1 : ℤ) c₀,
          ∑' r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
            if ((r : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c₀ o (r : ℤ).toNat) then W π.1 else 0 :=
          single_le_sum (f := fun o => ∑' r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧
            1 ≤ r}, if ((r : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c₀ o (r : ℤ).toNat) then W π.1
              else 0) (fun _ _ => zero_le) (mem_Icc.2 ⟨ho1, hoc⟩)
      _ ≤ _ := single_le_sum (f := fun c => ∑ o ∈ Icc (1 : ℤ) c,
          ∑' r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
            if ((r : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c o (r : ℤ).toNat) then W π.1 else 0)
          (fun _ _ => zero_le) (mem_Icc.2 ⟨hc2, hc128⟩)
  -- the summed indicator of `𝒞_ω(c, o, r)` over `P` is at most `T c o r`
  have hswap : ∀ c o : ℤ,
      ∀ r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
      ∑' π : P, (if ((r : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c o (r : ℤ).toNat) then W π.1 else 0) ≤
        T c o r := by
    intro c o r
    simp only [hT]
    split_ifs with hrg
    · simp only [hrg, true_and]
      rw [tsum_subtype P (fun π => if π ∈ c3CrossingSet ω c o (r : ℤ).toNat then W π else 0),
        tsum_subtype (c3CrossingSet ω c o (r : ℤ).toNat) W]
      refine ENNReal.tsum_le_tsum fun π => ?_
      simp only [Set.indicator]
      split_ifs <;> first | exact le_rfl | exact zero_le
    · simp only [hrg, false_and, ↓reduceIte, tsum_zero, le_refl]
  -- the paid mass of a crossing set, read in `ℝ≥0∞`
  have hTreal : ∀ c o : ℤ, 1 ≤ o → o ≤ c → ∀ r : ℕ, 1 ≤ r →
      ∑' π : c3CrossingSet ω c o r, W π.1 = ENNReal.ofReal (∑' π : c3CrossingSet ω c o r,
        trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length)) := by
    intro c o ho hoc r hr
    rw [ENNReal.ofReal_tsum_of_nonneg (fun π => mul_nonneg (trListWeight_nonneg _)
      (Real.exp_pos _).le) (summable_paid_c3CrossingSet n ξ e ω ho hoc hr).1]
  -- Step 3: the row bounds
  have hrow : ∀ c ∈ Icc (2 : ℤ) 128, ∀ o ∈ Icc (1 : ℤ) c,
      ∑' r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r}, T c o r ≤
        ENNReal.ofReal (if c ≤ 16 then
          varpi c * (((c3H17Mean c o s : ℚ) : ℝ) * N + (c3H17Range c o s : ℝ)) * ρ
          else varpi c * N * ρ) := by
    intro c hc o ho
    rw [mem_Icc] at hc ho
    set l : ℕ := ((ω : ℤ) + o - c).toNat with hldef
    have hl2 : 2 ≤ l := by omega
    have hlω : ω ≤ l + 127 := by omega
    have hlZ : ((l : ℕ) : ℤ) = (ω : ℤ) + o - c := by omega
    have hκ : (1 + ((N : ℝ) - 2) / d₀) * (1 / √(2 * (3 * (l : ℝ) - 1))) + 1 / (4 * d₀) ≤ ρ := by
      have := mul_le_mul_of_nonneg_left (one_div_sqrt_le_of_le_add hω34 hlω) hfac
      rw [hρdef]
      linarith
    split_ifs with hc16
    · -- the periodic cost table, `2 ≤ c ≤ 16`
      obtain ⟨q, h9⟩ := exists_nine_pow_two_pow_eq 14
      set h : ℕ → ℝ := fun k => (c3H17Table c o (9 ^ k * s) : ℝ) with hh
      have hh0 : ∀ k, 0 ≤ h k := fun k => Rat.cast_nonneg.2 (c3H17Table_mem_Icc c o _).1
      have hper : ∀ k, h (k + 2 ^ 14) = h k := by
        intro k
        simp only [hh]
        rw [show (9 : ℤ) ^ (k + 2 ^ 14) * s = 9 ^ k * s + 9 ^ k * s * q * 2 ^ 17 by
          rw [pow_add, h9]; ring, c3H17Table_add_mul_two_pow c (by omega)]
      have hμ : ((c3H17Mean c o s : ℚ) : ℝ) =
          (1 / ((2 ^ 14 : ℕ) : ℝ)) * ∑ k ∈ range (2 ^ 14), h k := by
        simp only [hh, c3H17Mean]
        push_cast
        ring
      have hfun : (Rat.cast ∘ c3H17CentredSum c o s : ℕ → ℝ) =
          fun k => ∑ j ∈ range k, (h j - ((c3H17Mean c o s : ℚ) : ℝ)) := by
        funext k
        simp only [Function.comp_apply, c3H17CentredSum, hh]
        push_cast
        rfl
      have hD : ((c3H17Range c o s : ℚ) : ℝ) =
          (range (2 ^ 14 + 1)).sup' nonempty_range_add_one
              (fun k => ∑ j ∈ range k, (h j - ((c3H17Mean c o s : ℚ) : ℝ))) -
            (range (2 ^ 14 + 1)).inf' nonempty_range_add_one
              (fun k => ∑ j ∈ range k, (h j - ((c3H17Mean c o s : ℚ) : ℝ))) := by
        rw [c3H17Range, Rat.cast_sub,
          Finset.apply_sup'_eq_sup'_comp _ _ fun x y => Rat.cast_max x y,
          Finset.apply_inf'_eq_inf'_comp _ _ fun x y => Rat.cast_min x y, hfun]
      have := tsum_le_ofReal_of_le_rawMass_mul_periodic hl2 (Nat.one_le_two_pow) hN1 a hh0 hper
        hμ hD hNd hZ' hκ (varpi_nonneg c) (fun r => T c o r) (fun r => by
          obtain ⟨r, -, hr1⟩ := r
          simp only [hT]
          split_ifs with hrg
          · rw [hTreal c o (by omega) (by omega) _ (by omega)]
            refine ENNReal.ofReal_le_ofReal ?_
            refine (hb.tsum_c3CrossingSet_mul_exp_le_c3H17Table hξ he hω (by omega) M₀ hdvd
              hc.1 hc16 ho.1 ho.2 (by omega) (by omega)).trans_eq ?_
            simp only [hh]
            rw [htable c o (by omega), show r.toNat + a = (r + a).toNat by omega,
              show r.toNat - 1 = (r - 1).toNat by omega, ← hlZ]
            ring
          · exact zero_le)
      refine this.trans_eq ?_
      congr 1
      ring
    · -- the constant weight `1`, `17 ≤ c ≤ 128`
      have := tsum_le_ofReal_of_le_rawMass_mul_periodic (g := fun _ => 1) (μ := 1) (D := 0) hl2
        le_rfl hN1 a (fun _ => zero_le_one) (fun _ => rfl) (by simp) (by simp) hNd hZ' hκ
        (varpi_nonneg c) (fun r => T c o r) (fun r => by
          obtain ⟨r, -, hr1⟩ := r
          simp only [hT]
          split_ifs with hrg
          · rw [hTreal c o (by omega) (by omega) _ (by omega)]
            refine ENNReal.ofReal_le_ofReal ?_
            refine (summable_paid_c3CrossingSet n ξ e ω (by omega) ho.2 (by omega)).2.trans_eq ?_
            rw [show r.toNat - 1 = (r - 1).toNat by omega, ← hlZ]
            ring
          · exact zero_le)
      refine this.trans_eq ?_
      congr 1
      ring
  -- Step 4: summation
  have hX0 : ∀ c ∈ Icc (2 : ℤ) 128, ∀ o ∈ Icc (1 : ℤ) c, 0 ≤ (if c ≤ 16 then
      varpi c * (((c3H17Mean c o s : ℚ) : ℝ) * N + (c3H17Range c o s : ℝ)) * ρ
      else varpi c * N * ρ) := by
    intro c _ o _
    have hμ0 : (0 : ℝ) ≤ ((c3H17Mean c o s : ℚ) : ℝ) := by
      have : (0 : ℚ) ≤ c3H17Mean c o s := by
        unfold c3H17Mean
        exact div_nonneg (sum_nonneg fun k _ => c3H17Table_nonneg _ _ _) (by positivity)
      exact_mod_cast this
    have hrg0 : (0 : ℝ) ≤ (c3H17Range c o s : ℝ) := by exact_mod_cast c3H17Range_nonneg c o s
    have := varpi_nonneg c
    split_ifs <;> positivity
  have hreal : ∑ c ∈ Icc (2 : ℤ) 128, ∑ o ∈ Icc (1 : ℤ) c, (if c ≤ 16 then
      varpi c * (((c3H17Mean c o s : ℚ) : ℝ) * N + (c3H17Range c o s : ℝ)) * ρ
      else varpi c * N * ρ) ≤ (qPack * (B + Hpack ι) + Gammapk / 4) / d₀ +
        49 / 120 * ((4 * qPack * (B + Hpack ι) + Gammapk) * (1 + (B + Hpack ι) / d₀) / √ω) := by
    refine (sum_c3Row_bound_le s (Nat.cast_nonneg N) hρ).trans ?_
    have henv := c3H17_affine_envelope (K := ℝ) ι hs (N := (N : ℝ)) (by
      rw [hNdef]; push_cast; have : (1 : ℝ) ≤ t := by exact_mod_cast ht
      linarith)
    have hq : (0 : ℝ) < qPack := by exact_mod_cast qPack_pos
    calc ((4 - (c3H17S s : ℝ)) * N + (c3H17Delta s : ℝ)) * ρ
        ≤ (4 * (qPack : ℝ) * N + (Gammapk : ℝ)) * ρ := mul_le_mul_of_nonneg_right henv hρ
      _ ≤ (4 * (qPack : ℝ) * (B + Hpack ι) + (Gammapk : ℝ)) * ρ := by gcongr
      _ ≤ (4 * (qPack : ℝ) * (B + Hpack ι) + (Gammapk : ℝ)) *
          (49 / (120 * √ω) * (1 + (B + Hpack ι) / d₀) + 1 / (4 * d₀)) := by
        have hΓ : (0 : ℝ) < Gammapk := by exact_mod_cast Gammapk_pos
        have hBH : (0 : ℝ) ≤ B + Hpack ι := (Nat.cast_nonneg N).trans hNB.le
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hρdef]
        have : ((N : ℝ) - 2) / d₀ ≤ (B + Hpack ι) / d₀ :=
          div_le_div_of_nonneg_right (by linarith) hd₀.le
        have : (0 : ℝ) ≤ 49 / (120 * √ω) := by positivity
        nlinarith
      _ = _ := by
        field_simp
        ring
  calc ∑' r : U, ∑' ℓ : ℤ, ∑' π : P, c3PaidTerm n ξ e ((r : ℤ), ℓ) π
      = ∑' π : P, if (chBlockPath π.1 π.1.length).1 ∈ U then W π.1 else 0 :=
        tsum_tsum_tsum_ite_chBlockPath_eq P U W
    _ ≤ ∑' π : P, ∑ c ∈ Icc (2 : ℤ) 128, ∑ o ∈ Icc (1 : ℤ) c,
        ∑' r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r},
          (if ((r : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c o (r : ℤ).toNat) then W π.1 else 0) :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑ c ∈ Icc (2 : ℤ) 128, ∑ o ∈ Icc (1 : ℤ) c,
        ∑' r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r}, ∑' π : P,
          (if ((r : ℤ) ≤ g ∧ π.1 ∈ c3CrossingSet ω c o (r : ℤ).toNat) then W π.1 else 0) := by
        rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        refine sum_congr rfl fun c _ => ?_
        rw [Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        exact sum_congr rfl fun o _ => ENNReal.tsum_comm
    _ ≤ ∑ c ∈ Icc (2 : ℤ) 128, ∑ o ∈ Icc (1 : ℤ) c,
        ∑' r : {r : ℤ // (∃ z ∈ Z', ∃ i : ℕ, i < N ∧ r = z + i) ∧ 1 ≤ r}, T c o r :=
        sum_le_sum fun c _ => sum_le_sum fun o _ => ENNReal.tsum_le_tsum fun r => hswap c o r
    _ ≤ ∑ c ∈ Icc (2 : ℤ) 128, ∑ o ∈ Icc (1 : ℤ) c, ENNReal.ofReal (if c ≤ 16 then
          varpi c * (((c3H17Mean c o s : ℚ) : ℝ) * N + (c3H17Range c o s : ℝ)) * ρ
          else varpi c * N * ρ) :=
        sum_le_sum fun c hc => sum_le_sum fun o ho => hrow c hc o ho
    _ = ENNReal.ofReal (∑ c ∈ Icc (2 : ℤ) 128, ∑ o ∈ Icc (1 : ℤ) c, (if c ≤ 16 then
          varpi c * (((c3H17Mean c o s : ℚ) : ℝ) * N + (c3H17Range c o s : ℝ)) * ρ
          else varpi c * N * ρ)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun c hc => sum_nonneg fun o ho => hX0 c hc o ho]
        exact sum_congr rfl fun c hc => (ENNReal.ofReal_sum_of_nonneg (hX0 c hc)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

end CollatzPosDens
