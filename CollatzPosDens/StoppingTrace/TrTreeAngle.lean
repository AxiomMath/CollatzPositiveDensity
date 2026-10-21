/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrGap
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.BlackSet.BkResidueShift
public import CollatzPosDens.CharSum.ChColtopAngle
public import CollatzPosDens.CharSum.ChColtopOdd

/-!
# A common phase along the raw walk

Fix a level `n`, a unit `ξ ∈ G_n` and the colour scale `ε_*`. Let `v = (j, l)` be a black point
with gap `ω = gap(v)`, let `B ≥ 1` and put `Q = 3^n`. The column top of `v` is
`t₀ = (j, l + ω)`, and the integer `N = Q ϑ(t₀)` is odd with `|N / Q| ≤ ε_* 2^{-ω}`. As `Q` is
odd there is an odd integer `0 < m < 2^B` with `m Q ≡ -9 N (mod 2^B)`; put
`α = 9 · 2^ω N / Q`, so that `|α| ≤ 9 ε_*`. For `r ≥ 1` and `0 ≤ L ≤ ω + B` the residue shift
gives `2^L r(v + (r, L)) = 9^r 2^ω r(t₀)`, so the integer `K = 9^{r-1} 2^ω (m Q + 9 N) / 2^L`
represents `r(v + (r, L))`. Hence
`ϑ(v + (r, L)) - 9^{r-1} (2^ω m + α) / 2^L = ϑ(v + (r, L)) - K / Q ∈ ℤ`.

## Main results

* `CollatzPosDens.exists_odd_bkTheta_add_sub_mem_int`: for a black point `v` with
  `gap(v) = ω` and `B ≥ 1` there are an odd integer `0 < m < 2^B` and a real `α` with
  `|α| ≤ 9 ε_*` such that `ϑ(v + (r, L)) - 9^{r-1} (2^ω m + α) / 2^L ∈ ℤ` for all `r ≥ 1` and
  `0 ≤ L ≤ ω + B`.

## Implementation notes

Black points are points of `𝒫` and the residue `ξ` is a unit; these standing assumptions are
the hypotheses `v ∈ bkPoints` and `IsResidueUnit ξ`. The gap is a nonnegative integer; the
statement takes a natural number `ω` together with the hypothesis `gap(v) = ω`. The integers
`r ≥ 1` and `0 ≤ L` are taken in `ℕ`, which is the same quantification. Membership in `ℤ` is
stated as the existence of an integer `k` equal to the difference. The integer `m` is produced
from a Bézout identity `a Q + b 2^B = 1` as the residue of `-9 N a` modulo `2^B`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- **A common phase along the raw walk.** Let `ξ` be a unit, `v ∈ 𝒫` black for `ε_*` with
`gap(v) = ω`, and `B ≥ 1`. Then there are an odd integer `m` with `0 < m < 2^B` and a real `α`
with `|α| ≤ 9 ε_*` such that `ϑ(v + (r, L)) - 9^{r-1} (2^ω m + α) / 2^L ∈ ℤ` for all integers
`r ≥ 1` and `0 ≤ L ≤ ω + B`. -/
@[collatz_pos_dens "lem_tr_tree_angle"]
theorem exists_odd_bkTheta_add_sub_mem_int {n : ℕ} {ξ : ResidueGroup n}
    (hξ : IsResidueUnit ξ) {v : ℤ × ℤ} (hv : v ∈ bkPoints)
    (hb : BkBlack n ξ (epsStar : ℝ) v) {ω : ℕ} (hgap : trGap n ξ (epsStar : ℝ) v = ω)
    {B : ℕ} (hB : 1 ≤ B) :
    ∃ m : ℤ, Odd m ∧ 0 < m ∧ m < 2 ^ B ∧ ∃ α : ℝ, |α| ≤ 9 * (epsStar : ℝ) ∧
      ∀ r L : ℕ, 1 ≤ r → L ≤ ω + B →
        ∃ k : ℤ, bkTheta n ξ (v + ((r : ℤ), (L : ℤ))) -
          (9 : ℝ) ^ (r - 1) * (2 ^ ω * m + α) / 2 ^ L = k := by
  obtain ⟨hε₀, hε⟩ := epsStar_mem_bkRange (K := ℝ)
  set Q : ℕ := 3 ^ n with hQ
  set t₀ : ℤ × ℤ := (bkJ v, bkColTop n ξ (epsStar : ℝ) v) with ht₀
  set N : ℤ := (bkThetaResidue n ξ t₀).valMinAbs with hN
  have hNodd : Odd N := odd_valMinAbs_bkThetaResidue_bkColTop hξ hε₀ hε hv hb
  have htop : bkColTop n ξ (epsStar : ℝ) v = bkL v + ω := by
    rw [bkColTop_eq_add_trGap, hgap]
  -- `|ϑ(t₀)| ≤ ε_* 2^{-ω}`.
  have hangle : |bkTheta n ξ t₀| ≤ (epsStar : ℝ) * (2 : ℝ) ^ (-(ω : ℤ)) :=
    abs_bkTheta_colTop_le hξ hε₀ hε hv hb ω (by rw [bkCanonTriangle_l, htop])
  -- Bézout: `a Q + b 2^B = 1`.
  have hcop : IsCoprime (Q : ℤ) (2 ^ B) := by
    rw [hQ]; push_cast
    exact (Int.isCoprime_iff_gcd_eq_one.2 (by decide : Int.gcd 3 2 = 1)).pow
  obtain ⟨a, b, hab⟩ := hcop
  have h2B : (0 : ℤ) < 2 ^ B := by positivity
  set m : ℤ := (-9 * N * a) % 2 ^ B with hm
  have hmdiv : -9 * N * a = 2 ^ B * ((-9 * N * a) / 2 ^ B) + m := by
    have := Int.emod_add_mul_ediv (-9 * N * a) (2 ^ B)
    rw [hm]; linarith
  -- `m Q + 9 N = 2^B c`.
  obtain ⟨c, hc⟩ : ∃ c : ℤ, m * Q + 9 * N = 2 ^ B * c :=
    ⟨9 * N * b - (-9 * N * a) / 2 ^ B * Q, by linear_combination (-9 * N) * hab - Q * hmdiv⟩
  have hmodd : Odd m := by
    have haQ : Odd (a * Q) := ⟨-(b * 2 ^ (B - 1)), by
      have : (2 : ℤ) ^ B = 2 * 2 ^ (B - 1) := by rw [← pow_succ']; congr 1; omega
      linear_combination hab - b * this⟩
    have h9 : Odd (-9 * N * a) := ((by decide : Odd (-9 : ℤ)).mul hNodd).mul (Int.odd_mul.1 haQ).1
    have hev : Even (2 ^ B * ((-9 * N * a) / 2 ^ B)) :=
      (Int.even_pow.2 ⟨even_two, by omega⟩).mul_right _
    have : m = -9 * N * a - 2 ^ B * ((-9 * N * a) / 2 ^ B) := by linarith
    rw [this]
    exact h9.sub_even hev
  have hm0 : 0 ≤ m := Int.emod_nonneg _ h2B.ne'
  have hmlt : m < 2 ^ B := Int.emod_lt_of_pos _ h2B
  have hmpos : 0 < m := lt_of_le_of_ne hm0 (fun h => by rw [← h] at hmodd; simp at hmodd)
  have hQpos : (0 : ℝ) < Q := by positivity
  have hθt₀ : bkTheta n ξ t₀ = (N : ℝ) / Q := by
    rw [hN, ← three_pow_mul_bkTheta n ξ t₀, hQ]; push_cast; field_simp
  refine ⟨m, hmodd, hmpos, hmlt, 9 * 2 ^ ω * N / Q, ?_, ?_⟩
  · -- `|α| = 9 · 2^ω |ϑ(t₀)| ≤ 9 ε_*`.
    have hα : (9 : ℝ) * 2 ^ ω * N / Q = 9 * 2 ^ ω * bkTheta n ξ t₀ := by
      rw [hθt₀]; ring
    rw [hα, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 9 * 2 ^ ω)]
    have h2ω : (2 : ℝ) ^ ω * (2 : ℝ) ^ (-(ω : ℤ)) = 1 := by
      rw [zpow_neg, zpow_natCast, mul_inv_cancel₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hangle (by positivity : (0 : ℝ) ≤ 9 * 2 ^ ω)
    calc 9 * 2 ^ ω * |bkTheta n ξ t₀| ≤ 9 * 2 ^ ω * ((epsStar : ℝ) * 2 ^ (-(ω : ℤ))) := this
      _ = 9 * (epsStar : ℝ) * ((2 : ℝ) ^ ω * (2 : ℝ) ^ (-(ω : ℤ))) := by ring
      _ = 9 * (epsStar : ℝ) := by rw [h2ω, mul_one]
  · intro r L hr1 hL
    set y : ℤ × ℤ := v + ((r : ℤ), (L : ℤ)) with hy
    set g : ℤ × ℤ := (bkJ v + r, bkL v) with hg
    have hv' := mem_bkPoints.1 hv
    have hyP : y ∈ bkPoints := mem_bkPoints.2 (by simp [y, bkJ] at hv' ⊢; omega)
    have hgP : g ∈ bkPoints := mem_bkPoints.2 (by simp [g, bkJ] at hv' ⊢; omega)
    have ht₀P : t₀ ∈ bkPoints := mem_bkPoints.2 hv'
    -- residue shifts
    have hrg : bkThetaResidue n ξ g =
        (9 : ResidueGroup n) ^ r * 2 ^ ω * bkThetaResidue n ξ t₀ := by
      rw [bkThetaResidue_shift n ξ ht₀P hgP (by simp [g, t₀, bkJ])
        (by change bkL v ≤ bkColTop n ξ (epsStar : ℝ) v; omega)]
      have h1 : (bkJ g - bkJ t₀).toNat = r := by simp [g, t₀, bkJ]
      have h2 : (bkL t₀ - bkL g).toNat = ω := by
        change (bkColTop n ξ (epsStar : ℝ) v - bkL v).toNat = ω
        rw [htop]; simp
      rw [h1, h2]; push_cast; ring
    have hrg' : bkThetaResidue n ξ g = (2 : ResidueGroup n) ^ L * bkThetaResidue n ξ y := by
      rw [bkThetaResidue_shift n ξ hyP hgP (by simp [g, y, bkJ]) (by simp [g, y, bkL])]
      have h1 : (bkJ g - bkJ y).toNat = 0 := by simp [g, y, bkJ]
      have h2 : (bkL y - bkL g).toNat = L := by simp [g, y, bkL]
      rw [h1, h2]; push_cast; ring
    -- the integer `K`
    set K : ℤ := 9 ^ (r - 1) * 2 ^ (ω + B - L) * c with hK
    have hKL : 2 ^ L * K = 9 ^ (r - 1) * 2 ^ ω * (m * Q + 9 * N) := by
      have h2 : (2 : ℤ) ^ L * 2 ^ (ω + B - L) = 2 ^ ω * 2 ^ B := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      rw [hK, hc]
      linear_combination (9 ^ (r - 1) * c) * h2
    have hunit : IsUnit ((2 : ResidueGroup n) ^ L) := by
      apply IsUnit.pow
      have : ((2 : ℕ) : ResidueGroup n) = 2 := by norm_num
      rw [← this, ZMod.isUnit_iff_coprime]
      exact Nat.Coprime.pow_right n (by decide)
    have hQ0 : ((Q : ℤ) : ResidueGroup n) = 0 := by
      rw [hQ]; push_cast; exact_mod_cast ZMod.natCast_self (3 ^ n)
    have hKy : ((K : ℤ) : ResidueGroup n) = bkThetaResidue n ξ y := by
      apply hunit.mul_left_cancel
      have := congrArg (fun z : ℤ => (z : ResidueGroup n)) hKL
      simp only [Int.cast_mul, Int.cast_pow, Int.cast_add, Int.cast_ofNat, hQ0] at this
      rw [this, ← hrg', hrg, hN, ZMod.coe_valMinAbs]
      have hr : r = (r - 1) + 1 := by omega
      conv_rhs => rw [hr]
      ring
    -- `valMinAbs (r y) - K` is divisible by `Q`
    have hdvd : (Q : ℤ) ∣ (bkThetaResidue n ξ y).valMinAbs - K := by
      rw [hQ, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp [hKy]
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    have hθy : bkTheta n ξ y = ((bkThetaResidue n ξ y).valMinAbs : ℝ) / Q := by
      rw [← three_pow_mul_bkTheta n ξ y, hQ]; push_cast; field_simp
    have hk' : ((bkThetaResidue n ξ y).valMinAbs : ℝ) = Q * k + K := by
      exact_mod_cast (by linear_combination hk : (bkThetaResidue n ξ y).valMinAbs = Q * k + K)
    have hKL' : (2 : ℝ) ^ L * K = 9 ^ (r - 1) * 2 ^ ω * (m * Q + 9 * N) := by
      exact_mod_cast hKL
    have h2 : (2 : ℝ) ^ L ≠ 0 := by positivity
    have hKQ : (9 : ℝ) ^ (r - 1) * (2 ^ ω * (m : ℝ) + 9 * 2 ^ ω * N / Q) / 2 ^ L = K / Q := by
      rw [div_eq_div_iff h2 hQpos.ne']
      field_simp
      linear_combination -hKL'
    rw [hθy, hk', hKQ]
    field_simp
    ring

end CollatzPosDens
