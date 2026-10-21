/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkEpsStarRange
public import CollatzPosDens.Case3.C3H17CrossingCost
public import CollatzPosDens.Case3.C3H17TableBound
public import CollatzPosDens.CharSum.ChColtopAngle
public import CollatzPosDens.CharSum.ChColtopOdd

/-!
# The cost of a first raw crossing set by the cost table

Let `ξ ∈ G_n` be a unit and `e ∈ 𝒫` black (for `ε_*`) with gap `ω = gap(e) ≥ 224`, let
`Δ = Δ(e)`, and let `M₀` be an integer such that `2^{17}` divides `3^n M₀ + 3^n ϑ(j(e), l_Δ)`.
For integers `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and `1 ≤ r ≤ ⌊9ω/32⌋`,
```
∑_{π ∈ 𝒞_ω(c,o,r)} bw^⊗(π) exp(-z_* N^*(e, π; |π|)) ≤ ϖ(c) 𝖱(r - 1, ω + o - c) ct_{c,o}(9^r M₀).
```

The integer `N = 3^n ϑ(j(e), l_Δ)` is odd, so `3^n M₀ ≡ -N (mod 2)` makes `M₀` odd, and so is
`m = 9^r M₀`. Put `β = 9^r ϑ(j(e), l_Δ)`. Since `l(e) + ω = l_Δ`, the angle at the column top is
`|ϑ(j(e), l_Δ)| ≤ ε_* 2^{-ω}`, and `9^5 < 2^{16}` with `r ≤ 9ω/32` gives `9^r ≤ 2^{9ω/10}`, so
`|β| < 10^{-6}`. The bound
`CollatzPosDens.BkBlack.tsum_c3CrossingSet_mul_exp_le_c3H17FirstCost` then reads the left side as
at most `ϖ(c) 𝖱(r - 1, ω + o - c) xc_{c,o}(m + β)`, and `xc_{c,o}(m + β) ≤ ct_{c,o}(m)` on the
whole cell.

## Main results

* `CollatzPosDens.BkBlack.tsum_c3CrossingSet_mul_exp_le_c3H17Table`: the bound above.

## Implementation notes

As for `CollatzPosDens.BkBlack.tsum_c3CrossingSet_mul_exp_le_c3H17FirstCost`, the gap is a
natural number `ω` with `(ω : ℤ) = gap(e)`, the bound `r ≤ ⌊9ω/32⌋` is `r ≤ 9 * ω / 32` in `ℕ`,
the standing hypothesis that `ξ` is a unit is explicit, and the divisibility by `2^{17}` is the
existence of an integer `k` with `3^n M₀ + 3^n ϑ(j(e), l_Δ) = 2^{17} k` in `ℝ`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- `10^6 · 9^r ≤ 2^ω` whenever `32 r ≤ 9 ω` and `ω ≥ 200`. -/
private lemma ten_pow_six_mul_nine_pow_le_two_pow {ω r : ℕ} (hω : 200 ≤ ω)
    (hr : r ≤ 9 * ω / 32) : 10 ^ 6 * 9 ^ r ≤ 2 ^ ω := by
  have h32 : 32 * r ≤ 9 * ω := by omega
  refine (Nat.pow_le_pow_iff_left (n := 5) (by norm_num)).1 ?_
  calc (10 ^ 6 * 9 ^ r) ^ 5 = 10 ^ 30 * (9 ^ 5) ^ r := by
        rw [← pow_mul, mul_comm 5 r, pow_mul]; ring
    _ ≤ 2 ^ 100 * (2 ^ 16) ^ r :=
        Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left (by norm_num) r)
    _ = 2 ^ (100 + 16 * r) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (5 * ω) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = (2 ^ ω) ^ 5 := by ring

/-- **The cost of a first raw crossing set by the cost table.** Let `ξ` be a unit, `e ∈ 𝒫` black
(for `ε_*`) with gap `ω = gap(e) ≥ 224`, `Δ = Δ(e)`, and `M₀` an integer such that `2^{17}`
divides `3^n M₀ + 3^n ϑ(j(e), l_Δ)`. For integers `2 ≤ c ≤ 16`, `1 ≤ o ≤ c` and
`1 ≤ r ≤ ⌊9ω/32⌋`, `∑_{π ∈ 𝒞_ω(c,o,r)} bw^⊗(π) exp(-z_* N^*(e, π; |π|)) ≤
ϖ(c) 𝖱(r - 1, ω + o - c) ct_{c,o}(9^r M₀)`. -/
@[collatz_pos_dens "lem_c3_h17_row_cost"]
theorem BkBlack.tsum_c3CrossingSet_mul_exp_le_c3H17Table {n : ℕ} {ξ : ResidueGroup n}
    {e : ℤ × ℤ} (hb : BkBlack n ξ (epsStar : ℝ) e) (hξ : IsResidueUnit ξ) (he : e ∈ bkPoints)
    {ω : ℕ} (hω : (ω : ℤ) = trGap n ξ (epsStar : ℝ) e) (hω224 : 224 ≤ ω) (M₀ : ℤ)
    (hdvd : ∃ k : ℤ, (3 : ℝ) ^ n * M₀ +
      3 ^ n * bkTheta n ξ (bkJ e, (bkCanonTriangle n ξ (epsStar : ℝ) e he).l) = 2 ^ 17 * k)
    {c o : ℤ} {r : ℕ} (hc : 2 ≤ c) (hc16 : c ≤ 16) (ho : 1 ≤ o) (hoc : o ≤ c) (hr : 1 ≤ r)
    (hrω : r ≤ 9 * ω / 32) :
    ∑' π : c3CrossingSet ω c o r,
        trListWeight π.1 * Real.exp (-(zStar : ℝ) * trCount n ξ e π.1 π.1.length) ≤
      varpi c * rawMass (r - 1) (ω + o - c) * (c3H17Table c o (9 ^ r * M₀) : ℝ) := by
  set θ := bkTheta n ξ (bkJ e, (bkCanonTriangle n ξ (epsStar : ℝ) e he).l) with hθ
  have hε := epsStar_mem_bkRange (K := ℝ)
  -- `M₀` is odd, as `3^n ϑ(j(e), l_Δ)` is an odd integer
  obtain ⟨N, hN, hNodd⟩ := odd_three_pow_mul_bkTheta_bkColTop hξ hε.1 hε.2 he hb
  obtain ⟨k, hk⟩ := hdvd
  have hkZ : 3 ^ n * M₀ + N = 2 ^ 17 * k := by
    rw [← hθ] at hN
    rw [← hN] at hk
    exact_mod_cast hk
  have hM₀ : Odd M₀ := by
    have h3 : Odd (3 ^ n * M₀) := by
      rw [show 3 ^ n * M₀ = 2 * (2 ^ 16 * k) - N by linarith]
      exact (even_two_mul _).sub_odd hNodd
    exact (Int.odd_mul.1 h3).2
  have hm : Odd (9 ^ r * M₀) := (Odd.pow (by decide)).mul hM₀
  -- the angle `β = 9^r ϑ(j(e), l_Δ)` is at most `10^{-6}`
  have hωl : bkL e + ω = (bkCanonTriangle n ξ (epsStar : ℝ) e he).l := by
    rw [bkCanonTriangle_l, bkColTop_eq_add_trGap, ← hω]
  have hθle := abs_bkTheta_colTop_le hξ hε.1 hε.2 he hb ω hωl
  rw [← hθ] at hθle
  have hnat : ((10 : ℝ) ^ 6 * 9 ^ r ≤ 2 ^ ω) := by
    exact_mod_cast ten_pow_six_mul_nine_pow_le_two_pow (by omega) hrω
  have h2ω : (0 : ℝ) < 2 ^ ω := by positivity
  have hβ : |(9 : ℝ) ^ r * θ| ≤ 1 / 10 ^ 6 := by
    rw [zpow_neg, zpow_natCast] at hθle
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 9 ^ r)]
    calc (9 : ℝ) ^ r * |θ| ≤ 9 ^ r * ((epsStar : ℝ) * (2 ^ ω)⁻¹) :=
          mul_le_mul_of_nonneg_left hθle (by positivity)
      _ ≤ 9 ^ r * (2 ^ ω)⁻¹ := by
          gcongr
          exact mul_le_of_le_one_left (by positivity) (by linarith [hε.2])
      _ ≤ 1 / 10 ^ 6 := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ h2ω (by norm_num)]
          linarith
  have hcell := c3H17FirstCost_le_c3H17Table hc16 ho hm hβ
  have hx : (9 : ℝ) ^ r * (M₀ + θ) = ((9 ^ r * M₀ : ℤ) : ℝ) + 9 ^ r * θ := by
    push_cast
    ring
  refine (hb.tsum_c3CrossingSet_mul_exp_le_c3H17FirstCost hξ he hω hω224 M₀ ⟨k, hk⟩ hc hc16 ho
    hoc hr hrω).trans ?_
  rw [← hθ, hx]
  exact mul_le_mul_of_nonneg_left hcell
    (mul_nonneg (varpi_nonneg c) (rawMass_nonneg _ _))

end CollatzPosDens
