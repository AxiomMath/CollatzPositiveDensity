/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The cosine on a quarter turn

For `0 ≤ a ≤ 1/4`, the cosine `cos (2π a)` is approximated within `10⁻⁹` by the Taylor
polynomial `P(y) = ∑_{k=0}^{7} (-1)^k y^(2k) / (2k)!` of degree `15` evaluated at
`y = 2 π₀ a`, where `π₀ = 3.141592654` (so `2 π₀ = 6.283185308`).

The proof splits the error in two. Since `0 ≤ y ≤ 8/5`, the Taylor remainder of the
exponential at `y i` bounds `|cos y - P(y)|` by `2 y^16 / 16! < 2 · 10⁻¹⁰`. Since
`|π - π₀| < 42 · 10⁻¹¹` and `cos` is `1`-Lipschitz, `|cos (2π a) - cos y| ≤ 21 · 10⁻¹¹`.

## Main results

* `CollatzPosDens.abs_cos_sub_cosTaylorSum_le`: `|cos y - P(y)| ≤ 2 |y|^16 / 16!` for `|y| ≤ 8`.
* `CollatzPosDens.abs_cos_two_pi_sub_cosTaylorSum_le`: the quarter-turn bound.
* `CollatzPosDens.TrDirectCertificate.cos_le_cosB`: for natural numbers `P` and `Q > 0`,
  `cos (2π P/Q) ≤ cosB P Q / 2^64 - 1`, where `cosB P Q` is a natural-number computation of the
  Taylor bound on the scale `2^64`.

## Implementation notes

The Taylor estimate is taken from the remainder bound `Complex.exp_bound'` for the complex
exponential, whose real part is the cosine; this gives the Lagrange bound `y^16/16!` up to a
factor `2`, which the margin absorbs. The enclosure of `π` is Mathlib's twenty-digit enclosure
`Real.pi_gt_d20`, `Real.pi_lt_d20`, in place of the Machin-formula computation.

## References

* [collatz-310], Lemma "The cosine on a quarter turn".
-/

@[expose] public section

namespace CollatzPosDens

open Finset Real

/-- The Taylor bound for the cosine at degree `15`: for `|y| ≤ 8`,
`|cos y - ∑_{k=0}^{7} (-1)^k y^(2k) / (2k)!| ≤ 2 |y|^16 / 16!`. -/
theorem abs_cos_sub_cosTaylorSum_le {y : ℝ} (hy : |y| ≤ 8) :
    |Real.cos y - ∑ k ∈ range 8, (-1) ^ k / ((2 * k).factorial : ℝ) * y ^ (2 * k)| ≤
      |y| ^ 16 / (Nat.factorial 16) * 2 := by
  have hn : ‖(y : ℂ) * Complex.I‖ = |y| := by simp
  have hb := Complex.exp_bound' (x := (y : ℂ) * Complex.I) (n := 16)
    (by rw [hn]; norm_num; linarith)
  rw [hn] at hb
  have hsum : ∑ m ∈ range 16, ((y : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
      ((∑ k ∈ range 8, (-1) ^ k / ((2 * k).factorial : ℝ) * y ^ (2 * k) : ℝ) : ℂ) +
        ((y - y ^ 3 / 6 + y ^ 5 / 120 - y ^ 7 / 5040 + y ^ 9 / 362880 -
          y ^ 11 / 39916800 + y ^ 13 / 6227020800 - y ^ 15 / 1307674368000 : ℝ) : ℂ) *
            Complex.I := by
    simp only [sum_range_succ, sum_range_zero, mul_pow]
    have h2 : Complex.I ^ 2 = -1 := Complex.I_sq
    simp only [Nat.factorial, Nat.cast_ofNat, Nat.cast_succ, Nat.mul_zero, Nat.mul_one]
    push_cast
    linear_combination ((y : ℂ) ^ 2 / 2 + (y : ℂ) ^ 3 * Complex.I / 6 + (y : ℂ) ^ 6 / 720 +
      (y : ℂ) ^ 7 * Complex.I / 5040 + (y : ℂ) ^ 10 / 3628800 +
      (y : ℂ) ^ 11 * Complex.I / 39916800 + (y : ℂ) ^ 14 / 87178291200 +
      (y : ℂ) ^ 15 * Complex.I / 1307674368000) * h2
  rw [hsum] at hb
  refine le_trans (le_of_eq ?_) ((Complex.abs_re_le_norm _).trans hb)
  rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.add_re, Complex.ofReal_re,
    Complex.re_ofReal_mul, Complex.I_re, mul_zero, add_zero]

/-- **The cosine on a quarter turn.** For `0 ≤ a ≤ 1/4`,
`|cos (2π a) - ∑_{k=0}^{7} (-1)^k / (2k)! · (6283185308 a / 10⁹)^(2k)| ≤ 10⁻⁹`. -/
@[collatz_pos_dens "lem_tr_cos_taylor"]
theorem abs_cos_two_pi_sub_cosTaylorSum_le {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1 / 4) :
    |Real.cos (2 * π * a) - ∑ k ∈ range 8,
        (-1) ^ k / ((2 * k).factorial : ℝ) * (6283185308 * a / 10 ^ 9) ^ (2 * k)| ≤
      1 / 10 ^ 9 := by
  set y : ℝ := 6283185308 * a / 10 ^ 9 with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hy1 : y ≤ 8 / 5 := by rw [hy]; linarith
  have hT := abs_cos_sub_cosTaylorSum_le (y := y) (by rw [abs_of_nonneg hy0]; linarith)
  have hpow : |y| ^ 16 ≤ (8 / 5 : ℝ) ^ 16 := by
    rw [abs_of_nonneg hy0]; exact pow_le_pow_left₀ hy0 hy1 16
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  have hL := Real.abs_cos_sub_cos_le (2 * π * a) y
  have hL' : |2 * π * a - y| ≤ 21 / 100000000000 := by
    rw [hy, show 2 * π * a - 6283185308 * a / 10 ^ 9 = 2 * a * (π - 3141592654 / 10 ^ 9) by ring,
      abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * a)]
    have hpi : |π - 3141592654 / 10 ^ 9| ≤ 42 / 100000000000 := by
      rw [abs_le]; constructor <;> norm_num <;> linarith
    nlinarith [abs_nonneg (π - 3141592654 / 10 ^ 9)]
  have hfac : ((Nat.factorial 16 : ℕ) : ℝ) = 20922789888000 := by norm_num [Nat.factorial]
  rw [hfac] at hT
  calc _ ≤ |Real.cos (2 * π * a) - Real.cos y| +
        |Real.cos y - ∑ k ∈ range 8, (-1) ^ k / ((2 * k).factorial : ℝ) * y ^ (2 * k)| :=
          abs_sub_le _ _ _
    _ ≤ 21 / 100000000000 + (8 / 5 : ℝ) ^ 16 / 20922789888000 * 2 := by
        gcongr
        · exact hL.trans hL'
        · exact hT.trans (by gcongr)
    _ ≤ 1 / 10 ^ 9 := by norm_num

/-! ### Fixed-point cosine bounds

Natural-number computations, on the scale `2^64`, of upper bounds for `cos (2π P/Q)` at rational
points `P/Q`, by the Taylor polynomial of the quarter-turn bound. -/

namespace TrDirectCertificate

/-! ### The scale -/

/-- The fixed-point scale `2^64`. -/
def one : ℕ := 18446744073709551616

/-- The scale `one` equals `2^64`. -/
theorem one_eq : one = 2 ^ 64 := rfl

/-- The scale `one` is positive. -/
theorem one_pos : 0 < one := by decide

/-! ### Rounding lemmas -/

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The quotient `x / d` is at most the ceiling division `(x + d - 1) / d` of natural numbers. -/
theorem div_le_ceilDiv (x d : ℕ) (hd : 0 < d) : (x : K) / d ≤ ((x + d - 1) / d : ℕ) := by
  rw [div_le_iff₀ (by exact_mod_cast hd)]
  have h := Nat.lt_div_mul_add (a := x + d - 1) hd
  have h' : x ≤ (x + d - 1) / d * d := by omega
  exact_mod_cast h'

/-- The difference `a - b` is at most the cast of the truncated subtraction `a - b` in `ℕ`. -/
theorem sub_le_natSub (a b : ℕ) : (a : K) - b ≤ ((a - b : ℕ) : K) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h]
    simp only [Nat.cast_zero, sub_nonpos]
    exact_mod_cast h

/-! ### The cosine bound -/

/-- The even part `∑_{k even} (14!/(2k)!) Z^k W^{7-k}` of the homogenised Taylor numerator. -/
def taylorPos (Z W : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.mul 87178291200 (Nat.pow W 7))
      (Nat.mul (Nat.mul 3632428800 (Nat.pow Z 2)) (Nat.pow W 5)))
    (Nat.add (Nat.mul (Nat.mul 2162160 (Nat.pow Z 4)) (Nat.pow W 3))
      (Nat.mul (Nat.mul 182 (Nat.pow Z 6)) W))

/-- The odd part `∑_{k odd} (14!/(2k)!) Z^k W^{7-k}` of the homogenised Taylor numerator. -/
def taylorNeg (Z W : ℕ) : ℕ :=
  Nat.add (Nat.add (Nat.mul 43589145600 (Nat.mul Z (Nat.pow W 6)))
      (Nat.mul (Nat.mul 121080960 (Nat.pow Z 3)) (Nat.pow W 4)))
    (Nat.add (Nat.mul (Nat.mul 24024 (Nat.pow Z 5)) (Nat.pow W 2)) (Nat.pow Z 7))

/-- The closed form of `taylorPos Z W`. -/
theorem taylorPos_eq (Z W : ℕ) : taylorPos Z W =
    87178291200 * W ^ 7 + 3632428800 * Z ^ 2 * W ^ 5 + 2162160 * Z ^ 4 * W ^ 3 +
      182 * Z ^ 6 * W := by
  simp only [taylorPos, Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; ring

/-- The closed form of `taylorNeg Z W`. -/
theorem taylorNeg_eq (Z W : ℕ) : taylorNeg Z W =
    43589145600 * Z * W ^ 6 + 121080960 * Z ^ 3 * W ^ 4 + 24024 * Z ^ 5 * W ^ 2 + Z ^ 7 := by
  simp only [taylorNeg, Nat.add_eq, Nat.mul_eq, Nat.pow_eq]; ring

/-- The Taylor polynomial `K(y) = ∑_{k=0}^{7} (-1)^k y^{2k} / (2k)!` at `a / b` as a quotient of
natural numbers. -/
theorem cosTaylorSum_div (a b : ℕ) (hb : b ≠ 0) :
    ∑ k ∈ range 8, (-1 : ℝ) ^ k / ((2 * k).factorial : ℝ) * ((a : ℝ) / b) ^ (2 * k) =
      ((taylorPos (a ^ 2) (b ^ 2) : ℝ) - taylorNeg (a ^ 2) (b ^ 2)) /
        ((b ^ 2) ^ 7 * 87178291200) := by
  have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
  rw [taylorPos_eq, taylorNeg_eq]
  simp only [sum_range_succ, sum_range_zero]
  norm_num [Nat.factorial]
  field_simp
  ring

/-- The rounded-up value `⌈2^64 N / D⌉ + ⌈2^64 / 10^9⌉`. -/
def roundCos (N D : ℕ) : ℕ :=
  Nat.add (Nat.div (Nat.sub (Nat.add (Nat.mul one N) D) 1) D) 18446744074

/-- The closed form of `roundCos N D`. -/
theorem roundCos_eq (N D : ℕ) : roundCos N D = (one * N + D - 1) / D + 18446744074 := rfl

/-- `2^64 (N / D + 10^{-9}) ≤ roundCos N D`. -/
theorem le_roundCos (N D : ℕ) (hD : 0 < D) :
    (N : ℝ) / D + 18446744074 / one ≤ (roundCos N D : ℝ) / one := by
  rw [roundCos_eq]
  have h1 := div_le_ceilDiv (K := ℝ) (one * N) D hD
  have hone : (0 : ℝ) < one := by exact_mod_cast one_pos
  have : ((one * N : ℕ) : ℝ) / D / one = (N : ℝ) / D := by
    push_cast; field_simp
  rw [← this, Nat.cast_add, add_div]
  gcongr
  norm_num

/-- The reduced numerator `A = |R - Q|`, `R = (2P + Q) mod 2Q`, so that
`|P/Q - ⌊P/Q + 1/2⌋| = A / (2Q)`. -/
def redA (P Q : ℕ) : ℕ :=
  let R := Nat.mod (Nat.add (Nat.mul 2 P) Q) (Nat.mul 2 Q)
  cond (Nat.ble Q R) (Nat.sub R Q) (Nat.sub Q R)

/-- The closed form of `redA P Q`, as `|R - Q|` with `R = (2P + Q) mod 2Q`. -/
theorem redA_eq (P Q : ℕ) : redA P Q =
    if Q ≤ (2 * P + Q) % (2 * Q) then (2 * P + Q) % (2 * Q) - Q
    else Q - (2 * P + Q) % (2 * Q) := by
  simp only [redA, cond_eq_ite, Nat.ble_eq]
  rfl

/-- The denominator `(10^9 Q)^14 · 14!`. -/
def cosDen (Q : ℕ) : ℕ := Nat.mul (Nat.pow (Nat.pow (Nat.mul 1000000000 Q) 2) 7) 87178291200

/-- The closed form of `cosDen Q`. -/
theorem cosDen_eq (Q : ℕ) : cosDen Q = ((1000000000 * Q) ^ 2) ^ 7 * 87178291200 := rfl

/-- The bound in the case `A ≤ Q / 2`: the Taylor polynomial at `π₀ A / Q`. -/
def cosNear (A Q : ℕ) : ℕ :=
  roundCos (Nat.sub (Nat.add (cosDen Q)
      (taylorPos (Nat.pow (Nat.mul 3141592654 A) 2) (Nat.pow (Nat.mul 1000000000 Q) 2)))
    (taylorNeg (Nat.pow (Nat.mul 3141592654 A) 2) (Nat.pow (Nat.mul 1000000000 Q) 2))) (cosDen Q)

/-- The bound in the case `A > Q / 2`: minus the Taylor polynomial at `π₀ (Q - A) / Q`. -/
def cosFar (A Q : ℕ) : ℕ :=
  roundCos (Nat.sub (Nat.add (cosDen Q)
      (taylorNeg (Nat.pow (Nat.mul 3141592654 (Nat.sub Q A)) 2)
        (Nat.pow (Nat.mul 1000000000 Q) 2)))
    (taylorPos (Nat.pow (Nat.mul 3141592654 (Nat.sub Q A)) 2)
      (Nat.pow (Nat.mul 1000000000 Q) 2))) (cosDen Q)

/-- The closed form of `cosNear A Q`. -/
theorem cosNear_eq (A Q : ℕ) : cosNear A Q =
    roundCos (cosDen Q + taylorPos ((3141592654 * A) ^ 2) ((1000000000 * Q) ^ 2) -
      taylorNeg ((3141592654 * A) ^ 2) ((1000000000 * Q) ^ 2)) (cosDen Q) := rfl

/-- The closed form of `cosFar A Q`. -/
theorem cosFar_eq (A Q : ℕ) : cosFar A Q =
    roundCos (cosDen Q + taylorNeg ((3141592654 * (Q - A)) ^ 2) ((1000000000 * Q) ^ 2) -
      taylorPos ((3141592654 * (Q - A)) ^ 2) ((1000000000 * Q) ^ 2)) (cosDen Q) := rfl

/-- An upper bound for `2^64 (1 + cos (2π P / Q))`, from the Taylor polynomial of degree `14`. -/
def cosB (P Q : ℕ) : ℕ :=
  let A := redA P Q
  cond (Nat.ble (Nat.mul 2 A) Q) (cosNear A Q) (cosFar A Q)

/-- `cosB P Q` is `cosNear A Q` if `2A ≤ Q` and `cosFar A Q` otherwise, where `A = redA P Q`. -/
theorem cosB_eq (P Q : ℕ) :
    cosB P Q = if 2 * redA P Q ≤ Q then cosNear (redA P Q) Q else cosFar (redA P Q) Q := by
  simp only [cosB, cond_eq_ite, Nat.ble_eq]
  rfl

/-- The Taylor value as a quotient: `1 + K(π₀ a / Q) = (D + N₊ - N₋) / D`. -/
theorem one_add_cosTaylorSum (a Q : ℕ) (hQ : 0 < Q) :
    1 + ∑ k ∈ range 8, (-1 : ℝ) ^ k / ((2 * k).factorial : ℝ) *
        (((3141592654 * a : ℕ) : ℝ) / ((1000000000 * Q : ℕ) : ℝ)) ^ (2 * k) =
      ((cosDen Q : ℝ) + taylorPos ((3141592654 * a) ^ 2) ((1000000000 * Q) ^ 2) -
        taylorNeg ((3141592654 * a) ^ 2) ((1000000000 * Q) ^ 2)) / cosDen Q := by
  have hb : (1000000000 * Q : ℕ) ≠ 0 := by positivity
  have hD : (0 : ℝ) < cosDen Q := by rw [cosDen_eq]; positivity
  rw [cosTaylorSum_div _ _ hb]
  have : (cosDen Q : ℝ) = ((((1000000000 * Q : ℕ) : ℝ) ^ 2) ^ 7 * 87178291200) := by
    rw [cosDen_eq]; push_cast; ring
  rw [this] at hD ⊢
  field_simp
  push_cast
  ring

/-- `2^64 (1 + K(π₀ A / Q) + 18446744074 / 2^64) ≤ cosNear A Q`, where `K` is the Taylor
polynomial `∑_{k=0}^{7} (-1)^k y^{2k} / (2k)!`. -/
theorem cosNear_spec (A Q : ℕ) (hQ : 0 < Q) :
    1 + ∑ k ∈ range 8, (-1 : ℝ) ^ k / ((2 * k).factorial : ℝ) *
        (((3141592654 * A : ℕ) : ℝ) / ((1000000000 * Q : ℕ) : ℝ)) ^ (2 * k) +
      18446744074 / one ≤ (cosNear A Q : ℝ) / one := by
  have hD : 0 < cosDen Q := by rw [cosDen_eq]; positivity
  rw [one_add_cosTaylorSum A Q hQ, cosNear_eq]
  refine le_trans ?_ (le_roundCos _ _ hD)
  gcongr
  have := sub_le_natSub (K := ℝ)
    (cosDen Q + taylorPos ((3141592654 * A) ^ 2) ((1000000000 * Q) ^ 2))
    (taylorNeg ((3141592654 * A) ^ 2) ((1000000000 * Q) ^ 2))
  push_cast at this
  exact this

/-- `2^64 (1 - K(π₀ (Q - A) / Q) + 18446744074 / 2^64) ≤ cosFar A Q`, where `K` is the Taylor
polynomial `∑_{k=0}^{7} (-1)^k y^{2k} / (2k)!`. -/
theorem cosFar_spec (A Q : ℕ) (hQ : 0 < Q) :
    1 - ∑ k ∈ range 8, (-1 : ℝ) ^ k / ((2 * k).factorial : ℝ) *
        (((3141592654 * (Q - A) : ℕ) : ℝ) / ((1000000000 * Q : ℕ) : ℝ)) ^ (2 * k) +
      18446744074 / one ≤ (cosFar A Q : ℝ) / one := by
  have hD : 0 < cosDen Q := by rw [cosDen_eq]; positivity
  have hD' : (0 : ℝ) < cosDen Q := by exact_mod_cast hD
  have h := one_add_cosTaylorSum (Q - A) Q hQ
  rw [cosFar_eq]
  refine le_trans ?_ (le_roundCos _ _ hD)
  have := sub_le_natSub (K := ℝ)
    (cosDen Q + taylorNeg ((3141592654 * (Q - A)) ^ 2) ((1000000000 * Q) ^ 2))
    (taylorPos ((3141592654 * (Q - A)) ^ 2) ((1000000000 * Q) ^ 2))
  push_cast at this
  refine add_le_add (le_trans (le_of_eq ?_) (div_le_div_of_nonneg_right this hD'.le)) le_rfl
  rw [eq_div_iff hD'.ne']
  rw [eq_div_iff hD'.ne'] at h
  linarith

/-- **The cosine bound.** For natural numbers `P` and `Q > 0`,
`cos (2π P / Q) ≤ cosB P Q / 2^64 - 1`. With `α = A / (2Q) = |P/Q - ⌊P/Q + 1/2⌋|`, this is the
Taylor bound `CollatzPosDens.abs_cos_two_pi_sub_cosTaylorSum_le` at `α` if `2A ≤ Q`, and at
`1/2 - α` (as `cos (2πα) = -cos (2π (1/2 - α))`) otherwise, the error `10^{-9}` being absorbed by
`18446744074 ≥ 2^64 · 10^{-9}`. -/
theorem cos_le_cosB (P Q : ℕ) (hQ : 0 < Q) :
    Real.cos (2 * π * ((P : ℝ) / Q)) ≤ (cosB P Q : ℝ) / one - 1 := by
  set R := (2 * P + Q) % (2 * Q) with hR
  set K := (2 * P + Q) / (2 * Q) with hK
  set A := redA P Q with hA
  have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hR2 : R < 2 * Q := Nat.mod_lt _ (by omega)
  have hAR : A = if Q ≤ R then R - Q else Q - R := by rw [hA, redA_eq]
  have hAQ : A ≤ Q := by rw [hAR]; split_ifs <;> omega
  -- the reduction `cos (2π P/Q) = cos (2π A/(2Q))`
  have hred : (P : ℝ) / Q = ((R : ℝ) - Q) / (2 * Q) + (K : ℝ) := by
    have hdiv := Nat.div_add_mod (2 * P + Q) (2 * Q)
    rw [← hR, ← hK] at hdiv
    have h' : ((2 * Q * K + R : ℕ) : ℝ) = ((2 * P + Q : ℕ) : ℝ) := by rw [hdiv]
    push_cast at h'
    field_simp
    linarith
  have hcosA : Real.cos (2 * π * ((P : ℝ) / Q)) = Real.cos (2 * π * ((A : ℝ) / (2 * Q))) := by
    rw [hred, mul_add, show 2 * π * (K : ℝ) = ((K : ℤ) : ℝ) * (2 * π) by push_cast; ring,
      Real.cos_add_int_mul_two_pi, hAR]
    split_ifs with h
    · rw [Nat.cast_sub h]
    · rw [Nat.cast_sub (not_le.1 h).le, ← Real.cos_neg]
      congr 1
      ring
  have herr : (1 : ℝ) / 10 ^ 9 ≤ 18446744074 / one := by norm_num [one]
  rw [hcosA, cosB_eq, ← hA]
  by_cases hcase : 2 * A ≤ Q
  · simp only [hcase, ↓reduceIte]
    have h0 : (0 : ℝ) ≤ A / (2 * Q) := by positivity
    have h1 : (A : ℝ) / (2 * Q) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      have : (2 * A : ℝ) ≤ Q := by exact_mod_cast hcase
      linarith
    have hT := abs_cos_two_pi_sub_cosTaylorSum_le h0 h1
    have hy : 6283185308 * ((A : ℝ) / (2 * Q)) / 10 ^ 9 =
        ((3141592654 * A : ℕ) : ℝ) / ((1000000000 * Q : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring
    rw [hy] at hT
    have := cosNear_spec A Q hQ
    have := (abs_le.1 hT).2
    linarith
  · simp only [hcase, ↓reduceIte]
    have hAQ' : (Q : ℝ) < 2 * A := by exact_mod_cast (not_le.1 hcase)
    have hpi : Real.cos (2 * π * ((A : ℝ) / (2 * Q))) =
        -Real.cos (2 * π * (((Q - A : ℕ) : ℝ) / (2 * Q))) := by
      rw [Nat.cast_sub hAQ, ← Real.cos_pi_sub]
      congr 1
      field_simp
      ring
    have h0 : (0 : ℝ) ≤ ((Q - A : ℕ) : ℝ) / (2 * Q) := by positivity
    have h1 : ((Q - A : ℕ) : ℝ) / (2 * Q) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity), Nat.cast_sub hAQ]
      linarith
    have hT := abs_cos_two_pi_sub_cosTaylorSum_le h0 h1
    have hy : 6283185308 * (((Q - A : ℕ) : ℝ) / (2 * Q)) / 10 ^ 9 =
        ((3141592654 * (Q - A) : ℕ) : ℝ) / ((1000000000 * Q : ℕ) : ℝ) := by
      rw [Nat.cast_mul (3141592654 : ℕ) (Q - A)]
      push_cast
      field_simp
      ring
    rw [hy] at hT
    have := cosFar_spec A Q hQ
    have := (abs_le.1 hT).1
    rw [hpi]
    linarith

/-- `cosB` depends on `P` only through `P mod Q`. -/
theorem cosB_mod (P Q : ℕ) : cosB (P % Q) Q = cosB P Q := by
  have h := Nat.mod_add_div P Q
  have : (2 * (P % Q) + Q) % (2 * Q) = (2 * P + Q) % (2 * Q) := by
    calc (2 * (P % Q) + Q) % (2 * Q) = ((2 * (P % Q) + Q) + (2 * Q) * (P / Q)) % (2 * Q) :=
          (Nat.add_mul_mod_self_left _ _ _).symm
      _ = (2 * P + Q) % (2 * Q) := by congr 1; linarith
  have hA : redA (P % Q) Q = redA P Q := by rw [redA_eq, redA_eq, this]
  rw [cosB_eq, cosB_eq, hA]

/-- `cosB` depends on `P` only through its residue modulo `Q`. -/
theorem cosB_congr {P P' Q : ℕ} (h : P ≡ P' [MOD Q]) : cosB P Q = cosB P' Q := by
  rw [← cosB_mod P, ← cosB_mod P', h]

end TrDirectCertificate

end CollatzPosDens
