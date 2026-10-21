/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Case3.C3H17ValuesDataBase
public import CollatzPosDens.Case3.C3H17TablePeriod
public import Mathlib.Algebra.BigOperators.Field

/-!
# The cosine bounds at the turns `n / 2^17`

At a turn `θ = n / 2^17` the rounded cosine bound `cb(θ)` of `U^{10^{-18}}_c` (with
`η = 10^{-18}`) is an integer multiple of `10^{-18}`: writing `r = n mod 2^17`, it is `1` if
`r = 0`, and otherwise `10^{-18} ⌈10^{18} (P(2 π₀ a / 2^17) + E_cos)⌉` with
`a = min (r, 2^17 - r)`, since the Taylor polynomial `P` is even. With
`P(2 π₀ a / 2^17) = N(a) / (D^{24} 24!)`, `D = 10^{15} 2^{16}`, where
`N(a) = ∑_{k ≤ 12} (-1)^k (3141592653589793 a)^{2k} D^{24 - 2k} 24! / (2k)!` is an integer,
this is an exact integer ceiling division, the integer `cosI n` below.

The integer `cosI n` depends only on `±n mod 2^17`. For `1 ≤ m ≤ 14` the multiplier `2^m - 1`
is congruent modulo `2^17` to `± 3^{f_m}` for an explicit exponent `f_m`, so the cosine bounds
of the radicand of `U^{10^{-18}}_c` at `θ = ± 2^v 3^J / 2^17` are the bounds at the points
`2^{v + i} 3^{J + f_m}`.

## Main definitions

* `CollatzPosDens.C3H17Values.cosNum`: the integer `⌈10^{18} (P(2 π₀ a / 2^17) + E_cos)⌉`.
* `CollatzPosDens.C3H17Values.cosI`: the cosine bound at `n / 2^17`, in units of `10^{-18}`.
* `CollatzPosDens.C3H17Values.mulExp`: the exponents `f_m`.

## Main results

* `CollatzPosDens.C3H17Values.trCapCosBound_eq_cosI`: `cb(n / 2^17) = cosI n / 10^{18}`.
* `CollatzPosDens.C3H17Values.cosI_neg`, `CollatzPosDens.C3H17Values.cosI_add_mul`: `cosI`
  is even and `2^17`-periodic.
* `CollatzPosDens.C3H17Values.cosI_mul_pow_two_sub_one`:
  `cosI ((2^m - 1) X) = cosI (3^{f_m} X)` for `1 ≤ m ≤ 14`.
-/

@[expose] public section

namespace CollatzPosDens

namespace C3H17Values

open Finset

/-! ### The cosine polynomial at `2 π₀ a / 2^17` -/

/-- The denominator `D = 10^{15} 2^{16}` of `2 π₀ / 2^17 = 3141592653589793 / D`. -/
def cosD : ℤ := 10 ^ 15 * 2 ^ 16

/-- The coefficient `(-1)^k D^{24 - 2k} 24! / (2k)!` of `A^k`, `A = (3141592653589793 a)^2`, in
the numerator of `P(2 π₀ a / 2^17)`. -/
def cosCoef (k : ℕ) : ℤ :=
  (-1) ^ k * cosD ^ (24 - 2 * k) * ((Nat.factorial 24 / Nat.factorial (2 * k) : ℕ) : ℤ)

/-- The numerator `N(a) = ∑_{k ≤ 12} cosCoef k A^k`, `A = (3141592653589793 a)^2`, in Horner
form. -/
def cosPolyNum (a : ℤ) : ℤ :=
  (List.map cosCoef (List.range 13)).foldr (fun c acc => c + (3141592653589793 * a) ^ 2 * acc) 0

/-- The denominator `D^{24} 24!` of `P(2 π₀ a / 2^17)`. -/
def cosPolyDen : ℕ := (10 ^ 15 * 2 ^ 16) ^ 24 * Nat.factorial 24

/-- `cosPolyNum a` is the sum `∑_{k ≤ 12} cosCoef k A^k` with `A = (3141592653589793 a)^2`. -/
theorem cosPolyNum_eq (a : ℤ) :
    cosPolyNum a = ∑ k ∈ range 13, cosCoef k * ((3141592653589793 * a) ^ 2) ^ k := by
  simp only [cosPolyNum, List.range_succ, List.range_zero, List.nil_append,
    List.map_cons, List.map_nil, List.cons_append, List.foldr_cons, List.foldr_nil,
    sum_range_succ, sum_range_zero]
  ring

private theorem term_aux (D P a q : ℚ) (hD : D ≠ 0) {k : ℕ} (hk : 2 * k ≤ 24)
    (hq : q * ((2 * k).factorial : ℚ) = (Nat.factorial 24 : ℚ)) :
    (-1) ^ k * D ^ (24 - 2 * k) * q * ((P * a) ^ 2) ^ k / (D ^ 24 * (Nat.factorial 24 : ℚ)) =
      (-1) ^ k * (P * a / D) ^ (2 * k) / ((2 * k).factorial : ℚ) := by
  have hD24 : D ^ 24 = D ^ (24 - 2 * k) * D ^ (2 * k) := by rw [← pow_add]; congr 1; omega
  have hf : ((2 * k).factorial : ℚ) ≠ 0 := by positivity
  have hq0 : q ≠ 0 := fun h => by
    rw [h, zero_mul] at hq
    exact absurd hq.symm (by positivity)
  rw [hD24, ← hq, ← pow_mul, div_pow]
  field_simp

private theorem cosCoef_term {k : ℕ} (hk : k ≤ 12) (a : ℤ) :
    ((cosCoef k * ((3141592653589793 * a) ^ 2) ^ k : ℤ) : ℚ) / cosPolyDen =
      (-1) ^ k * (2 * trCapPi0 * ((a : ℚ) / 2 ^ 17)) ^ (2 * k) / ((2 * k).factorial : ℚ) := by
  have hdvd : (2 * k).factorial ∣ Nat.factorial 24 := Nat.factorial_dvd_factorial (by omega)
  have hq : ((Nat.factorial 24 / (2 * k).factorial : ℕ) : ℚ) * ((2 * k).factorial : ℚ) =
      (Nat.factorial 24 : ℚ) := by exact_mod_cast Nat.div_mul_cancel hdvd
  have hy : 2 * trCapPi0 * ((a : ℚ) / 2 ^ 17) = 3141592653589793 * (a : ℚ) / (cosD : ℚ) := by
    simp only [trCapPi0, cosD]
    push_cast
    ring
  have hden : (cosPolyDen : ℚ) = (cosD : ℚ) ^ 24 * (Nat.factorial 24 : ℚ) := by
    simp only [cosPolyDen, cosD]
    push_cast
    ring
  have hD : (cosD : ℚ) ≠ 0 := by simp only [cosD]; norm_num
  rw [hy, hden, ← term_aux (cosD : ℚ) 3141592653589793 a _ hD (by omega) hq, cosCoef]
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
    Int.cast_ofNat]

/-- The Taylor polynomial at `2 π₀ a / 2^17` is `cosPolyNum a / cosPolyDen`. -/
theorem trCapCosPoly_eq (a : ℤ) :
    trCapCosPoly (2 * trCapPi0 * ((a : ℚ) / 2 ^ 17)) = (cosPolyNum a : ℚ) / cosPolyDen := by
  rw [cosPolyNum_eq, Int.cast_sum, Finset.sum_div, trCapCosPoly]
  refine sum_congr rfl fun k hk => ?_
  rw [cosCoef_term (by simp at hk; omega)]

/-- The numerator of `E_cos = (22/7)^26/26! + 10^{-15}` in lowest terms, as a natural number. -/
def cosErrNumN : ℕ := 5281774316046839986090749787919192243

/-- The numerator of `E_cos` in lowest terms. -/
def cosErrNum : ℤ := cosErrNumN

/-- The denominator of `E_cos` in lowest terms. -/
def cosErrDen : ℕ := 238711186033343105598287195919192243000000000000000

/-- The error term is `E_cos = cosErrNum / cosErrDen`. -/
theorem trCapCosErr_eq' : trCapCosErr = (cosErrNum : ℚ) / cosErrDen := by
  norm_num [trCapCosErr, cosErrNum, cosErrNumN, cosErrDen, Nat.factorial]

/-- The integer `⌈10^{18} (P(2 π₀ a / 2^17) + E_cos)⌉`. -/
def cosNum (a : ℤ) : ℤ :=
  -((-(10 ^ 18 * (cosPolyNum a * cosErrDen + cosErrNum * cosPolyDen))) /
    ((cosPolyDen * cosErrDen : ℕ) : ℤ))

/-- Rounding `P(2 π₀ a / 2^17) + E_cos` up to a multiple of `10^{-18}` gives
`cosNum a / 10^{18}`. -/
theorem trCapRoundUp_cosPoly (a : ℤ) :
    trCapRoundUp (1 / 10 ^ 18) (trCapCosPoly (2 * trCapPi0 * ((a : ℚ) / 2 ^ 17)) + trCapCosErr) =
      (cosNum a : ℚ) / 10 ^ 18 := by
  rw [trCapRoundUp_of_pos (by norm_num), trCapCosPoly_eq, trCapCosErr_eq']
  have hP : (cosPolyDen : ℚ) ≠ 0 := by unfold cosPolyDen; positivity
  have hE : (cosErrDen : ℚ) ≠ 0 := by unfold cosErrDen; positivity
  have h : ((cosPolyNum a : ℚ) / cosPolyDen + (cosErrNum : ℚ) / cosErrDen) / (1 / 10 ^ 18) =
      ((10 ^ 18 * (cosPolyNum a * cosErrDen + cosErrNum * cosPolyDen) : ℤ) : ℚ) /
        ((cosPolyDen * cosErrDen : ℕ) : ℚ) := by
    push_cast
    field_simp
    norm_num
  rw [h, Rat.ceil_intCast_div_natCast, cosNum]
  push_cast
  ring

/-! ### The cosine bound at `n / 2^17` -/

/-- The cosine bound at `n / 2^17` in units of `10^{-18}`: `10^{18}` if `2^17 ∣ n`, and
otherwise `cosNum a` with `a = r` or `a = 2^17 - r` for `r = n mod 2^17`, whichever is at most
`2^16`. -/
def cosI (n : ℤ) : ℤ :=
  if n % 2 ^ 17 = 0 then 10 ^ 18
  else cosNum (if n % 2 ^ 17 ≤ 2 ^ 16 then n % 2 ^ 17 else 2 ^ 17 - n % 2 ^ 17)

/-- The Taylor polynomial `P` is even. -/
theorem trCapCosPoly_neg (y : ℚ) : trCapCosPoly (-y) = trCapCosPoly y := by
  unfold trCapCosPoly
  refine sum_congr rfl fun k _ => ?_
  rw [pow_mul, neg_sq, ← pow_mul]

/-- The rounded cosine bound at `n / 2^17` is `cosI n / 10^{18}`. -/
theorem trCapCosBound_eq_cosI (n : ℤ) :
    trCapCosBound (1 / 10 ^ 18) ((n : ℚ) / 2 ^ 17) = (cosI n : ℚ) / 10 ^ 18 := by
  set r := n % 2 ^ 17 with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by norm_num)
  have hr1 : r < 2 ^ 17 := Int.emod_lt_of_pos _ (by norm_num)
  have hn : (n : ℚ) / 2 ^ 17 = (r : ℚ) / 2 ^ 17 + ((n / 2 ^ 17 : ℤ) : ℚ) := by
    have h : n = r + 2 ^ 17 * (n / 2 ^ 17) := by omega
    have h' : (n : ℚ) = r + 2 ^ 17 * ((n / 2 ^ 17 : ℤ) : ℚ) := by exact_mod_cast h
    rw [h']
    field_simp
  rw [hn, trCapCosBound_add_intCast, cosI, ← hr]
  have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast hr0
  have hr1' : (r : ℚ) < 2 ^ 17 := by exact_mod_cast hr1
  split_ifs with h0 h1
  · rw [h0, Int.cast_zero, zero_div, show (0 : ℚ) = ((0 : ℤ) : ℚ) by simp,
      trCapCosBound_intCast]
    norm_num
  · have hpos : (0 : ℚ) < r := by exact_mod_cast lt_of_le_of_ne hr0 (Ne.symm h0)
    have hfr : Int.fract ((r : ℚ) / 2 ^ 17) = (r : ℚ) / 2 ^ 17 :=
      Int.fract_eq_self.2 ⟨by positivity, by rw [div_lt_one (by norm_num)]; exact hr1'⟩
    have hfr0 : Int.fract ((r : ℚ) / 2 ^ 17) ≠ 0 := by rw [hfr]; positivity
    rw [trCapCosBound_of_fract_ne_zero hfr0, ← trCapRoundUp_cosPoly]
    rcases lt_or_eq_of_le h1 with h1 | h1
    · have hround : round ((r : ℚ) / 2 ^ 17) = 0 := by
        rw [round_eq, Int.floor_eq_iff]
        have : (r : ℚ) < 2 ^ 16 := by exact_mod_cast h1
        push_cast
        rw [show (r : ℚ) / 2 ^ 17 + 1 / 2 = (r + 2 ^ 16) / 2 ^ 17 by ring,
          le_div_iff₀ (by norm_num), div_lt_iff₀ (by norm_num)]
        constructor <;> linarith
      rw [hround]
      simp
    · have hround : round ((r : ℚ) / 2 ^ 17) = 1 := by
        rw [round_eq, Int.floor_eq_iff, h1]
        norm_num
      rw [hround, h1, ← trCapCosPoly_neg]
      congr 3
      push_cast
      ring
  · have hpos : (0 : ℚ) < r := by exact_mod_cast lt_of_le_of_ne hr0 (Ne.symm h0)
    have hfr : Int.fract ((r : ℚ) / 2 ^ 17) = (r : ℚ) / 2 ^ 17 :=
      Int.fract_eq_self.2 ⟨by positivity, by rw [div_lt_one (by norm_num)]; exact hr1'⟩
    have hfr0 : Int.fract ((r : ℚ) / 2 ^ 17) ≠ 0 := by rw [hfr]; positivity
    rw [trCapCosBound_of_fract_ne_zero hfr0, ← trCapRoundUp_cosPoly]
    have hround : round ((r : ℚ) / 2 ^ 17) = 1 := by
      rw [round_eq, Int.floor_eq_iff]
      have : (2 ^ 16 : ℚ) < r := by exact_mod_cast not_le.1 h1
      push_cast
      rw [show (r : ℚ) / 2 ^ 17 + 1 / 2 = (r + 2 ^ 16) / 2 ^ 17 by ring,
        le_div_iff₀ (by norm_num), div_lt_iff₀ (by norm_num)]
      constructor <;> linarith
    rw [hround, ← trCapCosPoly_neg]
    congr 3
    push_cast
    ring

/-- `cosI` is `2^17`-periodic. -/
theorem cosI_add_mul (n k : ℤ) : cosI (n + 2 ^ 17 * k) = cosI n := by
  simp only [cosI, Int.add_mul_emod_self_left]

/-- `cosI` is even. -/
theorem cosI_neg (n : ℤ) : cosI (-n) = cosI n := by
  unfold cosI
  have h : (-n) % 2 ^ 17 = if n % 2 ^ 17 = 0 then 0 else 2 ^ 17 - n % 2 ^ 17 := by omega
  rw [h]
  split_ifs with h0 h1 h2 h3 h4 <;> first | rfl | omega | skip
  all_goals congr 1; omega

/-- `cosI n` depends only on `n mod 2^17`. -/
theorem cosI_of_emod_eq {n n' : ℤ} (h : n % 2 ^ 17 = n' % 2 ^ 17) : cosI n = cosI n' := by
  simp only [cosI, h]

/-- For `v ≥ 17`, `cosI (2^v X) = 10^{18}`. -/
theorem cosI_mul_two_pow {v : ℕ} (hv : 17 ≤ v) (X : ℤ) : cosI (2 ^ v * X) = 10 ^ 18 := by
  have : (2 ^ v * X) % 2 ^ 17 = 0 := by
    rw [show (2 : ℤ) ^ v = 2 ^ 17 * 2 ^ (v - 17) by rw [← pow_add]; congr 1; omega, mul_assoc]
    exact Int.mul_emod_right _ _
  rw [cosI, ite_eq_left_iff.2 (fun h => absurd this h)]

/-! ### The multipliers `2^m - 1` -/

/-- The exponent `f_m` with `2^m - 1 ≡ ± 3^{f_m} (mod 2^17)`, for `1 ≤ m ≤ 14`. -/
def mulExp (m : ℕ) : ℕ :=
  [0, 0, 1, 1198, 15628, 11480, 1200, 13664, 6848, 30080, 27392, 22016, 11264, 22528, 12288].getD
    m 0

/-- For `1 ≤ m ≤ 14`, `2^m - 1 ≡ ± 3^{f_m} (mod 2^17)` with `f_m = mulExp m`. -/
theorem mulExp_spec : ∀ m ∈ Finset.Icc 1 14,
    (((2 : ℤ) ^ m - 1 - 3 ^ mulExp m) % 2 ^ 17 = 0 ∨
      ((2 : ℤ) ^ m - 1 + 3 ^ mulExp m) % 2 ^ 17 = 0) := by
  decide +kernel

/-- For `1 ≤ m ≤ 14`, `cosI ((2^m - 1) X) = cosI (3^{f_m} X)` with `f_m = mulExp m`. -/
theorem cosI_mul_pow_two_sub_one {m : ℕ} (hm : m ∈ Finset.Icc 1 14) (X : ℤ) :
    cosI ((2 ^ m - 1) * X) = cosI (3 ^ mulExp m * X) := by
  rcases mulExp_spec m hm with h | h
  · apply cosI_of_emod_eq
    have hd : (2 : ℤ) ^ 17 ∣ (2 ^ m - 1) * X - 3 ^ mulExp m * X := by
      rw [← sub_mul]; exact dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero h) _
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd hd)
  · rw [← cosI_neg (3 ^ mulExp m * X)]
    apply cosI_of_emod_eq
    have hd : (2 : ℤ) ^ 17 ∣ (2 ^ m - 1) * X - -(3 ^ mulExp m * X) := by
      rw [sub_neg_eq_add, ← add_mul]; exact dvd_mul_of_dvd_left (Int.dvd_of_emod_eq_zero h) _
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.2 (Int.emod_eq_zero_of_dvd hd)

/-! ### Evaluation in natural numbers -/

/-- The absolute value `D^{24 - 2k} 24! / (2k)!` of `cosCoef k`. -/
def cosCoefN (k : ℕ) : ℕ :=
  (10 ^ 15 * 2 ^ 16) ^ (24 - 2 * k) * (Nat.factorial 24 / Nat.factorial (2 * k))

/-- `cosCoef k = (-1)^k cosCoefN k`. -/
theorem cosCoef_eq (k : ℕ) : cosCoef k = (-1) ^ k * (cosCoefN k : ℤ) := by
  simp only [cosCoef, cosCoefN, cosD, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  ring

/-- The denominator `D^{24} 24! · (7^{26} 26! 10^{15})` of the cosine bound. -/
def cosY : ℕ := cosPolyDen * cosErrDen

/-- The coefficient of `B^i`, `B = A^2`, in the positive part of the numerator. -/
def cosCp (i : ℕ) : ℕ := 10 ^ 18 * cosErrDen * cosCoefN (2 * i)

/-- The coefficient of `A B^i`, `B = A^2`, in the negative part of the numerator. -/
def cosCn (i : ℕ) : ℕ := 10 ^ 18 * cosErrDen * cosCoefN (2 * i + 1)

/-- The positive part of `10^{18} (N(a) E_d + E_n D^{24} 24!) + 10^{18} cosY`, where
`E_cos = E_n / E_d`. -/
def cosXp (a : ℕ) : ℕ :=
  let B := ((3141592653589793 * a) ^ 2) ^ 2
  ((((((cosCp 6 * B + cosCp 5) * B + cosCp 4) * B + cosCp 3) * B + cosCp 2) * B + cosCp 1) * B +
      cosCp 0) + 10 ^ 18 * (cosErrNumN * cosPolyDen + cosY)

/-- The negative part of `10^{18} (N(a) E_d + E_n D^{24} 24!)`. -/
def cosXn (a : ℕ) : ℕ :=
  let A := (3141592653589793 * a) ^ 2
  let B := A ^ 2
  A * (((((cosCn 5 * B + cosCn 4) * B + cosCn 3) * B + cosCn 2) * B + cosCn 1) * B + cosCn 0)

/-- The integer `cosNum a + 10^{18}`, computed in natural numbers. -/
def cosLaneVal (a : ℕ) : ℕ := (cosXp a - cosXn a + cosY - 1) / cosY

/-- `cosXp a - cosXn a = 10^{18} (N(a) E_d + E_n D^{24} 24!) + 10^{18} cosY` in the integers,
where `E_cos = E_n / E_d`. -/
theorem cosXp_sub_cosXn (a : ℕ) :
    (cosXp a : ℤ) - cosXn a =
      10 ^ 18 * (cosPolyNum a * cosErrDen + cosErrNum * cosPolyDen) + 10 ^ 18 * cosY := by
  simp only [cosXp, cosXn, cosCp, cosCn, cosY, cosErrNum, cosPolyNum_eq, cosCoef_eq,
    sum_range_succ, sum_range_zero]
  push_cast
  ring

/-- The denominator `cosY` is positive. -/
theorem cosY_pos : 0 < cosY := by unfold cosY cosPolyDen cosErrDen; positivity

/-- If `cosXn a ≤ cosXp a`, then `cosLaneVal a = cosNum a + 10^{18}`. -/
theorem cosLaneVal_eq {a : ℕ} (h : cosXn a ≤ cosXp a) :
    (cosLaneVal a : ℤ) = cosNum a + 10 ^ 18 := by
  have hZ := cosXp_sub_cosXn a
  have hc : ((cosXp a - cosXn a : ℕ) : ℤ) =
      10 ^ 18 * (cosPolyNum a * cosErrDen + cosErrNum * cosPolyDen) + 10 ^ 18 * cosY := by
    rw [Nat.cast_sub h, hZ]
  rw [cosLaneVal, ceilDiv_cast _ _ cosY_pos, hc, cosNum]
  have hY : ((cosY : ℕ) : ℤ) ≠ 0 := by exact_mod_cast cosY_pos.ne'
  rw [show -(10 ^ 18 * ((cosPolyNum a : ℤ) * cosErrDen + cosErrNum * cosPolyDen) + 10 ^ 18 * cosY) =
      -(10 ^ 18 * ((cosPolyNum a : ℤ) * cosErrDen + cosErrNum * cosPolyDen)) +
        (-10 ^ 18) * ((cosY : ℕ) : ℤ) by ring, Int.add_mul_ediv_right _ _ hY]
  simp only [cosY]
  ring

/-- The cosine bound at a residue `r`, in units of `10^{-18}` and shifted by `10^{18}`. -/
def cosExpect (r : ℕ) : ℕ :=
  if r = 0 then 2 * 10 ^ 18 else cosLaneVal (if r ≤ 2 ^ 16 then r else 2 ^ 17 - r)

/-- The side condition `cosXn a ≤ cosXp a` under which `cosExpect r` is exact. -/
def cosExpectOK (r : ℕ) : Bool :=
  r == 0 || (let a := if r ≤ 2 ^ 16 then r else 2 ^ 17 - r; Nat.ble (cosXn a) (cosXp a))

/-- For `r < 2^17` with `cosExpectOK r`, `cosExpect r = cosI r + 10^{18}`. -/
theorem cosExpect_eq {r : ℕ} (hr : r < 2 ^ 17) (h : cosExpectOK r = true) :
    (cosExpect r : ℤ) = cosI r + 10 ^ 18 := by
  have hmod : (r : ℤ) % 2 ^ 17 = r := Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hr)
  unfold cosExpect cosI
  rw [hmod]
  by_cases h0 : r = 0
  · subst h0; norm_num
  · have h0' : (r : ℤ) ≠ 0 := by exact_mod_cast h0
    rw [ite_eq_right h0, ite_eq_right h0']
    simp only [cosExpectOK, Bool.or_eq_true, beq_iff_eq, h0, false_or] at h
    split_ifs at h ⊢ with h1 h2 h2
    all_goals replace h := Nat.le_of_ble_eq_true h
    · exact cosLaneVal_eq h
    · exact absurd (by exact_mod_cast h1) h2
    · exact absurd (by exact_mod_cast h2) h1
    · rw [cosLaneVal_eq h]
      congr 2
      omega

end C3H17Values

end CollatzPosDens
