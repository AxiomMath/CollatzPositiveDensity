/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass
public import CollatzPosDens.Maps.Offset
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Mixing.MxLevel
public import CollatzPosDens.Mixing.MxLevelNonneg
public import CollatzPosDens.Mixing.MxLog2Bounds
public import CollatzPosDens.Mixing.MxCrossingOffsetTail
public import CollatzPosDens.Mixing.MxJointSum

/-!
# Large cleared offsets at the crossing are rare

For every integer `n ≥ 2^80000`, the words `w ∈ ℤ_{≥1}^n` for which some `1 ≤ i ≤ n` has
`A(w_{≤ i-1}) ≤ Lv_n < A(w_{≤ i})` and `2^{A(w_{≤ i})} off(w_{≤ i}) ≥ 3^n` have geometric mass
at most `(4/5) n^{-3/2}`.

## Main results

* `CollatzPosDens.geomMass_productTail_le`: the bound.

## Implementation notes

The product condition is an inequality in `ℚ`, where the offset lives, as in the good set
`Gd_n`; the bound `(4/5) n^{-3/2}` is the real number embedded by `ENNReal.ofReal`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- Appending one letter to a prefix adds one term to the offset:
`off(w_{≤ k+1}) = off(w_{≤ k}) + 3^k 2^{-A(w_{≤ k+1})}` for `k < |w|`. -/
theorem off_take_succ (w : Word) {k : ℕ} (hk : k < w.length) :
    off (w.take (k + 1)) = off (w.take k) + 3 ^ k / 2 ^ Word.valSum (w.take (k + 1)) := by
  rw [List.take_succ_eq_append_getElem hk, off_append, Word.valSum_append,
    Word.valSum_singleton, Word.weight, List.length_take_of_le hk.le]
  simp only [off_cons, off_nil]
  rw [pow_add]
  field_simp
  ring

/-- The numerical inequality `(35/8)((6145/4096) L + 2) ≤ 2^{L/4096}` for `L ≥ 80000`. Its
core is `(35/8)(80000 · 6145/4096 + 3) < 2^{625/32}`, equivalent to the integer inequality
`(35 · 491612288)^32 < 2^1105`. -/
theorem thirtyFive_div_eight_mul_le_two_rpow {L : ℝ} (hL : 80000 ≤ L) :
    35 / 8 * (6145 / 4096 * L + 2) ≤ (2 : ℝ) ^ (L / 4096) := by
  set x := L / 4096 - 625 / 32 with hx
  have hx0 : 0 ≤ x := by linarith
  have hsplit : (2 : ℝ) ^ (L / 4096) = 2 ^ (625 / 32 : ℝ) * 2 ^ x := by
    rw [← Real.rpow_add (by norm_num), hx]
    congr 1
    ring
  have hexp : 1 + x * Real.log 2 ≤ (2 : ℝ) ^ x := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
    linarith [Real.add_one_le_exp (Real.log 2 * x)]
  have hK : (35 * 491612288 / 32768 : ℝ) < 2 ^ (625 / 32 : ℝ) := by
    by_contra h
    have h32 := pow_le_pow_left₀ (by positivity) (not_lt.mp h) 32
    rw [← Real.rpow_mul_natCast (by norm_num),
      show (625 / 32 * ((32 : ℕ) : ℝ) : ℝ) = ((625 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast] at h32
    set_option exponentiation.threshold 1200 in norm_num at h32
  have hlog := log_two_bounds.1
  rw [hsplit]
  have hxl : 0 ≤ x * Real.log 2 := mul_nonneg hx0 (by linarith)
  have hL' : L = 4096 * (x + 625 / 32) := by rw [hx]; ring
  rw [hL']
  nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 2 ^ (625 / 32 : ℝ)),
    mul_le_mul_of_nonneg_right hK.le hxl, mul_le_mul_of_nonneg_left hlog.le hx0]

/-- The level satisfies `2^{Lv_n} = 3^n / (4 n^{6145/4096})`. -/
theorem two_rpow_mxLevel {n : ℕ} (hn : (0 : ℝ) < n) :
    (2 : ℝ) ^ mxLevel n = 3 ^ n / (4 * (n : ℝ) ^ (6145 / 4096 : ℝ)) := by
  rw [mxLevel_def, Real.rpow_sub (by norm_num), Real.rpow_sub (by norm_num),
    mul_comm (n : ℝ), Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num)
      (by norm_num), Real.rpow_natCast, mul_comm (6145 / 4096 : ℝ),
    Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hn]
  norm_num
  rw [div_div, mul_comm]

/-- If `2^V = 3^n / (4R)`, then a word crossing `V` at `i` with `2^{A(w_{≤ i})} off(w_{≤ i}) ≥ 3^n`
satisfies `R ≤ 2^{A(w_{≤ i}) - ⌊V⌋ - 1} off(w_{≤ i-1})`. -/
theorem productTail_subset_crossingOffsetTail {n : ℕ} {V R : ℝ} (hR : 0 < R)
    (h2V : (2 : ℝ) ^ V = 3 ^ n / (4 * R)) :
    {w : Word | w.length = n ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
        (Word.valSum (w.take (i - 1)) : ℝ) ≤ V ∧ V < (Word.valSum (w.take i) : ℝ) ∧
        (3 : ℚ) ^ n ≤ (2 : ℚ) ^ Word.valSum (w.take i) * off (w.take i)} ⊆
      {w : Word | w.length = n ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
        (Word.valSum (w.take (i - 1)) : ℝ) ≤ V ∧ V < (Word.valSum (w.take i) : ℝ) ∧
        R ≤ (2 : ℝ) ^ ((Word.valSum (w.take i) : ℤ) - ⌊V⌋ - 1) *
          (off (w.take (i - 1)) : ℝ)} := by
  rintro w ⟨hw, i, hi1, hin, h1, h2, h3⟩
  refine ⟨hw, i, hi1, hin, h1, h2, ?_⟩
  set S := Word.valSum (w.take i)
  have hoff := off_take_succ w (k := i - 1) (by omega)
  rw [show i - 1 + 1 = i by omega] at hoff
  have h3' : (3 : ℝ) ^ n ≤ (2 : ℝ) ^ S * (off (w.take i) : ℝ) := by exact_mod_cast h3
  rw [hoff] at h3'
  push_cast at h3'
  have h2S : (0 : ℝ) < 2 ^ S := by positivity
  have hkey : (2 : ℝ) ^ S * (off (w.take (i - 1)) : ℝ) ≥ 3 ^ n - 3 ^ (i - 1) := by
    have : (2 : ℝ) ^ S * ((3 : ℝ) ^ (i - 1) / 2 ^ S) = 3 ^ (i - 1) := by field_simp
    nlinarith
  have h3pow : (3 : ℝ) ^ (i - 1) ≤ 3 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h3n : (3 : ℝ) ^ n = 3 * 3 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hfl : (2 : ℝ) ^ (⌊V⌋ + 1 : ℤ) ≤ 3 ^ n / (2 * R) := by
    rw [← Real.rpow_intCast]
    calc (2 : ℝ) ^ (((⌊V⌋ + 1 : ℤ)) : ℝ) ≤ 2 ^ (V + 1) := by
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
          push_cast
          linarith [Int.floor_le V]
      _ = 3 ^ n / (2 * R) := by
          rw [Real.rpow_add (by norm_num), h2V, Real.rpow_one]
          field_simp
          ring
  have hzpow : (2 : ℝ) ^ ((S : ℤ) - ⌊V⌋ - 1) = 2 ^ S / 2 ^ (⌊V⌋ + 1 : ℤ) := by
    rw [show (S : ℤ) - ⌊V⌋ - 1 = (S : ℤ) - (⌊V⌋ + 1) by ring, zpow_sub₀ (by norm_num),
      zpow_natCast]
  have hpos : (0 : ℝ) < 2 ^ (⌊V⌋ + 1 : ℤ) := by positivity
  rw [hzpow, div_mul_eq_mul_div, le_div_iff₀ hpos]
  have hRfl : R * 2 ^ (⌊V⌋ + 1 : ℤ) ≤ 3 ^ n / 2 := by
    calc R * 2 ^ (⌊V⌋ + 1 : ℤ) ≤ R * (3 ^ n / (2 * R)) :=
          mul_le_mul_of_nonneg_left hfl hR.le
      _ = 3 ^ n / 2 := by field_simp
  have : (0 : ℝ) ≤ 3 ^ (n - 1) := by positivity
  nlinarith

/-- For `n ≥ 2^80000` and `R = n^{6145/4096}`, `(7 / (2R)) (log₂ R + 2) ≤ (4/5) n^{-3/2}`. -/
theorem seven_div_mul_logb_add_two_le {n : ℕ} (hn : 2 ^ 80000 ≤ n) :
    7 / (2 * (n : ℝ) ^ (6145 / 4096 : ℝ)) * (Real.logb 2 ((n : ℝ) ^ (6145 / 4096 : ℝ)) + 2) ≤
      4 / 5 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast lt_of_lt_of_le (by positivity) hn
  set L := Real.logb 2 (n : ℝ) with hLdef
  set R : ℝ := (n : ℝ) ^ (6145 / 4096 : ℝ) with hRdef
  have hL : 80000 ≤ L := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity)
      (by exact_mod_cast hn : ((2 ^ 80000 : ℕ) : ℝ) ≤ n)
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow] at this
    rwa [Real.logb_self_eq_one (by norm_num), mul_one] at this
  have hQ : (n : ℝ) ^ (1 / 4096 : ℝ) = 2 ^ (L / 4096) := by
    rw [hLdef, div_eq_mul_one_div (Real.logb 2 _), Real.rpow_mul (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) hnpos]
  have hRsplit : R = (n : ℝ) ^ (3 / 2 : ℝ) * (n : ℝ) ^ (1 / 4096 : ℝ) := by
    rw [hRdef, ← Real.rpow_add hnpos]
    norm_num
  have hlogR : Real.logb 2 R = 6145 / 4096 * L := by
    rw [hRdef, Real.logb_rpow_eq_mul_logb_of_pos hnpos]
  have hkey := thirtyFive_div_eight_mul_le_two_rpow hL
  rw [← hQ] at hkey
  rw [hlogR, hRsplit, Real.rpow_neg hnpos.le, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have : 4 / 5 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ * (2 * ((n : ℝ) ^ (3 / 2 : ℝ) *
      (n : ℝ) ^ (1 / 4096 : ℝ))) = 8 / 5 * (n : ℝ) ^ (1 / 4096 : ℝ) := by
    field_simp
    ring
  rw [this]
  linarith

/-- **Large cleared offsets at the crossing are rare.** For every integer `n ≥ 2^80000`, the
words of length `n` crossing `Lv_n` at some index `i` with `2^{A(w_{≤ i})} off(w_{≤ i}) ≥ 3^n`
have geometric mass at most `(4/5) n^{-3/2}`. -/
@[collatz_pos_dens "lem_mx_product_tail"]
theorem geomMass_productTail_le {n : ℕ} (hn : 2 ^ 80000 ≤ n) :
    geomMass {w : Word | w.length = n ∧ ∃ i : ℕ, 1 ≤ i ∧ i ≤ n ∧
        (Word.valSum (w.take (i - 1)) : ℝ) ≤ mxLevel n ∧
        mxLevel n < (Word.valSum (w.take i) : ℝ) ∧
        (3 : ℚ) ^ n ≤ (2 : ℚ) ^ Word.valSum (w.take i) * off (w.take i)} ≤
      ENNReal.ofReal (4 / 5 * (n : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have hn2 : 2 ≤ n := le_trans (Nat.le_self_pow (by norm_num) 2) hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hV : 0 ≤ mxLevel n := le_trans (by positivity) (seven_div_ten_mul_le_mxLevel hn)
  set R : ℝ := (n : ℝ) ^ (6145 / 4096 : ℝ) with hRdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos hnpos _
  have hR2 : 2 ≤ R := by
    have : (n : ℝ) ^ (1 : ℝ) ≤ R := Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
    rw [Real.rpow_one] at this
    exact le_trans (by exact_mod_cast hn2) this
  have hterm : ∀ r : ℕ, (2 : ℝ)⁻¹ ^ (r + 1) * (7 / (R * (2 : ℝ)⁻¹ ^ r + 2)) =
      7 / (2 * R + 2 ^ (r + 2)) := by
    intro r
    rw [inv_pow, inv_pow, pow_succ, pow_add]
    field_simp
  obtain ⟨hsum, hle⟩ := jointSum_le hR2
  calc _ ≤ _ :=
        geomMass_mono (productTail_subset_crossingOffsetTail hRpos (two_rpow_mxLevel hnpos))
    _ ≤ ∑' r : ℕ, ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (r + 1) * (7 / (R * (2 : ℝ)⁻¹ ^ r + 2))) :=
        geomMass_crossingOffsetTail_le hV hRpos
    _ = ENNReal.ofReal (∑' r : ℕ, 7 / (2 * R + 2 ^ (r + 2))) := by
        simp_rw [hterm]
        rw [ENNReal.ofReal_tsum_of_nonneg (fun r => by positivity) hsum]
    _ ≤ ENNReal.ofReal (7 / (2 * R) * (Real.logb 2 R + 2)) := ENNReal.ofReal_le_ofReal hle
    _ ≤ _ := ENNReal.ofReal_le_ofReal (seven_div_mul_logb_add_two_le hn)

end CollatzPosDens
