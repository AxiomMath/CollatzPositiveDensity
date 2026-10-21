/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Transfer.Pstar
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02Epiece
public import CollatzPosDens.Transfer.S02H
public import CollatzPosDens.Transfer.S02K
public import CollatzPosDens.Transfer.S02PBits
public import CollatzPosDens.Transfer.S02S
public import CollatzPosDens.Transfer.S02ClearCount
public import CollatzPosDens.Transfer.S02ClearExp
public import CollatzPosDens.Transfer.S02HSchedule
public import CollatzPosDens.Transfer.S02ScheduleValues

/-!
# The value of the clearing allowance `E_piece`

For the two Fourier indices the clearing allowance is the rational number
$$E_{\mathrm{piece}}(\mathrm o) = \frac{25092942460067403877}{10^{24}}, \qquad
  E_{\mathrm{piece}}(\mathrm b) = \frac{12788}{10^{24}} .$$

Fix `ι` and suppress it. Every ingredient of `E_piece` is an explicit integer or rational: with
the schedule positions `p_0, …, p_{r_*}`, `h_*(p_i) = ⌈α_sc S_i⌉ + H_*` and
`P_* = p_{r_*} + 1`, one finds `p_i + h_*(p_i) + 1 ≤ P_*` for `i < r_*`, so that
`n^cl_0 = p_0 + 1` and `n^cl_i = p_i - p_{i-1}` for `1 ≤ i < r_*`, while
`P_* ≤ a_{r_*} + h_*(p_{r_*})`, so that `n^cl_{r_*} = 0`. Every clearing exponent has the form
`t^cl_i = a_i / d` with `a_i ∈ ℕ`: `a_i = 11511 h_*(p_i) - 1300 S_i` and `d = 7372800` at
`ι = o`, `a_i = 225 h_*(p_i) - 26 S_i` and `d = 4608` at `ι = b`.

* For the exactly evaluated blocks (`i = 0, 1` at `ι = o`, `i = 0` at `ι = b`) the ceiling
  `⌈10^24 n^cl_i / P_80(t^cl_i)⌉` is computed exactly. Writing `t = a / d`, the number
  `Q_80(a, d) := d^80 · 80! · P_80(a / d)` is a natural number, given by the recursion
  `Q_0 = 1`, `Q_{n+1} = (n + 1) d Q_n + a^{n+1}`, and the ceiling equals `c + 1` as soon as
  `c Q_80 < 10^24 n^cl_i d^80 80! ≤ (c + 1) Q_80`, an inequality of natural numbers.
  The ceilings are `25092769474872960485`, `172985194443384` at `ι = o` and `12786` at `ι = b`.
* For the remaining blocks `i < r_*` the single term `t^j / j!` of `P_80` gives
  `P_80(t^cl_i) ≥ L^j / j! ≥ 10^24 n^cl_i` with `(L, j) = (2627, 20)` at `ι = o` and
  `(L, j) = (925, 20)` at `ι = b`, so the ceiling is `1`.
* For `i = r_*` the ceiling is `0`.

## Main results

* `CollatzPosDens.ePiece_o`: `E_piece(o) = 25092942460067403877 / 10^24`.
* `CollatzPosDens.ePiece_b`: `E_piece(b) = 12788 / 10^24`.
* `CollatzPosDens.pow_div_factorial_le_expPartialSum`: for `0 ≤ t` and `j ≤ n`,
  `t^j / j! ≤ ∑_{k=0}^{n} t^k / k!`.

## Implementation notes

The exact ceilings are checked by comparing natural numbers only: the scaled partial sum
`Q_80(a, d)` is computed by a recursion in `ℕ`, so no rational arithmetic is evaluated by the
kernel. For the other blocks only one term of `P_80` is used, so the huge exponents `t^cl_i` are
never raised to a power beyond a fixed lower bound.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- For `0 ≤ t` and `j ≤ n`, the single term `t^j / j!` is at most the partial sum
`∑_{k=0}^{n} t^k / k!`. -/
theorem pow_div_factorial_le_expPartialSum {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {n j : ℕ} (hj : j ≤ n) {t : K} (ht : 0 ≤ t) :
    t ^ j / (j.factorial : K) ≤ expPartialSum n t := by
  rw [expPartialSum]
  exact single_le_sum (f := fun k => t ^ k / (k.factorial : K))
    (fun k _ => div_nonneg (pow_nonneg ht _) (Nat.cast_nonneg _))
    (mem_range.mpr (Nat.lt_succ_of_le hj))

/-- The scaled partial sum `Q_n(a, d) = d^n · n! · P_n(a / d)` of the exponential series, by the
recursion `Q_0 = 1`, `Q_{n+1} = (n + 1) d Q_n + a^{n+1}` in `ℕ`. -/
private noncomputable def ePieceValue_expNum (a d n : ℕ) : ℕ :=
  Nat.rec 1 (fun k q => (k + 1) * d * q + a ^ (k + 1)) n

/-- `Q_n(a, d) = d^n · n! · P_n(a / d)` for `d ≠ 0`. -/
private lemma ePieceValue_expNum_cast {a d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    (ePieceValue_expNum a d n : ℚ) =
      (d : ℚ) ^ n * (n.factorial : ℚ) * expPartialSum n ((a : ℚ) / d) := by
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  induction n with
  | zero => simp [ePieceValue_expNum]
  | succ n ih =>
    have h : ePieceValue_expNum a d (n + 1) =
        (n + 1) * d * ePieceValue_expNum a d n + a ^ (n + 1) := rfl
    have hf : ((n : ℚ) + 1) * n.factorial ≠ 0 := by positivity
    have hx : (d : ℚ) ^ (n + 1) * ((a : ℚ) / d) ^ (n + 1) = (a : ℚ) ^ (n + 1) := by
      rw [← mul_pow, mul_div_cancel₀ _ hd']
    rw [h, expPartialSum_succ, Nat.factorial_succ]
    push_cast
    rw [ih, mul_add, mul_div_assoc', mul_div_right_comm, mul_div_assoc, div_self hf, mul_one,
      mul_right_comm, hx]
    ring

/-- An exact ceiling: if `t = a / d` with `0 < d`, and `c Q_80 < 10^24 m d^80 80! ≤ (c + 1) Q_80`
in `ℕ`, then `⌈10^24 m / P_80(t)⌉ = c + 1`. -/
private lemma ePieceValue_ceil_exact {m a d c : ℕ} (hd : 0 < d) {t : ℚ} (ht : t = a / d)
    (h : c * ePieceValue_expNum a d 80 < 10 ^ 24 * m * (d ^ 80 * Nat.factorial 80) ∧
      10 ^ 24 * m * (d ^ 80 * Nat.factorial 80) ≤ (c + 1) * ePieceValue_expNum a d 80) :
    ⌈10 ^ 24 * (m : ℚ) / expPartialSum 80 t⌉ = (c : ℤ) + 1 := by
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hP := expPartialSum_pos 80 ht0
  have hQ := ePieceValue_expNum_cast (a := a) hd.ne' 80
  rw [← ht] at hQ
  have hD : (0 : ℚ) < (d : ℚ) ^ 80 * (Nat.factorial 80 : ℚ) := by positivity
  obtain ⟨h1, h2⟩ := h
  have h1' : (c : ℚ) * ePieceValue_expNum a d 80 <
      10 ^ 24 * m * ((d : ℚ) ^ 80 * (Nat.factorial 80 : ℚ)) := by exact_mod_cast h1
  have h2' : 10 ^ 24 * m * ((d : ℚ) ^ 80 * (Nat.factorial 80 : ℚ)) ≤
      ((c : ℚ) + 1) * ePieceValue_expNum a d 80 := by exact_mod_cast h2
  rw [hQ] at h1' h2'
  rw [Int.ceil_eq_iff]
  push_cast
  constructor
  · rw [add_sub_cancel_right, lt_div_iff₀ hP]
    nlinarith
  · rw [div_le_iff₀ hP]
    nlinarith

/-- A clearing count `n` damped by an exponent `t ≥ L` contributes a ceiling `1` as soon as
`0 < n`, `j ≤ 80` and `10^24 n · j! ≤ L^j`. -/
private lemma ePieceValue_ceil_eq_one {n L j : ℕ} {t : ℚ} (hn : 0 < n) (ht : (L : ℚ) ≤ t)
    (hj : j ≤ 80) (hb : 10 ^ 24 * n * Nat.factorial j ≤ L ^ j) :
    ⌈10 ^ 24 * (n : ℚ) / expPartialSum 80 t⌉ = 1 := by
  have ht0 : (0 : ℚ) ≤ t := (Nat.cast_nonneg L).trans ht
  have hP := expPartialSum_pos 80 ht0
  have h1 := pow_div_factorial_le_expPartialSum (n := 80) hj ht0
  have h2 : (L : ℚ) ^ j ≤ t ^ j := pow_le_pow_left₀ (Nat.cast_nonneg L) ht j
  have hb' : (10 : ℚ) ^ 24 * n * (Nat.factorial j : ℚ) ≤ (L : ℚ) ^ j := by exact_mod_cast hb
  have hf : (0 : ℚ) < Nat.factorial j := by positivity
  rw [Int.ceil_eq_iff]
  refine ⟨by norm_num; positivity, ?_⟩
  rw [div_le_iff₀ hP]
  push_cast
  have : (10 : ℚ) ^ 24 * n ≤ t ^ j / (Nat.factorial j : ℚ) := by
    rw [le_div_iff₀ hf]; linarith
  linarith

/-- The middle terms: for `1 ≤ i + 1 < r_*(ι)`, with `p_i = p`, `p_{i+1} = q`,
`h_*(ι, q) = w` and a lower bound `L ≤ t^cl_{i+1}(ι)` satisfying the explicit checks, the
ceiling is `1`. -/
private lemma ePieceValue_term_mid {ι : FIndex} {i p q w L j : ℕ}
    (hp : schedule ι i = p) (hq : schedule ι (i + 1) = q)
    (hw : windowLength ι (schedule ι (i + 1)) = w) (hle : q + w + 1 ≤ pStar ι)
    (hpos : p < q) (hj : j ≤ 80) (hb : 10 ^ 24 * (q - p) * Nat.factorial j ≤ L ^ j)
    (ht : (L : ℚ) ≤ clearingExponent ι (i + 1)) :
    ⌈10 ^ 24 * (clearCount ι (i + 1) : ℚ) /
      expPartialSum 80 (clearingExponent ι (i + 1))⌉ = 1 := by
  rw [clearCount_succ_of_le (by rw [hw, hq]; exact hle), hq, hp]
  exact ePieceValue_ceil_eq_one (by omega) ht hj hb

/-! ### The index `o` -/

/-- The window length at a schedule position of the index `o` with known position and size
factor. -/
private lemma ePieceValue_windowLength_o {i p k : ℕ} (hi : i ≤ rStar .o)
    (hp : schedule .o i = p) (hk : Kstar .o i = k) :
    windowLength .o (schedule .o i) = (113 * (k * (p + 1)) + 999) / 1000 + 10100 := by
  rw [windowLength_schedule_eq_div .o hi, sStar_def, hp, hk, traceSlopeNum_o, traceSlopeDen_o,
    Hstar_o]
  omega

/-- The clearing exponent at the index `o` with known position and size factor. -/
private lemma ePieceValue_clearingExponent_o {i p k : ℕ} (hi : i ≤ rStar .o)
    (hp : schedule .o i = p) (hk : Kstar .o i = k) :
    clearingExponent .o i =
      (1279 / 100 * (((113 * (k * (p + 1)) + 999) / 1000 + 10100 : ℕ) : ℚ) -
        13 / 9 * ((k * (p + 1) : ℕ) : ℚ)) / 8192 := by
  rw [clearingExponent_o, ePieceValue_windowLength_o hi hp hk, sStar_def, hp, hk]

/-- The middle terms at the index `o`, in terms of the positions and the size factor. -/
private lemma ePieceValue_term_mid_o {i p q k L j : ℕ} (hi : i + 1 ≤ rStar .o)
    (hp : schedule .o i = p) (hq : schedule .o (i + 1) = q) (hk : Kstar .o (i + 1) = k)
    (hle : q + ((113 * (k * (q + 1)) + 999) / 1000 + 10100) + 1 ≤ pStar .o)
    (hpos : p < q) (hj : j ≤ 80) (hb : 10 ^ 24 * (q - p) * Nat.factorial j ≤ L ^ j)
    (ht : (L : ℚ) ≤ (1279 / 100 * (((113 * (k * (q + 1)) + 999) / 1000 + 10100 : ℕ) : ℚ) -
        13 / 9 * ((k * (q + 1) : ℕ) : ℚ)) / 8192) :
    ⌈10 ^ 24 * (clearCount .o (i + 1) : ℚ) /
      expPartialSum 80 (clearingExponent .o (i + 1))⌉ = 1 :=
  ePieceValue_term_mid hp hq (ePieceValue_windowLength_o hi hq hk) hle hpos hj hb
    (by rwa [ePieceValue_clearingExponent_o hi hq hk])

private lemma ePieceValue_schedule_o_0 : schedule .o 0 = 193 := rfl

private lemma ePieceValue_schedule_o_1 : schedule .o 1 = 112161 := by
  simpa using congrArg (fun l : List ℕ => l.getD 1 0) schedule_values_o

private lemma ePieceValue_schedule_o_2 : schedule .o 2 = 20680179 := by
  simpa using congrArg (fun l : List ℕ => l.getD 2 0) schedule_values_o

private lemma ePieceValue_schedule_o_3 : schedule .o 3 = 2948776479 := by
  simpa using congrArg (fun l : List ℕ => l.getD 3 0) schedule_values_o

private lemma ePieceValue_schedule_o_4 : schedule .o 4 = 326497388488 := by
  simpa using congrArg (fun l : List ℕ => l.getD 4 0) schedule_values_o

private lemma ePieceValue_schedule_o_5 : schedule .o 5 = 28144727892821 := by
  simpa using congrArg (fun l : List ℕ => l.getD 5 0) schedule_values_o

private lemma ePieceValue_schedule_o_6 : schedule .o 6 = 1895012673761891 := by
  simpa using congrArg (fun l : List ℕ => l.getD 6 0) schedule_values_o

private lemma ePieceValue_schedule_o_7 : schedule .o 7 = 99969498591645143 := by
  simpa using congrArg (fun l : List ℕ => l.getD 7 0) schedule_values_o

private lemma ePieceValue_schedule_o_8 : schedule .o 8 = 4155432147958923993 := by
  simpa using congrArg (fun l : List ℕ => l.getD 8 0) schedule_values_o

private lemma ePieceValue_schedule_o_9 : schedule .o 9 = 141268071302011590393 := by
  simpa using congrArg (fun l : List ℕ => l.getD 9 0) schedule_values_o

private lemma ePieceValue_schedule_o_10 : schedule .o 10 = 17140454471732661035095372255 := by
  simpa using congrArg (fun l : List ℕ => l.getD 10 0) schedule_values_o

/-- The exact ceiling of the clearing block 0 at the index `o`. -/
private lemma ePieceValue_term_o_0 :
    ⌈10 ^ 24 * (clearCount .o 0 : ℚ) / expPartialSum 80 (clearingExponent .o 0)⌉ =
      (25092769474872960484 : ℕ) + 1 := by
  have hw := ePieceValue_windowLength_o (by decide) ePieceValue_schedule_o_0 Kstar_o_zero
  rw [clearCount_zero_of_le (by rw [hw, ePieceValue_schedule_o_0, pStar_o]; norm_num),
    ePieceValue_schedule_o_0]
  refine ePieceValue_ceil_exact (a := 116938425) (d := 7372800) (by norm_num) ?_ ?_
  · rw [ePieceValue_clearingExponent_o (by decide) ePieceValue_schedule_o_0 Kstar_o_zero]
    norm_num
  · decide +kernel

/-- The exact ceiling of the clearing block 1 at the index `o`. -/
private lemma ePieceValue_term_o_1 :
    ⌈10 ^ 24 * (clearCount .o 1 : ℚ) / expPartialSum 80 (clearingExponent .o 1)⌉ =
      (172985194443383 : ℕ) + 1 := by
  have hw := ePieceValue_windowLength_o (by decide) ePieceValue_schedule_o_1 Kstar_o_one
  rw [clearCount_succ_of_le (i := 0) (by rw [hw, ePieceValue_schedule_o_1, pStar_o]; norm_num),
    ePieceValue_schedule_o_1, ePieceValue_schedule_o_0]
  refine ePieceValue_ceil_exact (a := 251440375) (d := 7372800) (by norm_num) ?_ ?_
  · rw [ePieceValue_clearingExponent_o (by decide) ePieceValue_schedule_o_1 Kstar_o_one]
    norm_num
  · decide +kernel

/-- The last clearing block at the index `o` is empty. -/
private lemma ePieceValue_term_o_10 :
    ⌈10 ^ 24 * (clearCount .o 10 : ℚ) / expPartialSum 80 (clearingExponent .o 10)⌉ = 0 := by
  have hw := ePieceValue_windowLength_o (by decide) ePieceValue_schedule_o_10
    (Kstar_o_of_nine_le (by norm_num))
  rw [clearCount_eq_zero_of_le (by
    rw [hw, pStar_o, clearStart_succ, ePieceValue_schedule_o_9]
    norm_num)]
  simp

/-- The clearing allowance at the original index is
`E_piece(o) = 25092942460067403877 / 10^24`. -/
@[collatz_pos_dens "lem_s02_Epiece_value"]
theorem ePiece_o : ePiece .o = 25092942460067403877 / 10 ^ 24 := by
  have t2 := ePieceValue_term_mid_o (i := 1) (L := 2627) (j := 20) (by decide)
    ePieceValue_schedule_o_1 ePieceValue_schedule_o_2 Kstar_o_two
    (by rw [pStar_o]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by norm_num)
  have t3 := ePieceValue_term_mid_o (i := 2) (L := 2627) (j := 20) (by decide)
    ePieceValue_schedule_o_2 ePieceValue_schedule_o_3 Kstar_o_three
    (by rw [pStar_o]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by norm_num)
  have t4 := ePieceValue_term_mid_o (i := 3) (L := 2627) (j := 20) (by decide)
    ePieceValue_schedule_o_3 ePieceValue_schedule_o_4 Kstar_o_four
    (by rw [pStar_o]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by norm_num)
  have t5 := ePieceValue_term_mid_o (i := 4) (L := 2627) (j := 20) (by decide)
    ePieceValue_schedule_o_4 ePieceValue_schedule_o_5 Kstar_o_five
    (by rw [pStar_o]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by norm_num)
  have t6 := ePieceValue_term_mid_o (i := 5) (L := 2627) (j := 20) (by decide)
    ePieceValue_schedule_o_5 ePieceValue_schedule_o_6 Kstar_o_six
    (by rw [pStar_o]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by norm_num)
  have t7 := ePieceValue_term_mid_o (i := 6) (L := 2627) (j := 20) (by decide)
    ePieceValue_schedule_o_6 ePieceValue_schedule_o_7 Kstar_o_seven
    (by rw [pStar_o]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by norm_num)
  have t8 := ePieceValue_term_mid_o (i := 7) (L := 2627) (j := 20) (by decide)
    ePieceValue_schedule_o_7 ePieceValue_schedule_o_8 Kstar_o_eight
    (by rw [pStar_o]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by norm_num)
  have t9 := ePieceValue_term_mid_o (i := 8) (L := 2627) (j := 20) (by decide)
    ePieceValue_schedule_o_8 ePieceValue_schedule_o_9 (Kstar_o_of_nine_le (by norm_num))
    (by rw [pStar_o]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by norm_num)
  rw [ePiece_def, rStar_o]
  simp only [sum_range_succ, sum_range_zero]
  rw [ePieceValue_term_o_0, ePieceValue_term_o_1, t2, t3, t4, t5, t6, t7, t8, t9,
    ePieceValue_term_o_10]
  norm_num

/-! ### The index `b` -/

/-- The schedule positions, window lengths and interval sizes at the index `b`. -/
private lemma ePieceValue_data_b :
    (schedule .b 0 = 169 ∧ schedule .b 1 = 15486 ∧ schedule .b 2 = 514217) ∧
      (windowLength .b (schedule .b 0) = 15148 ∧ windowLength .b (schedule .b 1) = 498562 ∧
        windowLength .b (schedule .b 2) = 63187608 ∧
        windowLength .b (schedule .b 3) = 8207939556449166) ∧
      (sStar .b 0 = 122060 ∧ sStar .b 1 = 4150516 ∧ sStar .b 2 = 526559232 ∧
        sStar .b 3 = 68399496303738880) := by
  have hp := schedule_values_b
  have hw := windowLength_schedule_values_b
  have hs := sStar_values_b
  simp only [rStar_b, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
    List.cons.injEq] at hp hw hs
  exact ⟨⟨hp.1, hp.2.1, hp.2.2.1⟩, ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1⟩,
    ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩⟩

/-- The clearing exponent at the index `b` with known window length and interval size:
`t^cl_i(b) = (225 h - 26 S) / 4608`. -/
private lemma ePieceValue_clearingExponent_b {i w s : ℕ}
    (hw : windowLength .b (schedule .b i) = w) (hs : sStar .b i = s) :
    clearingExponent .b i = (225 * (w : ℚ) - 26 * s) / 4608 := by
  rw [clearingExponent_b, hw, hs]
  ring

/-- The exact ceiling of the clearing block 0 at the index `b`. -/
private lemma ePieceValue_term_b_0 :
    ⌈10 ^ 24 * (clearCount .b 0 : ℚ) / expPartialSum 80 (clearingExponent .b 0)⌉ =
      (12785 : ℕ) + 1 := by
  obtain ⟨⟨hp0, -, -⟩, ⟨hw0, -, -, -⟩, ⟨hs0, -, -, -⟩⟩ := ePieceValue_data_b
  rw [clearCount_zero_of_le (by rw [hw0, hp0, pStar_b]; norm_num), hp0]
  refine ePieceValue_ceil_exact (a := 234740) (d := 4608) (by norm_num) ?_ ?_
  · rw [ePieceValue_clearingExponent_b hw0 hs0]
    norm_num
  · decide +kernel

/-- The last clearing block at the index `b` is empty. -/
private lemma ePieceValue_term_b_3 :
    ⌈10 ^ 24 * (clearCount .b 3 : ℚ) / expPartialSum 80 (clearingExponent .b 3)⌉ = 0 := by
  obtain ⟨⟨-, -, hp2⟩, ⟨-, -, -, hw3⟩, -⟩ := ePieceValue_data_b
  rw [clearCount_eq_zero_of_le (by rw [hw3, pStar_b, clearStart_succ, hp2]; norm_num)]
  simp

/-- The clearing allowance at the bootstrap index is `E_piece(b) = 12788 / 10^24`. -/
@[collatz_pos_dens "lem_s02_Epiece_value"]
theorem ePiece_b : ePiece .b = 12788 / 10 ^ 24 := by
  obtain ⟨⟨hp0, hp1, hp2⟩, ⟨-, hw1, hw2, -⟩, ⟨-, hs1, hs2, -⟩⟩ := ePieceValue_data_b
  have t1 := ePieceValue_term_mid (ι := .b) (i := 0) (L := 925) (j := 20) hp0 hp1
    hw1 (by rw [pStar_b]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by rw [ePieceValue_clearingExponent_b hw1 hs1]; norm_num)
  have t2 := ePieceValue_term_mid (ι := .b) (i := 1) (L := 925) (j := 20) hp1 hp2
    hw2 (by rw [pStar_b]; norm_num) (by norm_num) (by norm_num) (by norm_num [Nat.factorial])
    (by rw [ePieceValue_clearingExponent_b hw2 hs2]; norm_num)
  rw [ePiece_def, rStar_b]
  simp only [sum_range_succ, sum_range_zero]
  rw [ePieceValue_term_b_0, t1, t2, ePieceValue_term_b_3]
  norm_num

end CollatzPosDens
