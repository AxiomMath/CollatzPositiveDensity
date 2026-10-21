/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.StoppingTrace.TrDirectCrossing
public import CollatzPosDens.Renewal.RnRawMassFormula
public import CollatzPosDens.Renewal.RnRawOddSum

/-!
# The broad first-crossing decrement at small gaps

For every integer `s` with `2 ≤ s ≤ 511` and `s ∉ {3, 6, 9, 13, 16}`, the broad first-crossing
decrement satisfies `D_cr(s) ≥ 61817834604121 / 268435456000000`, with equality at `s = 15`.

The decrement is a finite combination of the replaced crossing coefficients `δ^{rep}_{s,c,o}`,
the Pascal weights `ϖ(c) = (c - 1) 2^{-c}` and the raw-prefix masses `𝖱(k, t)`, which are
`[t = 0]` for `k = 0` and `binom(t - 1, 2k - 1) 2^{-t}` for `k ≥ 1` (and `0` for `t ≤ 0`). The
coefficient `δ^{rep}_{s,c,o}` is the packet deficit `δ^{pk}_{c,o}` except at `(c, o) = (3, 1)`,
where it is `max {δ^{pk}_{3,1}, 1 - ς_s}` with `δ^{pk}_{3,1} = 1/2`, and at `(c, o) = (4, 1)` for
`s ∈ {12, 19}`. All of these numbers are rational, and the bound is checked, for each of the `505`
values, by a computation in natural numbers.

## Main results

* `CollatzPosDens.cast_exitSumQ`: `G(f, t) = ∑_{r=1}^{f} 𝖱(r - 1, t)` as an explicit rational.
* `CollatzPosDens.trDirectCrossing_eq_crossingQ`: `D_cr(s)` equals the explicit rational
  `CollatzPosDens.crossingQ s`.
* `CollatzPosDens.le_trDirectCrossing_of_le_511`: `D_cr(s) ≥ 61817834604121 / 268435456000000`
  for `2 ≤ s ≤ 511`, `s ∉ {3, 6, 9, 13, 16}`.

## Implementation notes

Write `G(f, t) = ∑_{r=1}^{f} 𝖱(r - 1, t)`. Splitting `δ^{rep}_{s,c,o}` into `δ^{pk}_{c,o}` and the
two corrections at `(3, 1)` and `(4, 1)`,
`D_cr(s) = ∑_{j=0}^{15} W_j G(f_s, s - j) + ϖ(3) (δ^{rep}_{s,3,1} - 1/2) G(f_s, s - 2)
  + ϖ(4) (δ^{rep}_{s,4,1} - 41/100) G(f_s, s - 3)`,
where `W_j = ∑_{c - o = j} ϖ(c) δ^{pk}_{c,o}` collects the packet deficits by the difference
`j = c - o ∈ [0, 15]`. The sixteen weights `W_j` do not depend on `s` and are evaluated once
(`CollatzPosDens.weightQ_eq`), in natural numbers: the packet values `F_{c,o}(0)` are multiples
of `10^{-6}` and are computed, scaled by `10^6`, by `CollatzPosDens.pkListN`, a copy of the
recursion of `CollatzPosDens.trPacketValue` in natural numbers (`CollatzPosDens.pkListN_spec`).

For `t ≥ 2`, `2^t G(f, t) = ∑_{k < f - 1} binom(t - 1, 2k + 1) = ∑_{i < 2f - 2} binom(t - 2, i)`,
a prefix sum of a row of Pascal's triangle. For `s ≥ 17` the sixteen rows `s - 17, …, s - 2`
needed for `D_cr(s)` share the prefix length `2 f_s - 2`, so only the first is summed along the
row; each following one comes from
`∑_{i ≤ k} binom(n + 1, i) = 2 ∑_{i ≤ k} binom(n, i) - binom(n, k)` and
`binom(n + 1, k) = binom(n, k) (n + 1) / (n + 1 - k)` (`CollatzPosDens.crossingRows`). For
`2 ≤ s ≤ 16` and `s = 19` the kernel checks, in natural numbers, the bound for a lower estimate of
`D_cr(s)` with the main term exact (`G(f, t)` scaled by `2^t`, `CollatzPosDens.exitN`), the
correction at `(4, 1)` exact and `δ^{rep}_{s,3,1} - 1/2` bounded below by `r_s` as below
(`CollatzPosDens.crossSmallN`, `CollatzPosDens.le_crossingQ_of_crossSmallN`). For the other
`s ≥ 17` the kernel checks, in natural numbers, the bound for the lower estimate
`(A_s / (2^{16} 10^6) + r_s R_{13}) / 2^s` of `D_cr(s)` that drops the correction at `(4, 1)` and
bounds `δ^{rep}_{s,3,1} - 1/2` from below by `r_s` (`CollatzPosDens.crossN`,
`CollatzPosDens.le_crossingFastQ_of_crossN`).

## References

* [Mazur, *Collatz positive density*]
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-! ### Odd binomial coefficients along a row -/

/-- `oddChooseAcc n m = (binom(n, 2m + 1), ∑_{k < m} binom(n, 2k + 1))`, computed along the row
by `binom(n, i + 2) = binom(n, i) (n - i) (n - i - 1) / ((i + 1) (i + 2))`
(`CollatzPosDens.oddChooseAcc_eq`). -/
def oddChooseAcc (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (n, 0)
  | m + 1 =>
    let p := oddChooseAcc n m
    (p.1 * (n - (2 * m + 1)) * (n - (2 * m + 2)) / ((2 * m + 2) * (2 * m + 3)), p.2 + p.1)

/-- `oddChooseAcc n m = (binom(n, 2m + 1), ∑_{k < m} binom(n, 2k + 1))`. -/
theorem oddChooseAcc_eq (n m : ℕ) :
    oddChooseAcc n m = (n.choose (2 * m + 1), ∑ k ∈ range m, n.choose (2 * k + 1)) := by
  induction m with
  | zero => simp [oddChooseAcc]
  | succ m ih =>
    rw [oddChooseAcc, ih]
    ext
    · have h₁ := Nat.choose_succ_right_eq n (2 * m + 1)
      have h₂ := Nat.choose_succ_right_eq n (2 * m + 2)
      refine Nat.div_eq_of_eq_mul_left (by positivity) ?_
      rw [show 2 * m + 1 + 1 = 2 * m + 2 by ring] at h₁
      rw [show 2 * (m + 1) + 1 = 2 * m + 2 + 1 by ring, ← h₁, mul_right_comm, ← h₂]
      ring
    · simp [sum_range_succ]

/-! ### The partial raw-prefix masses -/

/-- The partial raw-prefix mass `G(f, t) = ∑_{r=1}^{f} 𝖱(r - 1, t)` for `f ≥ 1`, as a computable
rational: `[t = 0]` for `t ≤ 0`, and `2^{-t} ∑_{k < f - 1} binom(t - 1, 2k + 1)` for
`t ≥ 1` (`CollatzPosDens.cast_exitSumQ`). -/
def exitSumQ (f : ℕ) (t : ℤ) : ℚ :=
  if t ≤ 0 then (if t = 0 then 1 else 0)
  else ((oddChooseAcc (t.toNat - 1) (f - 1)).2 : ℚ) / (2 ^ t.toNat : ℕ)

/-- `exitSumQ f t = ∑_{r=1}^{f} 𝖱(r - 1, t)` for `f ≥ 1`. -/
theorem cast_exitSumQ {f : ℕ} (hf : 1 ≤ f) (t : ℤ) :
    (exitSumQ f t : ℝ) = ∑ r ∈ Icc 1 f, rawMass (r - 1) t := by
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, show m + 1 + 1 - 1 = m + 1 by omega,
    sum_range_succ']
  simp only [show ∀ k, 1 + (k + 1) - 1 = k + 1 by omega, show 1 + 0 - 1 = 0 by omega,
    rawMass_zero]
  have hR : ∀ k : ℕ, rawMass (k + 1) t = ((t - 1).toNat.choose (2 * k + 1) : ℝ) * 2 ^ (-t) :=
    fun k ↦ by rw [rawMass_eq_choose (by omega), show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  simp only [hR, exitSumQ, oddChooseAcc_eq, show m + 1 - 1 = m by omega]
  split_ifs with h₁ h₂ h₂
  · simp [show (t - 1).toNat = 0 by omega]
  · simp [show (t - 1).toNat = 0 by omega]
  · omega
  · lift t to ℕ using by omega
    rw [show ((t : ℤ) - 1).toNat = t - 1 by omega, ← sum_mul, zpow_neg, zpow_natCast]
    push_cast
    simp [div_eq_mul_inv]

/-! ### The packet weights and the two corrections -/

/-- `ϖ(c) = (c - 1) / 2^c` for natural `c ≥ 2`. -/
theorem varpi_natCast_of_two_le {c : ℕ} (hc : 2 ≤ c) : varpi c = ((c : ℝ) - 1) / 2 ^ c := by
  rw [varpi_of_two_le (by omega), zpow_neg, zpow_natCast, div_eq_mul_inv]
  simp

/-- The weight `W_j = ∑_{3 ≤ c ≤ 16, 1 ≤ o ≤ c, c - o = j} ϖ(c) δ^{pk}_{c,o}`. -/
def weightQ (j : ℕ) : ℚ :=
  ∑ c ∈ Icc (3 : ℕ) 16, ∑ o ∈ Icc 1 c,
    if c - o = j then ((c : ℚ) - 1) / 2 ^ c * trPacketDeficit c o else 0

/-- The exact values of the sixteen weights `W_0, …, W_15`. -/
def weightTable : List ℚ :=
  [59987721/1638400000, 832326661/6553600000, 655913787/2048000000, 14891187/81920000,
   206851881/1638400000, 103396153/1638400000, 51668289/1638400000, 25804357/1638400000,
   12872391/1638400000, 800801/204800000, 198369/102400000, 3116679/3276800000,
   601081/1310720000, 697807/3276800000, 93/1024000, 31/1024000]

/-- `2^{16} 10^6 W_j` as a natural number. -/
def weightN (j : ℕ) : ℕ :=
  ∑ c ∈ Icc (3 : ℕ) 16, ∑ o ∈ Icc 1 c, if c - o = j then pvN c o * 2 ^ (16 - c) else 0

/-- `W_j = weightN j / (2^{16} 10^6)`. -/
theorem weightQ_eq_weightN (j : ℕ) : weightQ j = (weightN j : ℚ) / (2 ^ 16 * 10 ^ 6) := by
  rw [weightQ, weightN, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  refine sum_congr rfl fun c hc => ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  refine sum_congr rfl fun o _ => ?_
  rw [mem_Icc] at hc
  split_ifs
  · rw [trPacketDeficit, trPacketValue_eq_pvN]
    have h1 : (c : ℚ) - 1 ≠ 0 := by
      have : (3 : ℚ) ≤ c := by exact_mod_cast hc.1
      linarith
    have h2 : (2 : ℚ) ^ 16 = 2 ^ (16 - c) * 2 ^ c := by
      rw [← pow_add, Nat.sub_add_cancel hc.2]
    push_cast
    rw [h2]
    field_simp
  · simp

/-- The values `2^{16} 10^6 W_j` of `weightTable`. -/
def weightTableN : List ℕ :=
  [2399508840, 8323266610, 20989241184, 11912949600, 8274075240, 4135846120, 2066731560,
   1032174280, 514895640, 256256320, 126956160, 62333580, 30054050, 13956140, 5952000, 1984000]

/-- The natural numbers `weightN j`, `j < 16`, are the entries of `weightTableN`. -/
theorem weightN_eq : ∀ j ∈ range 16, weightN j = weightTableN.getD j 0 := by
  decide +kernel

/-- The entries of `weightTable` are those of `weightTableN` divided by `2^{16} 10^6`. -/
theorem weightTable_eq : ∀ j ∈ range 16,
    weightTable.getD j 0 = (weightTableN.getD j 0 : ℚ) / (2 ^ 16 * 10 ^ 6) := by
  intro j hj
  rw [mem_range] at hj
  match j, hj with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _ | 12, _
  | 13, _ | 14, _ | 15, _ => norm_num [weightTable, weightTableN]
  | _ + 16, hj => omega

/-- The weights `W_j`, `0 ≤ j ≤ 15`, are the entries of `weightTable`. -/
theorem weightQ_eq (j : ℕ) (hj : j ∈ range 16) : weightQ j = weightTable.getD j 0 := by
  rw [weightQ_eq_weightN, weightN_eq j hj, weightTable_eq j hj]

/-- `δ^{pk}_{3,1} = 1/2`. -/
theorem trPacketDeficit_three_one : trPacketDeficit 3 1 = 1 / 2 := by
  rw [trPacketDeficit, trPacketValue_eq_pvN, show pvN 3 1 = 10 ^ 6 by decide +kernel]
  norm_num

/-- `δ^{pk}_{4,1} = 41/100`. -/
theorem trPacketDeficit_four_one : trPacketDeficit 4 1 = 41 / 100 := by
  rw [trPacketDeficit, trPacketValue_eq_pvN, show pvN 4 1 = 1230000 by decide +kernel]
  norm_num

/-- The cap `ς_s` with its powers computed in `ℕ`:
`min {1, max {1/2^16, 11 · 37037 · 9^{f_s} / (7 · 10^6 · 2^s)}}`. -/
def raw3CapQ (s : ℕ) : ℚ :=
  min 1 (max (1 / (2 ^ 16 : ℕ)) ((11 * 37037 * 9 ^ bkExitWidth s : ℕ) / (7 * 10 ^ 6 * 2 ^ s : ℕ)))

/-- The cap `ς_s` equals `raw3CapQ s`. -/
theorem trRaw3Cap_eq_raw3CapQ (s : ℕ) : trRaw3Cap s = raw3CapQ s := by
  rw [trRaw3Cap_def, raw3CapQ, epsStar_eq, zpow_neg (2 : ℚ) (s : ℤ), zpow_natCast]
  push_cast
  congr 2
  · norm_num
  · field_simp
    ring

/-- The correction `δ^{rep}_{s,3,1} - δ^{pk}_{3,1} = max {1/2, 1 - ς_s} - 1/2`. -/
def repCorrThree (s : ℕ) : ℚ := max (1 / 2) (1 - raw3CapQ s) - 1 / 2

/-- The correction `δ^{rep}_{s,4,1} - δ^{pk}_{4,1}`: `29/50 - 41/100` at `s = 12`,
`16/25 - 41/100` at `s = 19`, and `0` otherwise. -/
def repCorrFour (s : ℕ) : ℚ :=
  if s = 12 then 29 / 50 - 41 / 100 else if s = 19 then 16 / 25 - 41 / 100 else 0

/-- `δ^{rep}_{s,c,o}` is `δ^{pk}_{c,o}` plus the corrections at `(3, 1)` and `(4, 1)`. -/
theorem trRepCoeff_eq_add (s c o : ℕ) :
    trRepCoeff s c o = trPacketDeficit c o +
      (if c = 3 then if o = 1 then repCorrThree s else 0 else 0) +
      (if c = 4 then if o = 1 then repCorrFour s else 0 else 0) := by
  by_cases ho : o = 1
  · subst ho
    by_cases h₃ : c = 3
    · subst h₃
      simp [repCorrThree, trPacketDeficit_three_one, trRaw3Cap_eq_raw3CapQ]
    by_cases h₄ : c = 4
    · subst h₄
      by_cases h₁₂ : s = 12
      · subst h₁₂
        rw [trRepCoeff_four_one_twelve, trPacketDeficit_four_one]
        norm_num [repCorrFour]
      by_cases h₁₉ : s = 19
      · subst h₁₉
        rw [trRepCoeff_four_one_nineteen, trPacketDeficit_four_one]
        norm_num [repCorrFour]
      rw [trRepCoeff_of_ne (by omega) (by omega)]
      simp [repCorrFour, h₁₂, h₁₉]
    simp [trRepCoeff_of_ne_three_of_ne_four h₃ h₄, h₃, h₄]
  · simp [trRepCoeff_of_ne_one ho, ho]

/-- Grouping the double sum `∑_{3 ≤ c ≤ 16} ∑_{1 ≤ o ≤ c} a_{c,o} g(s + o - c)` by the
difference `j = c - o ∈ [0, 15]`. -/
theorem sum_sum_mul_eq_sum_range {M : Type*} [CommRing M] (a : ℕ → ℕ → M) (g : ℤ → M) (s : ℤ) :
    ∑ c ∈ Icc (3 : ℕ) 16, ∑ o ∈ Icc 1 c, a c o * g (s + o - c) =
      ∑ j ∈ range 16, (∑ c ∈ Icc (3 : ℕ) 16, ∑ o ∈ Icc 1 c, if c - o = j then a c o else 0) *
        g (s - j) := by
  simp_rw [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  refine sum_congr rfl fun c hc ↦ ?_
  rw [sum_comm]
  refine sum_congr rfl fun o ho ↦ ?_
  rw [mem_Icc] at hc ho
  simp only [sum_ite_eq, mem_range, show c - o < 16 by omega, ite_true]
  congr 2
  push_cast [show o ≤ c by omega]
  ring

/-! ### The exact value of the decrement -/

/-- The explicit rational
`∑_{j=0}^{15} W_j G(f_s, s - j) + (1/4) (δ^{rep}_{s,3,1} - 1/2) G(f_s, s - 2)
  + (3/16) (δ^{rep}_{s,4,1} - 41/100) G(f_s, s - 3)`. -/
def crossingQ (s : ℕ) : ℚ :=
  ∑ j ∈ range 16, weightTable.getD j 0 * exitSumQ (bkExitWidth s) ((s : ℤ) - j) +
    1 / 4 * repCorrThree s * exitSumQ (bkExitWidth s) ((s : ℤ) - 2) +
    3 / 16 * repCorrFour s * exitSumQ (bkExitWidth s) ((s : ℤ) - 3)

/-- `D_cr(s)` is the rational number `crossingQ s`. -/
theorem trDirectCrossing_eq_crossingQ (s : ℕ) : trDirectCrossing s = crossingQ s := by
  have hG : ∀ t : ℤ, ∑ r ∈ Icc 1 (bkExitWidth s), rawMass (r - 1) t =
      (exitSumQ (bkExitWidth s) t : ℝ) := fun t ↦ (cast_exitSumQ (one_le_bkExitWidth s) t).symm
  have hrep : ∀ c o, (trRepCoeff s c o : ℝ) = (trPacketDeficit c o : ℝ) +
      (if c = 3 then if o = 1 then (repCorrThree s : ℝ) else 0 else 0) +
      (if c = 4 then if o = 1 then (repCorrFour s : ℝ) else 0 else 0) := fun c o ↦ by
    rw [trRepCoeff_eq_add]
    push_cast [apply_ite (Rat.cast : ℚ → ℝ)]
    rfl
  have hpk := sum_sum_mul_eq_sum_range
    (fun c o ↦ ((((c : ℚ) - 1) / 2 ^ c * trPacketDeficit c o : ℚ) : ℝ))
    (fun t ↦ (exitSumQ (bkExitWidth s) t : ℝ)) (s : ℤ)
  rw [trDirectCrossing]
  simp only [hG, hrep, add_mul, sum_add_distrib, mul_add, ite_mul, zero_mul]
  rw [crossingQ, Rat.cast_add, Rat.cast_add, Rat.cast_sum]
  congr 2
  · have hw : ∀ j ∈ range 16,
        ((weightTable.getD j 0 * exitSumQ (bkExitWidth s) ((s : ℤ) - j) : ℚ) : ℝ) =
          (weightQ j : ℝ) * (exitSumQ (bkExitWidth s) ((s : ℤ) - j) : ℝ) := fun j hj ↦ by
      rw [weightQ_eq j hj, Rat.cast_mul]
    rw [sum_congr rfl hw]
    simp only [weightQ, Rat.cast_sum, apply_ite (Rat.cast : ℚ → ℝ), Rat.cast_zero]
    rw [← hpk]
    refine sum_congr rfl fun c hc ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun o _ ↦ ?_
    rw [varpi_natCast_of_two_le (by simp at hc; omega)]
    push_cast
    ring
  · rw [sum_eq_single 3 (fun c _ hc ↦ by simp [hc]) (by simp)]
    simp only [↓reduceIte]
    rw [sum_eq_single 1 (fun o _ ho ↦ by simp [ho]) (by simp)]
    simp only [↓reduceIte, Nat.cast_ofNat, varpi_three]
    push_cast
    ring_nf
  · rw [sum_eq_single 4 (fun c _ hc ↦ by simp [hc]) (by simp)]
    simp only [↓reduceIte]
    rw [sum_eq_single 1 (fun o _ ho ↦ by simp [ho]) (by simp)]
    simp only [↓reduceIte, Nat.cast_ofNat, varpi_four]
    push_cast
    ring_nf

/-! ### Shifting the row -/

/-- `prefixChooseAcc n k = (binom(n, k), ∑_{i < k} binom(n, i))`, computed along the row by
`binom(n, i + 1) = binom(n, i) (n - i) / (i + 1)` (`CollatzPosDens.prefixChooseAcc_eq`). -/
def prefixChooseAcc (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 =>
    let p := prefixChooseAcc n k
    (p.1 * (n - k) / (k + 1), p.2 + p.1)

/-- `prefixChooseAcc n k = (binom(n, k), ∑_{i < k} binom(n, i))`. -/
theorem prefixChooseAcc_eq (n k : ℕ) :
    prefixChooseAcc n k = (n.choose k, ∑ i ∈ range k, n.choose i) := by
  induction k with
  | zero => simp [prefixChooseAcc]
  | succ k ih =>
    rw [prefixChooseAcc, ih]
    ext
    · exact Nat.div_eq_of_eq_mul_left (by omega) (Nat.choose_succ_right_eq n k).symm
    · simp [sum_range_succ]

/-- `binom(n + 1, k)` computed from `x = binom(n, k)` (`CollatzPosDens.chooseSuccLeft_choose`). -/
def chooseSuccLeft (n k x : ℕ) : ℕ :=
  if k ≤ n then x * (n + 1) / (n + 1 - k) else if k = n + 1 then 1 else 0

/-- `chooseSuccLeft n k (binom(n, k)) = binom(n + 1, k)`. -/
theorem chooseSuccLeft_choose (n k : ℕ) :
    chooseSuccLeft n k (n.choose k) = (n + 1).choose k := by
  unfold chooseSuccLeft
  split_ifs with h₁ h₂
  · exact Nat.div_eq_of_eq_mul_left (by omega) (Nat.choose_mul_succ_eq n k)
  · subst h₂
    simp
  · rw [Nat.choose_eq_zero_of_lt (by omega)]

/-- `∑_{i ≤ k} binom(n + 1, i) + binom(n, k) = 2 ∑_{i ≤ k} binom(n, i)`. -/
theorem sum_range_choose_succ_add (n k : ℕ) :
    ∑ i ∈ range (k + 1), (n + 1).choose i + n.choose k =
      2 * ∑ i ∈ range (k + 1), n.choose i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, sum_range_succ (fun i ↦ n.choose i) (k + 1), Nat.choose_succ_succ']
    omega

/-- From `(n, binom(n, k), ∑_{j ≤ k} binom(n, j))`, the list of the prefix sums
`∑_{j ≤ k} binom(n + l, j)`, `l < i` (`CollatzPosDens.getD_shiftRows`). -/
def shiftRows (k : ℕ) : ℕ → ℕ × ℕ × ℕ → List ℕ
  | 0, _ => []
  | i + 1, (n, x, p) => p :: shiftRows k i (n + 1, chooseSuccLeft n k x, 2 * p - x)

/-- For `l < i`, the entry `l` of `shiftRows k i (n, binom(n, k), ∑_{j ≤ k} binom(n, j))` is
`∑_{j ≤ k} binom(n + l, j)`. -/
theorem getD_shiftRows (k i n : ℕ) {l : ℕ} (hl : l < i) :
    (shiftRows k i (n, n.choose k, ∑ j ∈ range (k + 1), n.choose j)).getD l 0 =
      ∑ j ∈ range (k + 1), (n + l).choose j := by
  induction i generalizing n l with
  | zero => omega
  | succ i ih =>
    rcases l with _ | l
    · simp [shiftRows]
    · have h := sum_range_choose_succ_add n k
      rw [shiftRows, List.getD_cons_succ, chooseSuccLeft_choose,
        show 2 * ∑ j ∈ range (k + 1), n.choose j - n.choose k =
          ∑ j ∈ range (k + 1), (n + 1).choose j by omega, ih (n + 1) (by omega),
        show n + 1 + l = n + (l + 1) by ring]

/-- The sixteen numerators `2^{s - j} G(f_s, s - j)`, `j = 15, …, 0`, for `s ≥ 17`
(`CollatzPosDens.exitSumQ_eq_crossingRows`): the prefix sums of the rows `s - 17, …, s - 2` of
Pascal's triangle up to the index `2 f_s - 3`. -/
def crossingRows (s : ℕ) : List ℕ :=
  let k := 2 * bkExitWidth s - 3
  let a := prefixChooseAcc (s - 17) k
  shiftRows k 16 (s - 17, a.1, a.2 + a.1)

/-- For `s ≥ 17` and `j ≤ 15`, `G(f_s, s - j)` is the entry `15 - j` of `crossingRows s` divided
by `2^{s - j}`. -/
theorem exitSumQ_eq_crossingRows {s j : ℕ} (hs : 17 ≤ s) (hj : j ≤ 15) :
    exitSumQ (bkExitWidth s) ((s : ℤ) - j) =
      ((crossingRows s).getD (15 - j) 0 : ℚ) / (2 ^ (s - j) : ℕ) := by
  have hf := bkExitWidth_def s
  rw [exitSumQ]
  simp only [show ¬((s : ℤ) - j ≤ 0) by omega, ↓reduceIte]
  rw [show ((s : ℤ) - j).toNat = s - j by omega]
  congr 2
  rw [crossingRows, prefixChooseAcc_eq, ← sum_range_succ, getD_shiftRows _ _ _ (by omega),
    oddChooseAcc_eq, show s - j - 1 = s - j - 2 + 1 by omega, sum_range_choose_succ_odd,
    show s - 17 + (15 - j) = s - j - 2 by omega,
    show 2 * bkExitWidth s - 3 + 1 = 2 * (bkExitWidth s - 1) by omega]

/-- `crossingQ s` with the partial raw-prefix masses read off `crossingRows s`. -/
def crossingFastQ (s : ℕ) : ℚ :=
  ∑ j ∈ range 16, weightTable.getD j 0 *
      (((crossingRows s).getD (15 - j) 0 : ℚ) / (2 ^ (s - j) : ℕ)) +
    1 / 4 * repCorrThree s * (((crossingRows s).getD 13 0 : ℚ) / (2 ^ (s - 2) : ℕ)) +
    3 / 16 * repCorrFour s * (((crossingRows s).getD 12 0 : ℚ) / (2 ^ (s - 3) : ℕ))

/-- For `s ≥ 17`, `crossingQ s = crossingFastQ s`. -/
theorem crossingQ_eq_crossingFastQ {s : ℕ} (hs : 17 ≤ s) : crossingQ s = crossingFastQ s := by
  have h₂ := exitSumQ_eq_crossingRows hs (j := 2) (by norm_num)
  have h₃ := exitSumQ_eq_crossingRows hs (j := 3) (by norm_num)
  simp only [Nat.cast_ofNat] at h₂ h₃
  rw [crossingQ, crossingFastQ, h₂, h₃,
    sum_congr rfl fun j hj ↦ by rw [exitSumQ_eq_crossingRows hs (by simp at hj; omega)]]

/-! ### The kernel evaluation -/

/-- The gaps excluded from the bound. -/
def crossingExceptions : Finset ℕ := {3, 6, 9, 13, 16}

/-! ### A fast check of the decrement at the gaps `s ≥ 17` -/

/-- `prefixChooseAcc`, by the bare recursor and explicit natural-number operations. -/
def prefixChooseAccR (n k : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ) (1, 0)
    (fun k p => (Nat.div (Nat.mul p.1 (Nat.sub n k)) (Nat.succ k), Nat.add p.2 p.1)) k

/-- `prefixChooseAccR n k = prefixChooseAcc n k`. -/
theorem prefixChooseAccR_eq (n k : ℕ) : prefixChooseAccR n k = prefixChooseAcc n k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change (Nat.div (Nat.mul (prefixChooseAccR n k).1 (Nat.sub n k)) (Nat.succ k),
      Nat.add (prefixChooseAccR n k).2 (prefixChooseAccR n k).1) = _
    rw [ih, prefixChooseAcc]
    rfl

/-- `chooseSuccLeft`, with the comparisons decided by `Nat.ble` and `Nat.beq`. -/
def chooseSuccLeftR (n k x : ℕ) : ℕ :=
  cond (Nat.ble k n) (Nat.div (Nat.mul x (Nat.succ n)) (Nat.sub (Nat.succ n) k))
    (cond (Nat.beq k (Nat.succ n)) 1 0)

/-- `chooseSuccLeftR n k x = chooseSuccLeft n k x`. -/
theorem chooseSuccLeftR_eq (n k x : ℕ) : chooseSuccLeftR n k x = chooseSuccLeft n k x := by
  unfold chooseSuccLeftR chooseSuccLeft
  by_cases h₁ : k ≤ n
  · simp [h₁, Nat.ble_eq_true_of_le h₁]; rfl
  · have : Nat.ble k n = false := by
      cases h : Nat.ble k n
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) h₁
    by_cases h₂ : k = n + 1 <;> simp [h₁, h₂, this]

/-- `shiftRows`, by the bare recursor. -/
def shiftRowsR (k : ℕ) (i : ℕ) : ℕ × ℕ × ℕ → List ℕ :=
  Nat.rec (motive := fun _ => ℕ × ℕ × ℕ → List ℕ) (fun _ => [])
    (fun _ ih q => q.2.2 :: ih (Nat.succ q.1, chooseSuccLeftR q.1 k q.2.1,
      Nat.sub (Nat.mul 2 q.2.2) q.2.1)) i

/-- `shiftRowsR k i q = shiftRows k i q`. -/
theorem shiftRowsR_eq (k i : ℕ) (q : ℕ × ℕ × ℕ) : shiftRowsR k i q = shiftRows k i q := by
  induction i generalizing q with
  | zero => rfl
  | succ i ih =>
    obtain ⟨n, x, p⟩ := q
    change p :: shiftRowsR k i (Nat.succ n, chooseSuccLeftR n k x, Nat.sub (Nat.mul 2 p) x) = _
    rw [ih, chooseSuccLeftR_eq, shiftRows]
    rfl

/-- `crossingRows`, computed with `prefixChooseAccR` and `shiftRowsR`. -/
def crossingRowsR (s : ℕ) : List ℕ :=
  let k := Nat.sub (Nat.mul 2 (bkExitWidth s)) 3
  let a := prefixChooseAccR (Nat.sub s 17) k
  shiftRowsR k 16 (Nat.sub s 17, a.1, Nat.add a.2 a.1)

/-- `crossingRowsR s = crossingRows s`. -/
theorem crossingRowsR_eq (s : ℕ) : crossingRowsR s = crossingRows s := by
  simp only [crossingRowsR, crossingRows, prefixChooseAccR_eq, shiftRowsR_eq]
  rfl

/-- The weights `2^{16} 10^6 W_{15-i} 2^{15-i}`, `i < 16`. -/
def weightRevN : List ℕ :=
  [65011712000, 97517568000, 114328698880, 123101388800, 127659171840, 130003107840,
   131203235840, 131813283840, 132118307840, 132270819840, 132347075840, 132385203840,
   95303596800, 83956964736, 16646533220, 2399508840]

/-- `∑_{i < |W|} R_i W_i`, by the bare recursor on `W` (missing entries of `R` count as `0`). -/
def dotN (W : List ℕ) : List ℕ → ℕ :=
  List.rec (motive := fun _ => List ℕ → ℕ) (fun _ => 0)
    (fun w _ ih R => Nat.add (Nat.mul (R.headD 0) w) (ih R.tail)) W

/-- `dotN W R = ∑_{i < |W|} R_i W_i`, with missing entries of `R` read as `0`. -/
theorem dotN_eq : ∀ (W R : List ℕ), dotN W R = ∑ i ∈ range W.length, R.getD i 0 * W.getD i 0
  | [], _ => rfl
  | w :: W, R => by
    change Nat.add (Nat.mul (R.headD 0) w) (dotN W R.tail) = _
    rw [dotN_eq W R.tail, List.length_cons, sum_range_succ']
    cases R <;> simp [add_comm]

/-- `2^{16} 10^6 ∑_{j<16} W_j 2^j R_{15-j}`. -/
def crossMainN (R : List ℕ) : ℕ := dotN weightRevN R

/-- The entry `j < 16` of `weightRevN` is `2^{16} 10^6 W_{15-j} 2^{15-j}`. -/
theorem weightRevN_getD : ∀ j ∈ range 16,
    weightRevN.getD j 0 = weightTableN.getD (15 - j) 0 * 2 ^ (15 - j) := by
  decide +kernel

/-- `2^{15} b - max {b, 2^{16} a}`, with `a = 11 · 37037 · 9^{f_s}` and `b = 7 · 10^6 · 2^s`: the
numerator over `2^{16} b` of a lower bound for `δ^{rep}_{s,3,1} - δ^{pk}_{3,1}`. -/
def corr3N (s : ℕ) : ℕ :=
  32768 * (7 * 10 ^ 6 * 2 ^ s) - max (7 * 10 ^ 6 * 2 ^ s) (65536 * (11 * 37037 * 9 ^ bkExitWidth s))

/-- The check, in natural numbers, that `61817834604121 / 268435456000000` is at most the lower
bound `(A / (2^{16} 10^6) + r R_{13} / (2^{16} b)) / 2^s` of the decrement at `s`, where
`R = crossingRows s`, `A = crossMainN R`, `r = corr3N s` and `b = 7 · 10^6 · 2^s`. -/
def crossN (s : ℕ) : Bool :=
  Nat.ble (61817834604121 * (2 ^ 16 * 10 ^ 6 * 65536 * (7 * 10 ^ 6 * 2 ^ s) * 2 ^ s))
    (268435456000000 * (crossMainN (crossingRowsR s) * 65536 * (7 * 10 ^ 6 * 2 ^ s) +
      2 ^ 16 * 10 ^ 6 * (crossingRowsR s).getD 13 0 * corr3N s))

/-- `corr3N s / (2^{16} b) ≤ δ^{rep}_{s,3,1} - δ^{pk}_{3,1}`, where `b = 7 · 10^6 · 2^s`. -/
theorem corr3N_le (s : ℕ) :
    (corr3N s : ℚ) / (65536 * ((7 * 10 ^ 6 * 2 ^ s : ℕ) : ℚ)) ≤ repCorrThree s := by
  set b : ℕ := 7 * 10 ^ 6 * 2 ^ s with hb
  set a : ℕ := 11 * 37037 * 9 ^ bkExitWidth s with ha
  have hb0 : (0 : ℚ) < b := by positivity
  have hς : raw3CapQ s ≤ (max b (65536 * a) : ℕ) / (65536 * b) := by
    rw [raw3CapQ]
    refine (min_le_right _ _).trans (max_le ?_ ?_)
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith [le_max_left (b : ℚ) (65536 * a)]
    · rw [← hb, ← ha, div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      nlinarith [le_max_right (b : ℚ) (65536 * a)]
  rw [repCorrThree, corr3N, ← hb, ← ha]
  rcases le_total (max b (65536 * a)) (32768 * b) with h | h
  · rw [Nat.cast_sub h, sub_div]
    have : ((32768 * b : ℕ) : ℚ) / (65536 * b) = 1 / 2 := by
      push_cast; field_simp; norm_num
    rw [this]
    have := le_max_right (1 / 2 : ℚ) (1 - raw3CapQ s)
    linarith
  · rw [Nat.sub_eq_zero_of_le h]
    simp only [Nat.cast_zero, zero_div, sub_nonneg]
    exact le_max_left _ _

/-- The correction `δ^{rep}_{s,4,1} - δ^{pk}_{4,1}` is nonnegative. -/
theorem repCorrFour_nonneg (s : ℕ) : 0 ≤ repCorrFour s := by
  unfold repCorrFour; split_ifs <;> norm_num

/-- For `s ≥ 17`, the main term `∑_{j=0}^{15} W_j G(f_s, s - j)`, read off `crossingRows s`,
equals `crossMainN (crossingRows s) / (2^{16} 10^6 2^s)`. -/
theorem crossMain_eq {s : ℕ} (hs : 17 ≤ s) :
    ∑ j ∈ range 16, weightTable.getD j 0 *
      (((crossingRows s).getD (15 - j) 0 : ℚ) / (2 ^ (s - j) : ℕ)) =
      (crossMainN (crossingRows s) : ℚ) / (2 ^ 16 * 10 ^ 6 * 2 ^ s) := by
  rw [crossMainN, dotN_eq, show weightRevN.length = 16 from rfl, ← sum_range_reflect,
    Nat.cast_sum, div_eq_mul_inv (∑ _ ∈ _, _), Finset.sum_mul]
  refine sum_congr rfl fun j hj => ?_
  have hj15 : j ≤ 15 := by rw [mem_range] at hj; omega
  rw [show 16 - 1 - j = 15 - j by omega, show 15 - (15 - j) = j by omega,
    weightRevN_getD j hj, weightTable_eq (15 - j) (mem_range.2 (by omega))]
  have hj' : 15 - j ≤ s := by omega
  have h2 : (2 : ℚ) ^ s = 2 ^ (s - (15 - j)) * 2 ^ (15 - j) := by
    rw [← pow_add, Nat.sub_add_cancel hj']
  push_cast
  rw [h2]
  field_simp

/-- For `b, t > 0`, the inequality
`61817834604121 (2^{16} 10^6 2^{16} b t) ≤ 268435456000000 (2^{16} A b + 2^{16} 10^6 R r)` gives
`61817834604121 / 268435456000000 ≤ A / (2^{16} 10^6 t) + r R / (2^{16} b t)`. -/
theorem crossKey {A R r b t : ℚ} (hb : 0 < b) (ht : 0 < t)
    (h : 61817834604121 * (65536000000 * 65536 * b * t) ≤
      268435456000000 * (A * 65536 * b + 65536000000 * R * r)) :
    (61817834604121 / 268435456000000 : ℚ) ≤ A / (65536000000 * t) + r * R / (65536 * b * t) := by
  rw [div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by norm_num) (by positivity)]
  have := mul_le_mul_of_nonneg_right h ht.le
  nlinarith

/-- For `s ≥ 17`, a passing check `crossN s` gives
`61817834604121 / 268435456000000 ≤ crossingFastQ s`. -/
theorem le_crossingFastQ_of_crossN {s : ℕ} (hs : 17 ≤ s) (h : crossN s = true) :
    (61817834604121 / 268435456000000 : ℚ) ≤ crossingFastQ s := by
  have h' := Nat.le_of_ble_eq_true h
  rw [crossingRowsR_eq] at h'
  have hb0 : (0 : ℚ) < ((7 * 10 ^ 6 * 2 ^ s : ℕ) : ℚ) := by positivity
  have h3 : (corr3N s : ℚ) * (crossingRows s).getD 13 0 /
      (65536 * ((7 * 10 ^ 6 * 2 ^ s : ℕ) : ℚ) * 2 ^ s) ≤
      1 / 4 * repCorrThree s * (((crossingRows s).getD 13 0 : ℚ) / (2 ^ (s - 2) : ℕ)) := by
    have e : (2 : ℚ) ^ s = 2 ^ (s - 2) * 4 := by
      rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_add, Nat.sub_add_cancel (by omega)]
    have hc := corr3N_le s
    calc (corr3N s : ℚ) * (crossingRows s).getD 13 0 /
          (65536 * ((7 * 10 ^ 6 * 2 ^ s : ℕ) : ℚ) * 2 ^ s)
        = (corr3N s : ℚ) / (65536 * ((7 * 10 ^ 6 * 2 ^ s : ℕ) : ℚ)) *
            (((crossingRows s).getD 13 0 : ℚ) / (2 ^ (s - 2) * 4)) := by
          rw [← e]; field_simp
      _ ≤ repCorrThree s * (((crossingRows s).getD 13 0 : ℚ) / (2 ^ (s - 2) * 4)) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := by push_cast; ring
  have h4 : 0 ≤ 3 / 16 * repCorrFour s *
      (((crossingRows s).getD 12 0 : ℚ) / (2 ^ (s - 3) : ℕ)) := by
    have := repCorrFour_nonneg s
    positivity
  have hmain := crossMain_eq hs
  rw [show (2 : ℚ) ^ 16 * 10 ^ 6 * 2 ^ s = 65536000000 * 2 ^ s by norm_num] at hmain
  rw [crossingFastQ, hmain]
  generalize crossMainN (crossingRows s) = A at h' ⊢
  generalize corr3N s = r at h' h3
  generalize (crossingRows s).getD 13 0 = R at h' h3 ⊢
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = 7 * 10 ^ 6 * 2 ^ s := ⟨_, rfl⟩
  rw [← hb] at h' h3 hb0
  have hc' : (61817834604121 : ℚ) * (65536000000 * 65536 * b * 2 ^ s) ≤
      268435456000000 * (A * 65536 * b + 65536000000 * R * r) := by
    have h'' : 61817834604121 * (65536000000 * 65536 * b * 2 ^ s) ≤
        268435456000000 * (A * 65536 * b + 65536000000 * R * r) := by
      simpa only [show (2 : ℕ) ^ 16 * 10 ^ 6 = 65536000000 by norm_num] using h'
    exact_mod_cast h''
  have key := crossKey hb0 (by positivity) hc'
  linarith

/-! ### A check of the decrement in natural numbers at the gaps `s ≤ 16` and `s = 19` -/

/-- `2^{max t 0} G(f, t)` in natural numbers: `[t = 0]` for `t ≤ 0`, and
`∑_{k < f - 1} binom(t - 1, 2k + 1)` for `t ≥ 1` (`CollatzPosDens.exitSumQ_mul_two_pow`). -/
def exitN (f : ℕ) (t : ℤ) : ℕ :=
  if t ≤ 0 then (if t = 0 then 1 else 0) else (oddChooseAcc (t.toNat - 1) (f - 1)).2

/-- `G(f, s - j) 2^s = 2^j exitN f (s - j)`. -/
theorem exitSumQ_mul_two_pow (f s j : ℕ) :
    exitSumQ f ((s : ℤ) - j) * 2 ^ s = (exitN f ((s : ℤ) - j) : ℚ) * 2 ^ j := by
  by_cases hj : j ≤ s
  · unfold exitSumQ exitN
    split_ifs with h1 h2
    · obtain rfl : j = s := by omega
      simp
    · omega
    · have h2s : (2 : ℚ) ^ s = 2 ^ (s - j) * 2 ^ j := by rw [← pow_add, Nat.sub_add_cancel hj]
      rw [show ((s : ℤ) - j).toNat = s - j by omega, h2s]
      push_cast
      field_simp
  · simp [exitSumQ, exitN, show (s : ℤ) - j ≤ 0 by omega, show (s : ℤ) - j ≠ 0 by omega]

/-- `100 (δ^{rep}_{s,4,1} - 41/100)`. -/
def corr4N (s : ℕ) : ℕ := if s = 12 then 17 else if s = 19 then 23 else 0

/-- `δ^{rep}_{s,4,1} - δ^{pk}_{4,1} = corr4N s / 100`. -/
theorem repCorrFour_eq_corr4N (s : ℕ) : repCorrFour s = (corr4N s : ℚ) / 100 := by
  unfold repCorrFour corr4N; split_ifs <;> norm_num

/-- `2^{16} 10^6 2^s ∑_{j=0}^{15} W_j G(f_s, s - j)` in natural numbers. -/
def crossMainSmallN (s : ℕ) : ℕ :=
  ∑ j ∈ range 16, weightTableN.getD j 0 * exitN (bkExitWidth s) ((s : ℤ) - j) * 2 ^ j

/-- The check, in natural numbers, that `61817834604121 / 268435456000000` is at most the lower
bound `A / (2^{16} 10^6 2^s) + r R_2 / (2^{16} b 2^s) + 3 c_4 R_3 / (200 · 2^s)` of `crossingQ s`,
where `A = crossMainSmallN s`, `R_i = exitN f_s (s - i)`, `r = corr3N s`, `c_4 = corr4N s` and
`b = 7 · 10^6 · 2^s`. -/
def crossSmallN (s : ℕ) : Bool :=
  Nat.ble (61817834604121 * (65536000000 * 65536 * (7 * 10 ^ 6 * 2 ^ s) * 200 * 2 ^ s))
    (268435456000000 * (crossMainSmallN s * 65536 * (7 * 10 ^ 6 * 2 ^ s) * 200 +
      65536000000 * 200 * exitN (bkExitWidth s) ((s : ℤ) - 2) * corr3N s +
      65536000000 * 65536 * (7 * 10 ^ 6 * 2 ^ s) * 3 * corr4N s *
        exitN (bkExitWidth s) ((s : ℤ) - 3)))

/-- A passing check `crossSmallN s` gives the bound on `crossingQ s`. -/
theorem le_crossingQ_of_crossSmallN {s : ℕ} (h : crossSmallN s = true) :
    (61817834604121 / 268435456000000 : ℚ) ≤ crossingQ s := by
  have h' := Nat.le_of_ble_eq_true h
  have ht : (0 : ℚ) < 2 ^ s := by positivity
  have hE : ∀ j : ℕ, exitSumQ (bkExitWidth s) ((s : ℤ) - j) =
      (exitN (bkExitWidth s) ((s : ℤ) - j) : ℚ) * 2 ^ j / 2 ^ s := fun j => by
    rw [eq_div_iff ht.ne', exitSumQ_mul_two_pow]
  have hmain : ∑ j ∈ range 16, weightTable.getD j 0 * exitSumQ (bkExitWidth s) ((s : ℤ) - j) =
      (crossMainSmallN s : ℚ) / (65536000000 * 2 ^ s) := by
    rw [crossMainSmallN, Nat.cast_sum, div_eq_mul_inv, sum_mul]
    refine sum_congr rfl fun j hj => ?_
    rw [weightTable_eq j hj, hE j]
    push_cast
    field_simp
    ring
  have h4 : 3 / 16 * repCorrFour s * exitSumQ (bkExitWidth s) ((s : ℤ) - 3) =
      3 * corr4N s * exitN (bkExitWidth s) ((s : ℤ) - 3) / (200 * 2 ^ s) := by
    rw [repCorrFour_eq_corr4N, show ((s : ℤ) - 3) = (s : ℤ) - (3 : ℕ) by norm_num, hE 3]
    field_simp
    ring
  have hc := corr3N_le s
  have e2 := hE 2
  simp only [Nat.cast_ofNat] at e2
  rw [crossingQ, hmain, h4, e2]
  generalize crossMainSmallN s = A at h' ⊢
  generalize corr3N s = r at h' hc
  generalize corr4N s = c at h' ⊢
  generalize exitN (bkExitWidth s) ((s : ℤ) - 2) = R at h' ⊢
  generalize exitN (bkExitWidth s) ((s : ℤ) - 3) = E at h' ⊢
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = 7 * 10 ^ 6 * 2 ^ s := ⟨_, rfl⟩
  rw [← hb] at h' hc
  have hb0 : (0 : ℚ) < b := by rw [hb]; positivity
  have hc' : (61817834604121 : ℚ) * (65536000000 * 65536 * b * 200 * 2 ^ s) ≤
      268435456000000 * (A * 65536 * b * 200 + 65536000000 * 200 * R * r +
        65536000000 * 65536 * b * 3 * c * E) := by
    exact_mod_cast h'
  have hR : (0 : ℚ) ≤ (R : ℚ) * 2 ^ 2 / 2 ^ s :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by norm_num)) ht.le
  have h3 : (r : ℚ) / (65536 * b) * ((R : ℚ) * 2 ^ 2 / 2 ^ s) ≤
      repCorrThree s * ((R : ℚ) * 2 ^ 2 / 2 ^ s) := mul_le_mul_of_nonneg_right hc hR
  have key : (61817834604121 / 268435456000000 : ℚ) ≤ A / (65536000000 * 2 ^ s) +
      r / (65536 * b) * ((R : ℚ) * 2 ^ 2 / 2 ^ s) * (1 / 4) + 3 * c * E / (200 * 2 ^ s) := by
    rw [show A / (65536000000 * 2 ^ s) + r / (65536 * b) * ((R : ℚ) * 2 ^ 2 / 2 ^ s) * (1 / 4) +
        3 * c * E / (200 * 2 ^ s) = (A * 65536 * b * 200 + 65536000000 * 200 * R * r +
          65536000000 * 65536 * b * 3 * c * E) / (65536000000 * 65536 * b * 200 * 2 ^ s) by
      field_simp; ring]
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    linarith
  linarith [key, h3]

/-- For `2 ≤ s ≤ 16` with `s ∉ crossingExceptions`,
`61817834604121 / 268435456000000 ≤ crossingQ s`. -/
theorem le_crossingQ_2_16 : ∀ s ∈ Icc 2 16, s ∉ crossingExceptions →
    (61817834604121 / 268435456000000 : ℚ) ≤ crossingQ s := by
  have hN : ∀ s ∈ Icc 2 16, s ∉ crossingExceptions → crossSmallN s = true := by decide +kernel
  exact fun s hs hne => le_crossingQ_of_crossSmallN (hN s hs hne)

/-- For `17 ≤ s ≤ 511`, either `s = 19` or the check `crossN s` passes. -/
theorem crossN_17_511 : ∀ s ∈ Icc 17 511, s = 19 ∨ crossN s = true := by
  decide +kernel

/-- `61817834604121 / 268435456000000 ≤ crossingFastQ 19`. -/
theorem le_crossingFastQ_19 : (61817834604121 / 268435456000000 : ℚ) ≤ crossingFastQ 19 := by
  rw [← crossingQ_eq_crossingFastQ (by norm_num)]
  exact le_crossingQ_of_crossSmallN (by decide +kernel)

/-- **The decrement at the remaining small gaps.** For `2 ≤ s ≤ 511` with
`s ∉ {3, 6, 9, 13, 16}`, `D_cr(s) ≥ 61817834604121 / 268435456000000`. -/
@[collatz_pos_dens "lem_tr_D_small"]
theorem le_trDirectCrossing_of_le_511 {s : ℕ} (hs₂ : 2 ≤ s) (hs : s ≤ 511)
    (hne : s ∉ ({3, 6, 9, 13, 16} : Finset ℕ)) :
    (61817834604121 / 268435456000000 : ℝ) ≤ trDirectCrossing s := by
  have h : (61817834604121 / 268435456000000 : ℚ) ≤ crossingQ s := by
    by_cases h₁ : s ≤ 16
    · exact le_crossingQ_2_16 s (mem_Icc.2 ⟨hs₂, h₁⟩) hne
    rw [crossingQ_eq_crossingFastQ (by omega)]
    rcases crossN_17_511 s (mem_Icc.2 ⟨by omega, hs⟩) with rfl | h₂
    · exact le_crossingFastQ_19
    · exact le_crossingFastQ_of_crossN (by omega) h₂
  rw [trDirectCrossing_eq_crossingQ,
    show (61817834604121 / 268435456000000 : ℝ) = ((61817834604121 / 268435456000000 : ℚ) : ℝ)
      by norm_num]
  exact Rat.cast_le.2 h

end CollatzPosDens
