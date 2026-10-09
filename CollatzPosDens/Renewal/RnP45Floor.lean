/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnRawMassFormula
public import CollatzPosDens.Renewal.RnP45Large

/-!
# A uniform floor for the closing exit mass

For every `s ∈ ℕ`, the closing exit mass satisfies `p₄₅(s) ≥ 3/16`.

For `s ≥ 256` this follows from the large-gap bound `p₄₅(s) ≥ 5/16 - 125/(8s)`. For `s ≤ 255`,
`p₄₅(s)` is a finite sum of rationals: by the closed form of the raw-prefix mass,
`𝖱(k, t) 2^t` is `[t = 0]` for `k = 0` and `binom(t - 1, 2k - 1)` for `k ≥ 1`, `t ≥ 0`, and
`𝖱(k, t) = 0` for `t < 0`. With `ϖ(4) = 3/16` and `ϖ(5) = 2/16` this gives
`p₄₅(s) = N(s) / (16 · 2^s)` for an explicit natural number `N(s)`, and the inequality
`3 · 2^s ≤ N(s)` is checked exactly for each of the `256` values `s ≤ 255`. Equality holds at
`s = 0`, and the minimum over `1 ≤ s ≤ 255` is `p₄₅(6) = 227/1024`.

## Main results

* `CollatzPosDens.three_div_sixteen_le_p45`: `3/16 ≤ p₄₅(s)` for every `s ∈ ℕ`.

## Implementation notes

The finite check runs on a computable natural-number mirror `N(s)` of `16 · 2^s · p₄₅(s)`, in
which binomial coefficients are computed through factorials and the sum over the length `r`
by a primitive recursion, and is discharged by kernel evaluation. The cases `s = 0` and
`1 ≤ s ≤ 255` are handled together by this check.

## References

* [Mazur, *Collatz positive density*], §6.6.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Binomial coefficients through factorials (a kernel-friendly form of `Nat.choose`). -/
private def chooseF (n k : ℕ) : ℕ :=
  if k ≤ n then n.factorial / (k.factorial * (n - k).factorial) else 0

private lemma chooseF_eq (n k : ℕ) : chooseF n k = n.choose k := by
  unfold chooseF
  split_ifs with h
  · exact (Nat.choose_eq_factorial_div_factorial h).symm
  · exact (Nat.choose_eq_zero_of_lt (by omega)).symm

/-- The numerator `2^t 𝖱(k, t)` for `t ∈ ℕ`. -/
private def rawNum (k t : ℕ) : ℕ :=
  if k = 0 then (if t = 0 then 1 else 0) else chooseF (t - 1) (2 * k - 1)

private lemma rawMass_natCast_eq (k t : ℕ) :
    rawMass k (t : ℤ) = (rawNum k t : ℝ) * (1 / 2) ^ t := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [rawMass_zero]
    by_cases ht : t = 0 <;> simp [rawNum, ht]
  · simp only [rawNum, hk.ne', ↓reduceIte]
    rw [rawMass_eq_choose hk, chooseF_eq,
      show ((t : ℤ) - 1).toNat = t - 1 by omega]
    simp [zpow_neg, one_div]

/-- `sumBelow g n = g 0 + ⋯ + g (n - 1)`, by primitive recursion. -/
private def sumBelow (g : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumBelow g n + g n

private lemma sumBelow_eq (g : ℕ → ℕ) (n : ℕ) : sumBelow g n = ∑ i ∈ range n, g i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumBelow, ih, sum_range_succ]

/-- The numerator `2^s ∑_{r=1}^{⌊(5s+16)/16⌋} 𝖱(r - 1, s - d)`. -/
private def innerNum (s d : ℕ) : ℕ :=
  if d ≤ s then sumBelow (fun j ↦ rawNum j (s - d)) ((5 * s + 16) / 16) * 2 ^ d else 0

private lemma inner_eq (s : ℕ) (O c : ℤ) (d : ℕ) (h : c - O = d) :
    ∑ r ∈ Icc 1 ((5 * s + 16) / 16), rawMass (r - 1) ((s : ℤ) + O - c) =
      (innerNum s d : ℝ) * (1 / 2) ^ s := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simp only [Nat.add_sub_cancel_left]
  unfold innerNum
  split_ifs with hd
  · rw [show (s : ℤ) + O - c = ((s - d : ℕ) : ℤ) by omega]
    simp_rw [rawMass_natCast_eq]
    rw [← sum_mul, sumBelow_eq]
    push_cast
    rw [mul_assoc]
    congr 1
    rw [show s = (s - d) + d by omega, pow_add, Nat.add_sub_cancel]
    rw [mul_comm ((1 / 2 : ℝ) ^ (s - d)), ← mul_assoc, ← mul_pow]
    norm_num
  · simp only [Nat.cast_zero, zero_mul]
    exact sum_eq_zero fun r _ ↦ rawMass_of_neg _ (by omega)

/-- The numerator `N(s) = 16 · 2^s · p₄₅(s)`. -/
private def p45Num (s : ℕ) : ℕ :=
  3 * (innerNum s 3 + innerNum s 2 + innerNum s 1 + innerNum s 0) +
    2 * (innerNum s 4 + innerNum s 3 + innerNum s 2 + innerNum s 1)

private lemma p45_eq (s : ℕ) : p45 s = (p45Num s : ℝ) / 16 * (1 / 2) ^ s := by
  have h5 : varpi 5 = 2 / 16 := by rw [varpi_five]; norm_num
  rw [p45, show Icc (4 : ℤ) 5 = {4, 5} by rfl, show Icc (1 : ℤ) 4 = {1, 2, 3, 4} by rfl]
  simp only [sum_insert (show (4 : ℤ) ∉ ({5} : Finset ℤ) by decide), sum_singleton,
    sum_insert (show (1 : ℤ) ∉ ({2, 3, 4} : Finset ℤ) by decide),
    sum_insert (show (2 : ℤ) ∉ ({3, 4} : Finset ℤ) by decide),
    sum_insert (show (3 : ℤ) ∉ ({4} : Finset ℤ) by decide)]
  rw [inner_eq s 1 4 3 (by norm_num), inner_eq s 2 4 2 (by norm_num),
    inner_eq s 3 4 1 (by norm_num), inner_eq s 4 4 0 (by norm_num),
    inner_eq s 1 5 4 (by norm_num), inner_eq s 2 5 3 (by norm_num),
    inner_eq s 3 5 2 (by norm_num), inner_eq s 4 5 1 (by norm_num), varpi_four, h5, p45Num]
  push_cast
  ring

set_option maxRecDepth 100000 in
private lemma p45Num_ge : ∀ s < 256, 3 * 2 ^ s ≤ p45Num s := by
  decide +kernel

/-- **A uniform floor for the closing exit mass.** For every `s ∈ ℕ`, `p₄₅(s) ≥ 3/16`. -/
@[collatz_pos_dens "lem_rn_p45_floor"]
theorem three_div_sixteen_le_p45 (s : ℕ) : 3 / 16 ≤ p45 s := by
  rcases lt_or_ge s 256 with hs | hs
  · have h : ((3 * 2 ^ s : ℕ) : ℝ) ≤ p45Num s := by exact_mod_cast p45Num_ge s hs
    rw [p45_eq]
    push_cast at h
    have h2 : (2 : ℝ) ^ s * (1 / 2) ^ s = 1 := by rw [← mul_pow]; norm_num
    have hp : (0 : ℝ) ≤ (1 / 2) ^ s := by positivity
    nlinarith
  · have h := p45_ge_of_le hs
    have hs' : (256 : ℝ) ≤ s := by exact_mod_cast hs
    have : 125 / (8 * (s : ℝ)) ≤ 2 / 16 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith

end CollatzPosDens
