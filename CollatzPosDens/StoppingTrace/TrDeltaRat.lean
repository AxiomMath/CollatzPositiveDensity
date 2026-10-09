/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnP3
public import CollatzPosDens.Renewal.RnP45
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnRawMassFormula
public import CollatzPosDens.StoppingTrace.TrDelta
public import CollatzPosDens.StoppingTrace.TrE8
public import CollatzPosDens.Transfer.D
public import CollatzPosDens.Transfer.Gamma
public import CollatzPosDens.Transfer.Kappa

/-!
# Rational models of the exit masses and the passage surplus

The exit masses `p₄₅(s)` and `p₃(s)` are finite sums of raw-prefix masses `𝖱(k, t)`, with
`𝖱(0, t) = [t = 0]` and `𝖱(k, t) = binom(t - 1, 2k - 1) 2^{-t}` for `k ≥ 1` (zero when `t ≤ 0`).
Writing `N = ⌊(5s + 16)/16⌋ = K + 1`, the inner sum over the length is
`∑_{r=1}^{K+1} 𝖱(r - 1, t) = [t = 0] + 2^{-t} ∑_{k<K} binom(t - 1, 2k + 1)`, and only
`t ∈ [s - 4, s]` occurs. This file defines the resulting rationals `p₄₅^ℚ(s)`, `p₃^ℚ(s)` and the
`d_*`-free part of `δ_tr(s)`, and proves `p₄₅(s) = p₄₅^ℚ(s)` and `p₃(s) = p₃^ℚ(s)` for every `s`.

## Main results

* `CollatzPosDens.p45_eq_p45Q`, `CollatzPosDens.p3_eq_p3Q`: the exit masses are their rational
  models.
* `CollatzPosDens.trDeltaMassQ`: `E₈(γ_*) p₄₅^ℚ(s) + E₈(κ_* γ_*) p₃^ℚ(s)` as a rational.

## Implementation notes

The odd-index binomial sums `∑_{k<K} binom(m, 2k + 1)` are evaluated by walking along row `m`
of Pascal's triangle with the ratio `binom(m, j + 1) = binom(m, j) (m - j) / (j + 1)`, so each
row costs `O(K)` exact multiplications. The definitions are exposed and computable, so rational
inequalities about them can be decided by kernel evaluation (`decide +kernel`).
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- Walk along row `m` of Pascal's triangle: starting at column `j` with `cur = binom(m, j)`,
add `binom(m, j + 1), binom(m, j + 3), …` (`n` terms) to `acc`. -/
def oddChooseAux (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, acc => acc
  | n + 1, j, cur, acc =>
      oddChooseAux m n (j + 2) (cur * (m - j) / (j + 1) * (m - (j + 1)) / (j + 2))
        (acc + cur * (m - j) / (j + 1))

private theorem choose_succ_eq_div (m j : ℕ) :
    m.choose j * (m - j) / (j + 1) = m.choose (j + 1) := by
  rw [← Nat.choose_succ_right_eq, Nat.mul_div_cancel _ (Nat.succ_pos j)]

/-- Started at `cur = binom(m, j)`, `oddChooseAux` adds `∑_{i<n} binom(m, j + 2i + 1)` to `acc`. -/
theorem oddChooseAux_eq (m n : ℕ) : ∀ j acc,
    oddChooseAux m n j (m.choose j) acc = acc + ∑ i ∈ range n, m.choose (j + 2 * i + 1) := by
  induction n with
  | zero => intro j acc; simp [oddChooseAux]
  | succ n ih =>
    intro j acc
    rw [oddChooseAux, choose_succ_eq_div, choose_succ_eq_div, ih, sum_range_succ']
    simp only [mul_zero, add_zero]
    rw [add_assoc, add_comm (∑ _ ∈ _, _) _]
    congr 2
    refine sum_congr rfl fun i _ ↦ ?_
    congr 1
    ring

/-- The length-summed raw mass `[t = 0] + 2^{-t} ∑_{k<K} binom(t - 1, 2k + 1)` as a rational. -/
def rowMassQ (t : ℤ) (K : ℕ) : ℚ :=
  (if t = 0 then 1 else 0) + (oddChooseAux (t - 1).toNat K 0 1 0 : ℚ) / 2 ^ t.toNat

private theorem rawMass_succ_eq_div (k : ℕ) (t : ℤ) :
    rawMass (k + 1) t = ((t - 1).toNat.choose (2 * k + 1) : ℝ) / 2 ^ t.toNat := by
  rw [rawMass_eq_choose (by omega), show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
  rcases le_or_gt 0 t with ht | ht
  · rw [zpow_neg, ← Int.toNat_of_nonneg ht, zpow_natCast, div_eq_mul_inv, Int.toNat_natCast]
  · rw [show (t - 1).toNat = 0 by omega, Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- The raw masses `𝖱(r - 1, t)` summed over lengths `1 ≤ r ≤ K + 1` equal `rowMassQ t K`. -/
theorem sum_Icc_rawMass_eq_rowMassQ (t : ℤ) (K : ℕ) :
    ∑ r ∈ Icc 1 (K + 1), rawMass (r - 1) t = (rowMassQ t K : ℝ) := by
  have h := oddChooseAux_eq (t - 1).toNat K 0 0
  rw [Nat.choose_zero_right] at h
  rw [rowMassQ, h]
  simp only [zero_add]
  clear h
  induction K with
  | zero => simp [rawMass_zero]; split_ifs <;> simp
  | succ K ih =>
    rw [sum_Icc_succ_top (by omega), ih, Nat.add_sub_cancel, rawMass_succ_eq_div,
      sum_range_succ]
    push_cast
    ring_nf

/-- The rational model of `p₄₅(s)`. -/
def p45Q (s : ℕ) : ℚ :=
  3 / 16 * (rowMassQ ((s : ℤ) - 3) ((5 * s + 16) / 16 - 1) +
      rowMassQ ((s : ℤ) - 2) ((5 * s + 16) / 16 - 1) +
      rowMassQ ((s : ℤ) - 1) ((5 * s + 16) / 16 - 1) + rowMassQ s ((5 * s + 16) / 16 - 1)) +
    1 / 8 * (rowMassQ ((s : ℤ) - 4) ((5 * s + 16) / 16 - 1) +
      rowMassQ ((s : ℤ) - 3) ((5 * s + 16) / 16 - 1) +
      rowMassQ ((s : ℤ) - 2) ((5 * s + 16) / 16 - 1) +
      rowMassQ ((s : ℤ) - 1) ((5 * s + 16) / 16 - 1))

/-- The rational model of `p₃(s)`. -/
def p3Q (s : ℕ) : ℚ :=
  1 / 4 * (rowMassQ ((s : ℤ) - 2) ((5 * s + 16) / 16 - 1) +
    rowMassQ ((s : ℤ) - 1) ((5 * s + 16) / 16 - 1) + rowMassQ s ((5 * s + 16) / 16 - 1))

/-- The exit mass `p₄₅(s)` equals its rational model `p₄₅^ℚ(s)`. -/
theorem p45_eq_p45Q (s : ℕ) : p45 s = (p45Q s : ℝ) := by
  have hN : (5 * s + 16) / 16 = ((5 * s + 16) / 16 - 1) + 1 := by omega
  rw [p45, hN]
  simp only [show Icc (4 : ℤ) 5 = {4, 5} by decide, show Icc (1 : ℤ) 4 = {1, 2, 3, 4} by decide]
  simp only [sum_insert (by decide : (4 : ℤ) ∉ ({5} : Finset ℤ)), sum_singleton,
    sum_insert (by decide : (1 : ℤ) ∉ ({2, 3, 4} : Finset ℤ)),
    sum_insert (by decide : (2 : ℤ) ∉ ({3, 4} : Finset ℤ)),
    sum_insert (by decide : (3 : ℤ) ∉ ({4} : Finset ℤ)), sum_Icc_rawMass_eq_rowMassQ,
    varpi_of_two_le (by norm_num : (2 : ℤ) ≤ 4), varpi_of_two_le (by norm_num : (2 : ℤ) ≤ 5)]
  rw [p45Q]
  push_cast
  ring_nf

/-- The exit mass `p₃(s)` equals its rational model `p₃^ℚ(s)`. -/
theorem p3_eq_p3Q (s : ℕ) : p3 s = (p3Q s : ℝ) := by
  have hN : (5 * s + 16) / 16 = ((5 * s + 16) / 16 - 1) + 1 := by omega
  rw [p3, hN]
  simp only [show Icc (1 : ℕ) 3 = {1, 2, 3} by decide]
  simp only [sum_insert (by decide : (1 : ℕ) ∉ ({2, 3} : Finset ℕ)),
    sum_insert (by decide : (2 : ℕ) ∉ ({3} : Finset ℕ)), sum_singleton, sum_Icc_rawMass_eq_rowMassQ,
    varpi_of_two_le (by norm_num : (2 : ℤ) ≤ 3)]
  rw [p3Q]
  push_cast
  ring_nf

/-- The `d_*`-free part `E₈(γ_*) p₄₅(s) + E₈(κ_* γ_*) p₃(s)` of `δ_tr(s)`, as a rational. -/
def trDeltaMassQ (s : ℕ) : ℚ :=
  E8Q (87 / 200) * p45Q s + E8Q (4 / 25 * (87 / 200)) * p3Q s

end CollatzPosDens
