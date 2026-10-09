/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnCrossP
public import CollatzPosDens.Renewal.RnPascal
public import CollatzPosDens.Renewal.RnRawMass
public import CollatzPosDens.Renewal.RnPascalTail
public import CollatzPosDens.Renewal.RnRawMassFormula

/-!
# Mass of words straddling a height

For `t, j ∈ ℕ`, a word `c = (c₁, …, c_{j+1}) ∈ ℤ^{j+1}` with all letters `c_i ≥ 2` *straddles* the
height `t` if `c₁ + ⋯ + c_j ≤ t < c₁ + ⋯ + c_{j+1}`. The total Pascal weight of the straddling
words is the straddle weight:
`∑ ∏_{i=1}^{j+1} ϖ(c_i) = p_t(j) = binom(t + 1, 2j + 1) 2^{-t}`.

The proof splits according to the height `h = c₁ + ⋯ + c_j ∈ {0, …, t}` of the first `j` letters.
For a fixed prefix the admissible last letters are those with `c_{j+1} > t - h`, of total weight
`(t - h + 1) 2^{-(t-h)}`; summing the prefixes of height `h` gives the raw-prefix mass `𝖱(j, h)`.
Hence the left side is `∑_{h=0}^t 𝖱(j, h) (t - h + 1) 2^{-(t-h)}`, which the closed form of `𝖱`
and two applications of the hockey-stick identity evaluate to `binom(t + 1, 2j + 1) 2^{-t}`.

## Main definitions

* `CollatzPosDens.straddleWords`: the set of straddling words.

## Main results

* `CollatzPosDens.hasSum_straddleWords`: the weights of the straddling words sum to
  `p_t(j)`, as an unconditionally convergent series over `ℤ^{j+1}`.
* `CollatzPosDens.summable_straddleWords`, `CollatzPosDens.tsum_straddleWords`: the same
  identity for the `tsum`.

## Implementation notes

The set of straddling words is infinite (the last letter is unbounded), so the sum over them is
formalized as the series over `ℤ^{j+1} = (Fin (j + 1) → ℤ)` of the weight `∏ ϖ(c_i)` restricted
to the straddling words, in the strong (`HasSum`) form.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §6.5.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The words `c ∈ ℤ^{j+1}` with every letter `c_i ≥ 2` straddling the height `t`, that is
`c₁ + ⋯ + c_j ≤ t < c₁ + ⋯ + c_{j+1}`. -/
def straddleWords (t j : ℕ) : Set (Fin (j + 1) → ℤ) :=
  {c | (∀ i, 2 ≤ c i) ∧ ∑ i : Fin j, c i.castSucc ≤ t ∧ (t : ℤ) < ∑ i, c i}

/-- A word `c` lies in `straddleWords t j` if and only if every letter is at least `2` and
`c₁ + ⋯ + c_j ≤ t < c₁ + ⋯ + c_{j+1}`. -/
@[simp]
theorem mem_straddleWords {t j : ℕ} {c : Fin (j + 1) → ℤ} :
    c ∈ straddleWords t j ↔
      (∀ i, 2 ≤ c i) ∧ ∑ i : Fin j, c i.castSucc ≤ t ∧ (t : ℤ) < ∑ i, c i :=
  Iff.rfl

/-- The hockey-stick identity in the shifted form `∑_{h=0}^t binom(h - 1, k) = binom(t, k + 1)`,
for `k ≥ 1`. -/
private lemma sum_range_choose_pred {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    ∑ h ∈ range (t + 1), (h - 1).choose k = t.choose (k + 1) := by
  induction t with
  | zero => simp [Nat.choose_eq_zero_of_lt (show 0 < k by omega)]
  | succ t ih =>
    rw [sum_range_succ, ih, Nat.add_sub_cancel, Nat.choose_succ_succ', add_comm]

/-- The double hockey-stick identity `∑_{h=0}^t binom(h - 1, k) (t - h + 1) = binom(t + 1, k + 2)`,
for `k ≥ 1`. -/
private lemma sum_range_choose_pred_mul {k : ℕ} (hk : 1 ≤ k) (t : ℕ) :
    ∑ h ∈ range (t + 1), (h - 1).choose k * (t - h + 1) = (t + 1).choose (k + 2) := by
  induction t with
  | zero =>
    simp [Nat.choose_eq_zero_of_lt (show 0 < k by omega),
      Nat.choose_eq_zero_of_lt (show 1 < k + 2 by omega)]
  | succ t ih =>
    rw [sum_range_succ, Nat.add_sub_cancel, Nat.sub_self]
    have : ∑ h ∈ range (t + 1), (h - 1).choose k * (t + 1 - h + 1) =
        ∑ h ∈ range (t + 1), (h - 1).choose k * (t - h + 1) +
          ∑ h ∈ range (t + 1), (h - 1).choose k := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun h hh ↦ ?_
      rw [mem_range] at hh
      rw [show t + 1 - h + 1 = (t - h + 1) + 1 by omega, mul_add, mul_one]
    rw [this, ih, sum_range_choose_pred hk, Nat.choose_succ_succ' (t + 1) (k + 1),
      Nat.choose_succ_succ' t k]
    ring

/-- The height decomposition: `∑_{h=0}^t 𝖱(j, h) (t - h + 1) 2^{-(t-h)} = p_t(j)`. -/
private lemma sum_rawMass_mul_tail (t j : ℕ) :
    ∑ h ∈ range (t + 1), rawMass j h * ((((t - h : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (-((t - h : ℕ) : ℤ)))
      = straddleWeight t j := by
  rw [straddleWeight_natCast]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [sum_eq_single 0]
    · simp [rawMass_zero, zpow_neg, zpow_natCast, div_eq_mul_inv]
    · intro h _ h0
      simp [rawMass_zero, h0]
    · simp
  · have key := sum_range_choose_pred_mul (k := 2 * j - 1) (by omega) t
    rw [show 2 * j - 1 + 2 = 2 * j + 1 by omega] at key
    rw [← key, Nat.cast_sum, div_eq_mul_inv, sum_mul]
    refine sum_congr rfl fun h hh ↦ ?_
    rw [mem_range] at hh
    rw [rawMass_eq_choose hj, show ((h : ℤ) - 1).toNat = h - 1 by omega]
    have e : (2 : ℝ) ^ (-(h : ℤ)) * (2 : ℝ) ^ (-((t - h : ℕ) : ℤ)) = ((2 : ℝ) ^ t)⁻¹ := by
      rw [← zpow_add₀ (by norm_num), show -(h : ℤ) + -((t - h : ℕ) : ℤ) = -(t : ℤ) by omega,
        zpow_neg, zpow_natCast]
    rw [← e]
    push_cast [Nat.cast_sub (show h ≤ t by omega)]
    ring

/-- **Mass of words straddling a height.** For `t, j ∈ ℕ`, the Pascal weights
`∏_{i=1}^{j+1} ϖ(c_i)` of the words `c ∈ ℤ^{j+1}` with all letters `≥ 2` and
`c₁ + ⋯ + c_j ≤ t < c₁ + ⋯ + c_{j+1}` sum to the straddle weight `p_t(j)`. -/
@[collatz_pos_dens "lem_rn_straddle"]
theorem hasSum_straddleWords (t j : ℕ) :
    HasSum ((straddleWords t j).indicator fun c ↦ ∏ i, varpi (c i)) (straddleWeight t j) := by
  rw [← sum_rawMass_mul_tail, ← (Fin.snocEquiv fun _ : Fin (j + 1) ↦ ℤ).hasSum_iff]
  simp only [rawMass, sum_mul]
  set G : ℕ → (Fin j → ℤ) → ℤ × (Fin j → ℤ) → ℝ := fun h d p ↦
    if p.2 = d then (∏ i, varpi (d i)) * (Set.Ioi ((t - h : ℕ) : ℤ)).indicator varpi p.1 else 0
    with hG
  have hsum : ∀ h ∈ range (t + 1), ∀ d ∈ rawWords j h, HasSum (G h d)
      ((∏ i, varpi (d i)) * ((((t - h : ℕ) : ℝ) + 1) * (2 : ℝ) ^ (-((t - h : ℕ) : ℤ)))) := by
    intro h _ d _
    have hinj : Function.Injective fun b : ℤ ↦ (b, d) := fun _ _ e ↦ (Prod.ext_iff.1 e).1
    rw [← hinj.hasSum_iff]
    · convert (hasSum_varpi_indicator_Ioi (t - h)).mul_left (∏ i, varpi (d i)) using 1
      funext b
      simp [hG]
    · rintro ⟨b, d'⟩ hp
      simp only [hG]
      split_ifs with hd
      · subst hd
        exact absurd ⟨b, rfl⟩ hp
      · rfl
  convert hasSum_sum fun h hh ↦ hasSum_sum (hsum h hh) using 1
  ext ⟨b, d⟩
  have he : (Fin.snocEquiv fun _ : Fin (j + 1) ↦ ℤ) (b, d) = Fin.snoc d b :=
    funext fun x ↦ Fin.snocEquiv_apply _ _ x
  simp only [hG, Function.comp_apply, he, sum_ite_eq, mem_rawWords]
  by_cases h2 : ∀ i, 2 ≤ d i
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, ∑ i, d i = n :=
      ⟨(∑ i, d i).toNat, (Int.toNat_of_nonneg (sum_nonneg fun i _ ↦ by linarith [h2 i])).symm⟩
    simp only [h2, hn, Nat.cast_inj]
    simp only [Set.indicator, mem_straddleWords, Fin.forall_fin_succ',
      Fin.snoc_castSucc, Fin.snoc_last, Fin.sum_univ_castSucc, Fin.prod_univ_castSucc, hn, h2,
      Set.mem_Ioi, implies_true, true_and, sum_ite_eq, mem_range]
    by_cases hnt : n ≤ t
    · rw [ite_eq_left (by omega : n < t + 1), Nat.cast_sub hnt]
      by_cases hb : (t : ℤ) - n < b
      · rw [ite_eq_left hb]
        by_cases hb2 : 2 ≤ b
        · rw [ite_eq_left ⟨hb2, by omega, by omega⟩]
        · rw [ite_eq_right (fun h ↦ hb2 h.1), varpi_of_le_one (by omega), mul_zero]
      · rw [ite_eq_right hb, ite_eq_right (by omega), mul_zero]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · simp only [h2, false_and, ite_false, sum_const_zero]
    rw [Set.indicator_of_notMem]
    simp only [mem_straddleWords, Fin.forall_fin_succ', Fin.snoc_castSucc, not_and]
    exact fun h _ ↦ absurd h.1 h2

/-- The weights of the straddling words are summable. -/
theorem summable_straddleWords (t j : ℕ) :
    Summable ((straddleWords t j).indicator fun c ↦ ∏ i, varpi (c i)) :=
  (hasSum_straddleWords t j).summable

/-- **Mass of words straddling a height**, as a `tsum`. -/
theorem tsum_straddleWords (t j : ℕ) :
    ∑' c, (straddleWords t j).indicator (fun c ↦ ∏ i, varpi (c i)) c = straddleWeight t j :=
  (hasSum_straddleWords t j).tsum_eq

end CollatzPosDens
