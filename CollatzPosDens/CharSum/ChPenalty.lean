/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.SpecialFunctions.Exp
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChPaidReward
public import CollatzPosDens.Transfer.S02Z

/-!
# The penalty of a letter sequence

Fix `n`, `ξ ∈ G_n` and `ε`, and let `R_c(p)` be the paid reward. For a word
`b = (b₁, …, b_k)` of integers, the *penalty* of `b` is
`Pen(b) = ∏_{i=1}^{k} exp (-z_* R_{b_i}((i, b₁ + ⋯ + b_i)))`,
the empty product being `1`.

## Main definitions

* `CollatzPosDens.chPenaltyFrom n ξ ε j s b`: the shifted penalty, in which the point
  attached to the letter `b_i` is `(j + i, s + b₁ + ⋯ + b_i)`.
* `CollatzPosDens.chPenalty n ξ ε b`: the penalty `Pen(b)`.

## Main results

* `CollatzPosDens.chPenalty_def`: `Pen(b)` as an explicit product over `0`-based indices.
* `CollatzPosDens.chPenaltyFrom_nil`, `CollatzPosDens.chPenaltyFrom_cons`,
  `CollatzPosDens.chPenalty_nil`, `CollatzPosDens.chPenalty_cons`: the recursion on the
  first letter.
* `CollatzPosDens.chPenaltyFrom_append`, `CollatzPosDens.chPenalty_append`: the penalty
  of a concatenation `b c` is `Pen(b)` times the penalty of `c` shifted by `(|b|, Σ b)`.
* `CollatzPosDens.chPenalty_pos`, `CollatzPosDens.chPenalty_le_one`:
  `0 < Pen(b) ≤ 1`.

## Implementation notes

The parameters `n`, `ξ` and `ε`, suppressed in the source, are explicit. Words are `List ℤ`,
indexed from `0`, so the source's letter `b_i` is `b.getD (i - 1) 0`. To state the behaviour
under concatenation the penalty is defined as the case `j = s = 0` of a penalty shifted by a
starting index `j` and a starting height `s`.

## References

* [Mazur, *Collatz positive density*], §7.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The penalty shifted by an index `j` and a height `s`:
`∏_{i=1}^{k} exp (-z_* R_{b_i}((j + i, s + b₁ + ⋯ + b_i)))`. -/
noncomputable def chPenaltyFrom (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ) (b : List ℤ) :
    ℝ :=
  ∏ i ∈ Finset.range b.length,
    Real.exp (-(zStar : ℝ) *
      chPaidReward n ξ ε (b.getD i 0) (j + (i + 1 : ℕ), s + (b.take (i + 1)).sum))

/-- The penalty of a word `b = (b₁, …, b_k)`:
`Pen(b) = ∏_{i=1}^{k} exp (-z_* R_{b_i}((i, b₁ + ⋯ + b_i)))` (the empty product is `1`). -/
@[collatz_pos_dens "def_ch_penalty"]
noncomputable def chPenalty (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (b : List ℤ) : ℝ :=
  chPenaltyFrom n ξ ε 0 0 b

/-- `Pen(b)` as an explicit product over `0`-based indices `i`: the letter `b.getD i 0`
contributes `exp (-z_* R_{b_{i+1}}((i + 1, b₁ + ⋯ + b_{i+1})))`. -/
theorem chPenalty_def (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (b : List ℤ) :
    chPenalty n ξ ε b =
      ∏ i ∈ Finset.range b.length,
        Real.exp (-(zStar : ℝ) *
          chPaidReward n ξ ε (b.getD i 0) ((i + 1 : ℕ), (b.take (i + 1)).sum)) := by
  simp [chPenalty, chPenaltyFrom]

/-- The shifted penalty of the empty word is `1`. -/
@[simp]
theorem chPenaltyFrom_nil (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ) :
    chPenaltyFrom n ξ ε j s [] = 1 := by
  simp [chPenaltyFrom]

/-- The shifted penalty of `a :: b`: the first letter contributes
`exp (-z_* R_a((j + 1, s + a)))`, and the rest is the penalty of `b` shifted to
`(j + 1, s + a)`. -/
theorem chPenaltyFrom_cons (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s a : ℤ) (b : List ℤ) :
    chPenaltyFrom n ξ ε j s (a :: b) =
      Real.exp (-(zStar : ℝ) * chPaidReward n ξ ε a (j + 1, s + a)) *
        chPenaltyFrom n ξ ε (j + 1) (s + a) b := by
  simp only [chPenaltyFrom, List.length_cons, Finset.prod_range_succ']
  rw [mul_comm]
  congr 1
  · simp
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
    congr 4
    · push_cast
      ring
    · ring

/-- The penalty of the empty word is `1`. -/
@[simp]
theorem chPenalty_nil (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) : chPenalty n ξ ε [] = 1 := by
  simp [chPenalty]

/-- The penalty of `a :: b`: the first letter contributes `exp (-z_* R_a((1, a)))`, and the
rest is the penalty of `b` shifted to `(1, a)`. -/
theorem chPenalty_cons (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (a : ℤ) (b : List ℤ) :
    chPenalty n ξ ε (a :: b) =
      Real.exp (-(zStar : ℝ) * chPaidReward n ξ ε a (1, a)) * chPenaltyFrom n ξ ε 1 a b := by
  simp only [chPenalty, chPenaltyFrom_cons, zero_add]

/-- The shifted penalty of a concatenation `b ++ c` is the product of the shifted penalty of `b`
and the penalty of `c` shifted further by `(|b|, Σ b)`. -/
theorem chPenaltyFrom_append (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ) (b c : List ℤ) :
    chPenaltyFrom n ξ ε j s (b ++ c) =
      chPenaltyFrom n ξ ε j s b * chPenaltyFrom n ξ ε (j + b.length) (s + b.sum) c := by
  induction b generalizing j s with
  | nil => simp
  | cons a b ih =>
    have hj : j + 1 + (b.length : ℤ) = j + ((a :: b).length : ℕ) := by
      push_cast [List.length_cons]
      ring
    have hs : s + a + b.sum = s + (a :: b).sum := by simp [add_assoc]
    rw [List.cons_append, chPenaltyFrom_cons, chPenaltyFrom_cons, ih, hj, hs]
    ring

/-- The penalty of a concatenation `b ++ c` is `Pen(b)` times the penalty of `c` shifted by
`(|b|, Σ b)`. -/
theorem chPenalty_append (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (b c : List ℤ) :
    chPenalty n ξ ε (b ++ c) =
      chPenalty n ξ ε b * chPenaltyFrom n ξ ε b.length b.sum c := by
  simp [chPenalty, chPenaltyFrom_append]

/-- The shifted penalty is positive. -/
theorem chPenaltyFrom_pos (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ) (b : List ℤ) :
    0 < chPenaltyFrom n ξ ε j s b :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

/-- The shifted penalty is at most `1`. -/
theorem chPenaltyFrom_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ) (b : List ℤ) :
    chPenaltyFrom n ξ ε j s b ≤ 1 := by
  have hz : (0 : ℝ) ≤ zStar := by exact_mod_cast zStar_pos.le
  refine Finset.prod_le_one₀ (fun _ _ => (Real.exp_pos _).le) fun _ _ => ?_
  refine Real.exp_le_one_iff.2 ?_
  rw [neg_mul]
  exact neg_nonpos.2 (mul_nonneg hz chPaidReward_nonneg)

/-- The penalty is positive. -/
theorem chPenalty_pos (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (b : List ℤ) :
    0 < chPenalty n ξ ε b :=
  chPenaltyFrom_pos _ _ _ _ _ _

/-- The penalty is at most `1`. -/
theorem chPenalty_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (b : List ℤ) :
    chPenalty n ξ ε b ≤ 1 :=
  chPenaltyFrom_le_one _ _ _ _ _ _

end CollatzPosDens
