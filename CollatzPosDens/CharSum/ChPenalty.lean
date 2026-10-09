/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import CollatzPosDens.Attr
public import CollatzPosDens.CharSum.ChRaw3Factor
public import CollatzPosDens.CharSum.ChWhiteFactor

/-!
# The penalty of a letter sequence

Fix `n`, `ξ ∈ G_n` and `ε`, let `w` be the white factor and `w₃` the raw-three factor. For a
word `b = (b₁, …, b_k)` of integers, the *penalty* of `b` is
`Pen(b) = ∏_{1 ≤ i ≤ k, b_i ∈ {4,5}} w(i, b₁ + ⋯ + b_i) ·
  ∏_{1 ≤ i ≤ k, b_i = 3} w₃(i, b₁ + ⋯ + b_i)`,
empty products being `1`.

## Main definitions

* `CollatzPosDens.chPenaltyFrom n ξ ε j s b`: the shifted penalty, in which the point
  attached to the letter `b_i` is `(j + i, s + b₁ + ⋯ + b_i)`.
* `CollatzPosDens.chPenalty n ξ ε b`: the penalty `Pen(b)`.

## Main results

* `CollatzPosDens.chPenalty_def`: `Pen(b)` is the product displayed above.
* `CollatzPosDens.chPenaltyFrom_nil`, `CollatzPosDens.chPenaltyFrom_cons`,
  `CollatzPosDens.chPenalty_nil`, `CollatzPosDens.chPenalty_cons`: the recursion on the
  first letter.
* `CollatzPosDens.chPenaltyFrom_append`, `CollatzPosDens.chPenalty_append`: the penalty
  of a concatenation `b c` is `Pen(b)` times the penalty of `c` shifted by `(|b|, Σ b)`.
* `CollatzPosDens.chPenalty_pos`, `CollatzPosDens.chPenalty_le_one`:
  `0 < Pen(b) ≤ 1`.

## Implementation notes

The parameters `n`, `ξ` and `ε`, suppressed in [mazur2026], are explicit. Words are `List ℤ`,
indexed from `0`, so the letter `b_i` is `b.getD (i - 1) 0`. To state the behaviour under
concatenation the penalty is defined as the case `j = s = 0` of a penalty shifted by a starting
index `j` and a starting height `s`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §7.2.
-/

@[expose] public section

namespace CollatzPosDens

/-- The penalty shifted by an index `j` and a height `s`:
`∏_{b_i ∈ {4,5}} w(j + i, s + b₁ + ⋯ + b_i) · ∏_{b_i = 3} w₃(j + i, s + b₁ + ⋯ + b_i)`. -/
noncomputable def chPenaltyFrom (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ) (b : List ℤ) :
    ℝ :=
  (∏ i ∈ (Finset.range b.length).filter (fun i => b.getD i 0 ∈ ({4, 5} : Finset ℤ)),
      chWhiteFactor n ξ ε (j + (i + 1 : ℕ), s + (b.take (i + 1)).sum)) *
    ∏ i ∈ (Finset.range b.length).filter (fun i => b.getD i 0 = 3),
      chRaw3Factor n ξ ε (j + (i + 1 : ℕ), s + (b.take (i + 1)).sum)

/-- The penalty of a word `b = (b₁, …, b_k)`:
`Pen(b) = ∏_{b_i ∈ {4,5}} w(i, b₁ + ⋯ + b_i) · ∏_{b_i = 3} w₃(i, b₁ + ⋯ + b_i)`
(empty products are `1`). -/
@[collatz_pos_dens "def_ch_penalty"]
noncomputable def chPenalty (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (b : List ℤ) : ℝ :=
  chPenaltyFrom n ξ ε 0 0 b

/-- `Pen(b)` is the product over the letters `b_i ∈ {4,5}` of `w` and over the letters `b_i = 3`
of `w₃`, written with `0`-based indices. -/
theorem chPenalty_def (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (b : List ℤ) :
    chPenalty n ξ ε b =
      (∏ i ∈ (Finset.range b.length).filter (fun i => b.getD i 0 ∈ ({4, 5} : Finset ℤ)),
          chWhiteFactor n ξ ε ((i + 1 : ℕ), (b.take (i + 1)).sum)) *
        ∏ i ∈ (Finset.range b.length).filter (fun i => b.getD i 0 = 3),
          chRaw3Factor n ξ ε ((i + 1 : ℕ), (b.take (i + 1)).sum) := by
  simp [chPenalty, chPenaltyFrom]

/-- The shifted penalty of the empty word is `1`. -/
@[simp]
theorem chPenaltyFrom_nil (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ) :
    chPenaltyFrom n ξ ε j s [] = 1 := by
  simp [chPenaltyFrom]

/-- The shifted penalty of `a :: b`: the first letter contributes `w(j + 1, s + a)` if
`a ∈ {4,5}` and `w₃(j + 1, s + a)` if `a = 3`, and the rest is the penalty of `b` shifted to
`(j + 1, s + a)`. -/
theorem chPenaltyFrom_cons (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s a : ℤ) (b : List ℤ) :
    chPenaltyFrom n ξ ε j s (a :: b) =
      (if a ∈ ({4, 5} : Finset ℤ) then chWhiteFactor n ξ ε (j + 1, s + a) else 1) *
        (if a = 3 then chRaw3Factor n ξ ε (j + 1, s + a) else 1) *
          chPenaltyFrom n ξ ε (j + 1) (s + a) b := by
  have key : ∀ (P : ℤ → Prop) [DecidablePred P] (f : ℤ × ℤ → ℝ),
      (∏ i ∈ (Finset.range (a :: b).length).filter (fun i => P ((a :: b).getD i 0)),
          f (j + (i + 1 : ℕ), s + ((a :: b).take (i + 1)).sum)) =
        (if P a then f (j + 1, s + a) else 1) *
          ∏ i ∈ (Finset.range b.length).filter (fun i => P (b.getD i 0)),
            f (j + 1 + (i + 1 : ℕ), s + a + (b.take (i + 1)).sum) := by
    intro P _ f
    simp only [Finset.prod_filter, List.length_cons, Finset.prod_range_succ']
    rw [mul_comm]
    congr 1
    · simp
    · refine Finset.prod_congr rfl fun i _ => ?_
      simp only [List.getD_cons_succ, List.take_succ_cons, List.sum_cons]
      congr 3
      · push_cast; ring
      · ring
  rw [chPenaltyFrom, chPenaltyFrom, key (· ∈ ({4, 5} : Finset ℤ)), key (· = 3)]
  ring

/-- The penalty of the empty word is `1`. -/
@[simp]
theorem chPenalty_nil (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) : chPenalty n ξ ε [] = 1 := by
  simp [chPenalty]

/-- The penalty of `a :: b`: the first letter contributes `w(1, a)` if `a ∈ {4,5}` and
`w₃(1, a)` if `a = 3`, and the rest is the penalty of `b` shifted to `(1, a)`. -/
theorem chPenalty_cons (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (a : ℤ) (b : List ℤ) :
    chPenalty n ξ ε (a :: b) =
      (if a ∈ ({4, 5} : Finset ℤ) then chWhiteFactor n ξ ε (1, a) else 1) *
        (if a = 3 then chRaw3Factor n ξ ε (1, a) else 1) * chPenaltyFrom n ξ ε 1 a b := by
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
      simp only [List.length_cons]; push_cast; ring
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
  mul_pos (Finset.prod_pos fun _ _ => chWhiteFactor_pos _ _ _ _)
    (Finset.prod_pos fun _ _ => chRaw3Factor_pos _ _ _ _)

/-- The shifted penalty is at most `1`. -/
theorem chPenaltyFrom_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (j s : ℤ) (b : List ℤ) :
    chPenaltyFrom n ξ ε j s b ≤ 1 := by
  have h₁ := Finset.prod_le_one₀ (s := (Finset.range b.length).filter
      (fun i => b.getD i 0 ∈ ({4, 5} : Finset ℤ)))
    (f := fun i => chWhiteFactor n ξ ε (j + (i + 1 : ℕ), s + (b.take (i + 1)).sum))
    (fun _ _ => chWhiteFactor_nonneg _ _ _ _) fun _ _ => chWhiteFactor_le_one _ _ _ _
  have h₂ := Finset.prod_le_one₀ (s := (Finset.range b.length).filter (fun i => b.getD i 0 = 3))
    (f := fun i => chRaw3Factor n ξ ε (j + (i + 1 : ℕ), s + (b.take (i + 1)).sum))
    (fun _ _ => chRaw3Factor_nonneg _ _ _ _) fun _ _ => chRaw3Factor_le_one _ _ _ _
  have h₃ := Finset.prod_nonneg (s := (Finset.range b.length).filter (fun i => b.getD i 0 = 3))
    (f := fun i => chRaw3Factor n ξ ε (j + (i + 1 : ℕ), s + (b.take (i + 1)).sum))
    fun _ _ => chRaw3Factor_nonneg _ _ _ _
  rw [chPenaltyFrom]
  nlinarith

/-- The penalty is positive. -/
theorem chPenalty_pos (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (b : List ℤ) :
    0 < chPenalty n ξ ε b :=
  chPenaltyFrom_pos _ _ _ _ _ _

/-- The penalty is at most `1`. -/
theorem chPenalty_le_one (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (b : List ℤ) :
    chPenalty n ξ ε b ≤ 1 :=
  chPenaltyFrom_le_one _ _ _ _ _ _

end CollatzPosDens
