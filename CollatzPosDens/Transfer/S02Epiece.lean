/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.S02Findex
public import CollatzPosDens.Transfer.Rstar
public import CollatzPosDens.Transfer.S02ClearCount
public import CollatzPosDens.Transfer.S02ClearExp
public import CollatzPosDens.Transfer.S02ClearExpPos
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.BigOperators

/-!
# The clearing allowance `E_piece`

Fix a Fourier index `ι ∈ {o, b}`. The `i`th clearing block contains `n^cl_i(ι)` times and is
damped by the factor `e^{-t^cl_i(ι)}`, where `t^cl_i(ι)` is the clearing exponent. For `t ≥ 0`
every term of the exponential series at `t` is nonnegative, so the degree-`80` partial sum
$$P_{80}(t) = \sum_{j=0}^{80} \frac{t^j}{j!}$$
is a rational lower bound for `e^t`, and the contribution of the `i`th block is paid with
`n^cl_i(ι) / P_80(t^cl_i(ι))`, rounded up to a multiple of `10^{-24}`. The clearing allowance is
the sum of these rounded contributions over the trace times,
$$E_{\mathrm{piece}}(ι) := \sum_{i=0}^{r_*(ι)} 10^{-24}
  \Bigl\lceil \frac{10^{24}\, n^{\mathrm{cl}}_i(ι)}{P_{80}(t^{\mathrm{cl}}_i(ι))} \Bigr\rceil
  \in ℚ .$$

## Main definitions

* `CollatzPosDens.expPartialSum`: the degree-`n` partial sum `∑_{j=0}^{n} t^j / j!` of the
  exponential series.
* `CollatzPosDens.ePiece`: the clearing allowance `E_piece(ι)`.

## Main results

* `CollatzPosDens.one_le_expPartialSum`, `CollatzPosDens.expPartialSum_pos`: for `0 ≤ t`,
  `0 < 1 ≤ ∑_{j=0}^{n} t^j / j!`.
* `CollatzPosDens.ratCast_expPartialSum`: the partial sum commutes with the cast `ℚ → K`.
* `CollatzPosDens.ePiece_def`: the defining formula of `E_piece(ι)`.
* `CollatzPosDens.ePiece_nonneg`: `0 ≤ E_piece(ι)`.

## Implementation notes

The factor `10^{-24}` is written as division by `10^24`, and the ceiling is the integer ceiling
`Int.ceil` on `ℚ`. Since the clearing counts and exponents involve real ceilings, `E_piece(ι)` is
a `noncomputable` rational number.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The degree-`n` partial sum `∑_{j=0}^{n} t^j / j!` of the exponential series. -/
def expPartialSum {K : Type*} [DivisionRing K] (n : ℕ) (t : K) : K :=
  ∑ j ∈ range (n + 1), t ^ j / (j.factorial : K)

/-- Unfolding lemma for the partial sum of the exponential series. -/
theorem expPartialSum_def {K : Type*} [DivisionRing K] (n : ℕ) (t : K) :
    expPartialSum n t = ∑ j ∈ range (n + 1), t ^ j / (j.factorial : K) := rfl

/-- The degree-`0` partial sum is `1`. -/
@[simp]
theorem expPartialSum_zero {K : Type*} [DivisionRing K] (t : K) : expPartialSum 0 t = 1 := by
  simp [expPartialSum]

/-- Adding the next term of the exponential series. -/
theorem expPartialSum_succ {K : Type*} [DivisionRing K] (n : ℕ) (t : K) :
    expPartialSum (n + 1) t = expPartialSum n t + t ^ (n + 1) / ((n + 1).factorial : K) := by
  simp only [expPartialSum, sum_range_succ _ (n + 1)]

/-- The partial sum of the exponential series commutes with the cast from `ℚ`. -/
@[simp, norm_cast]
theorem ratCast_expPartialSum {K : Type*} [DivisionRing K] [CharZero K] (n : ℕ) (t : ℚ) :
    ((expPartialSum n t : ℚ) : K) = expPartialSum n (t : K) := by
  simp [expPartialSum]

/-- For `0 ≤ t`, the partial sum `∑_{j=0}^{n} t^j / j!` is at least its constant term `1`. -/
theorem one_le_expPartialSum {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) {t : K} (ht : 0 ≤ t) : 1 ≤ expPartialSum n t := by
  rw [expPartialSum, sum_range_succ']
  have h : 0 ≤ ∑ j ∈ range n, t ^ (j + 1) / ((j + 1).factorial : K) :=
    sum_nonneg fun j _ => div_nonneg (pow_nonneg ht _) (Nat.cast_nonneg _)
  simpa using h

/-- For `0 ≤ t`, the partial sum `∑_{j=0}^{n} t^j / j!` is positive. -/
theorem expPartialSum_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) {t : K} (ht : 0 ≤ t) : 0 < expPartialSum n t :=
  zero_lt_one.trans_le (one_le_expPartialSum n ht)

/-- The clearing allowance
`E_piece(ι) := ∑_{i=0}^{r_*(ι)} 10^{-24} ⌈10^24 n^cl_i(ι) / P_80(t^cl_i(ι))⌉ ∈ ℚ`, where
`P_80(t) = ∑_{j=0}^{80} t^j / j!`. -/
@[collatz_pos_dens "def_s02_Epiece"]
noncomputable def ePiece (ι : FIndex) : ℚ :=
  ∑ i ∈ range (rStar ι + 1),
    (⌈10 ^ 24 * (clearCount ι i : ℚ) / expPartialSum 80 (clearingExponent ι i)⌉ : ℚ) / 10 ^ 24

/-- The defining formula of the clearing allowance. -/
theorem ePiece_def (ι : FIndex) :
    ePiece ι = ∑ i ∈ range (rStar ι + 1),
      (⌈10 ^ 24 * (clearCount ι i : ℚ) / expPartialSum 80 (clearingExponent ι i)⌉ : ℚ) /
        10 ^ 24 :=
  rfl

/-- The clearing allowance is nonnegative. -/
theorem ePiece_nonneg (ι : FIndex) : 0 ≤ ePiece ι := by
  rw [ePiece_def]
  refine sum_nonneg fun i hi => div_nonneg ?_ (by positivity)
  have ht : 0 ≤ clearingExponent ι i :=
    (clearingExponent_pos (Nat.lt_succ_iff.mp (mem_range.mp hi))).le
  have hP := expPartialSum_pos 80 ht
  exact_mod_cast Int.ceil_nonneg (by positivity)

end CollatzPosDens
