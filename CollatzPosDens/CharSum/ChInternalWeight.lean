/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Analysis.SpecialFunctions.Exp
public import CollatzPosDens.Attr
public import CollatzPosDens.BlackSet.BkPoints
public import CollatzPosDens.CharSum.ChBlockPoint
public import CollatzPosDens.CharSum.ChResidualReward
public import CollatzPosDens.Transfer.S02Z

/-!
# The internal weight of a block

Fix a level `n`, a residue `ξ ∈ G_n` and a threshold `ε`, and let `ρ_c` be the residual reward
and `z_*` the transfer exponent. For a point `x ∈ ℕ × ℤ` and a block `β = (c, e)` with
`c = (c₁, …, c_m)`, the *internal weight* of `β` started at `x` is
`I(x; β) = ∏_{i=1}^m exp(-z_* ρ_{c_i}(x + (i, c₁ + ⋯ + c_i))) · exp(-z_* ρ_e(x + bpt(β)))`,
the empty product being `1`. Every letter of the block, the closing letter included,
contributes the factor of its residual reward at the lattice point reached by the partial sums
of the block when it is read starting from `x`.

## Main definitions

* `CollatzPosDens.chInternalWeight n ξ ε x β`: the internal weight `I(x; β)`.

## Main results

* `CollatzPosDens.chInternalWeight_nil`: `I(x; ([], e)) = exp(-z_* ρ_e(x + (1, e)))`.
* `CollatzPosDens.chInternalWeight_cons`: the recursion
  `I(x; (a :: c, e)) = exp(-z_* ρ_a(x + (1, a))) · I(x + (1, a); (c, e))`.
* `CollatzPosDens.chInternalWeight_pos`: `0 < I(x; β)`.
* `CollatzPosDens.chInternalWeight_eq_one_of_le`: `I(x; β) = 1` when `⌊n/2⌋ ≤ j(x)`.

## Implementation notes

A block is modelled as `β : List ℤ × ℤ`, as for `chBlockPoint`. The point `x` is taken in
`ℤ × ℤ` rather than `ℕ × ℤ`. The index `i : Fin m` is `0`-based, so the index `i + 1` appears as
the first coordinate `i + 1` of the shift, and the partial sum `c₁ + ⋯ + c_{i+1}` is
`(c.take (i + 1)).sum`. The residual reward is nonnegative (`zero_le_chResidualReward`), so the
internal weight is at most `1` (`chInternalWeight_le_one`).

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

namespace CollatzPosDens

/-- The internal weight
`I(x; β) = ∏_{i=1}^m exp(-z_* ρ_{c_i}(x + (i, c₁ + ⋯ + c_i))) · exp(-z_* ρ_e(x + bpt(β)))`
of a block `β = (c, e)` started at `x`, where `ρ` is the residual reward for `n, ξ, ε`. -/
@[collatz_pos_dens "def_ch_internal_weight"]
noncomputable def chInternalWeight (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) : ℝ :=
  (∏ i : Fin β.1.length,
    Real.exp (-(zStar : ℝ) *
      chResidualReward n ξ ε β.1[i] (x + ((i : ℤ) + 1, (β.1.take (i + 1)).sum)))) *
    Real.exp (-(zStar : ℝ) * chResidualReward n ξ ε β.2 (x + chBlockPoint β))

/-- A block with no nonclosing letters has internal weight `exp(-z_* ρ_e(x + (1, e)))`. -/
@[simp]
lemma chInternalWeight_nil (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ) (e : ℤ) :
    chInternalWeight n ξ ε x ([], e) =
      Real.exp (-(zStar : ℝ) * chResidualReward n ξ ε e (x + (1, e))) := by
  simp [chInternalWeight]

/-- The recursion for the internal weight: prepending a nonclosing letter `a` contributes the
factor `exp(-z_* ρ_a(x + (1, a)))` and shifts the start to `x + (1, a)`. -/
lemma chInternalWeight_cons (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ) (a : ℤ)
    (c : List ℤ) (e : ℤ) :
    chInternalWeight n ξ ε x (a :: c, e) =
      Real.exp (-(zStar : ℝ) * chResidualReward n ξ ε a (x + (1, a))) *
        chInternalWeight n ξ ε (x + (1, a)) (c, e) := by
  have hpt : x + chBlockPoint (a :: c, e) = x + (1, a) + chBlockPoint (c, e) := by
    rw [chBlockPoint_cons]; abel
  have hprod : ∀ i : Fin c.length,
      x + (((i.succ : Fin (a :: c).length) : ℤ) + 1, ((a :: c).take (i.succ + 1)).sum) =
        x + (1, a) + ((i : ℤ) + 1, (c.take (i + 1)).sum) := by
    intro i
    ext <;> simp [List.take_succ_cons] <;> ring
  unfold chInternalWeight
  dsimp only
  rw [hpt]
  simp only [List.length_cons]
  rw [Fin.prod_univ_succ, mul_assoc]
  refine congrArg₂ (· * ·) (by simp) (congrArg₂ (· * ·) ?_ rfl)
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hprod i]
  rfl

/-- The internal weight as the exponential of a sum of residual rewards. -/
lemma chInternalWeight_eq_exp (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) :
    chInternalWeight n ξ ε x β =
      Real.exp (-(zStar : ℝ) *
        ((∑ i : Fin β.1.length,
          chResidualReward n ξ ε β.1[i] (x + ((i : ℤ) + 1, (β.1.take (i + 1)).sum))) +
          chResidualReward n ξ ε β.2 (x + chBlockPoint β))) := by
  rw [chInternalWeight, mul_add, Real.exp_add, Finset.mul_sum, Real.exp_sum]

/-- The internal weight is positive. -/
lemma chInternalWeight_pos (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) : 0 < chInternalWeight n ξ ε x β := by
  rw [chInternalWeight_eq_exp]
  exact Real.exp_pos _

/-- The internal weight is nonnegative. -/
lemma chInternalWeight_nonneg (n : ℕ) (ξ : ResidueGroup n) (ε : ℝ) (x : ℤ × ℤ)
    (β : List ℤ × ℤ) : 0 ≤ chInternalWeight n ξ ε x β :=
  (chInternalWeight_pos n ξ ε x β).le

/-- The internal weight of a block started at a point `x` with `⌊n/2⌋ ≤ j(x)` is `1`: every
point at which it evaluates a residual reward has first coordinate `> ⌊n/2⌋`. -/
lemma chInternalWeight_eq_one_of_le {n : ℕ} (ξ : ResidueGroup n) (ε : ℝ) {x : ℤ × ℤ}
    (hx : ((n / 2 : ℕ) : ℤ) ≤ bkJ x) (β : List ℤ × ℤ) :
    chInternalWeight n ξ ε x β = 1 := by
  rw [chInternalWeight, chResidualReward_eq_zero_of_lt_bkJ (by simp [bkJ] at hx ⊢; omega),
    mul_zero, Real.exp_zero, mul_one]
  refine Finset.prod_eq_one fun i _ => ?_
  rw [chResidualReward_eq_zero_of_lt_bkJ (by simp [bkJ] at hx ⊢; omega), mul_zero,
    Real.exp_zero]

end CollatzPosDens
