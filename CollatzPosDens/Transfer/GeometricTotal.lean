/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecificLimits.Basic
public import CollatzPosDens.Attr
public import CollatzPosDens.Transfer.GeometricMass

/-!
# Total geometric mass of the words of a given length

For every `t ∈ ℕ`, the set `ℤ_{≥1}^t` of words of length `t` has geometric mass
`𝐩(ℤ_{≥1}^t) = 1`. Since `2^{-A(w)} = ∏_{i=1}^t 2^{-a_i}`, Tonelli gives
`𝐩(ℤ_{≥1}^t) = (∑_{a ≥ 1} 2^{-a})^t = 1`.

## Main results

* `CollatzPosDens.geomMass_setOf_length_eq`: `𝐩({w | |w| = t}) = 1`.
* `CollatzPosDens.geomMass_setOf_length_succ_and`: the first-letter decomposition
  `𝐩({x ∈ ℤ_{≥1}^{t+1} : P x}) = ∑_{a ≥ 1} 2^{-a} 𝐩({y ∈ ℤ_{≥1}^t : P (a y)})`.

## Implementation notes

Words are lists of positive integers, so `ℤ_{≥1}^t` is the set of words of length `t`. The
product formula is proved by induction on `t`: prepending a letter is a bijection
`ℕ+ × ℤ_{≥1}^t ≃ ℤ_{≥1}^{t+1}`, which splits the sum as `(∑_{a ≥ 1} 2^{-a}) · 𝐩(ℤ_{≥1}^t)`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- `∑_{a ≥ 1} 2^{-a} = 1` in `ℝ≥0∞`. -/
theorem tsum_two_inv_pow_pnat : ∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) = 1 := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n => (2⁻¹ : ℝ≥0∞) ^ n), ENNReal.tsum_geometric_add_one,
    ENNReal.one_sub_inv_two, inv_inv, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Prepending a letter is a bijection from `ℕ+ × ℤ_{≥1}^t` onto `ℤ_{≥1}^{t+1}`. -/
def Word.consLengthEquiv (t : ℕ) :
    ℕ+ × {w : Word | w.length = t} ≃ {w : Word | w.length = t + 1} where
  toFun p := ⟨p.1 :: p.2.1, congrArg Nat.succ p.2.2⟩
  invFun
    | ⟨[], h⟩ => absurd h (by simp)
    | ⟨a :: w, h⟩ => (a, ⟨w, by simpa using h⟩)
  left_inv p := rfl
  right_inv
    | ⟨[], h⟩ => absurd h (by simp)
    | ⟨_ :: _, _⟩ => rfl

/-- Splitting a sum over the words of length `t + 1` according to the first letter. -/
theorem Word.tsum_setOf_length_succ (t : ℕ) (f : Word → ℝ≥0∞) :
    ∑' w : {w : Word | w.length = t + 1}, f w =
      ∑' a : ℕ+, ∑' y : {w : Word | w.length = t}, f (a :: (y : Word)) := by
  rw [← (Word.consLengthEquiv t).tsum_eq]
  exact ENNReal.tsum_prod (f := fun (a : ℕ+) (y : {w : Word | w.length = t}) => f (a :: y.1))

/-- The geometric mass of `{x ∈ ℤ_{≥1}^t : P x}` as a sum over `ℤ_{≥1}^t`. -/
theorem geomMass_setOf_length_and (t : ℕ) (P : Word → Prop) :
    geomMass {x : Word | x.length = t ∧ P x} =
      ∑' w : {w : Word | w.length = t}, {x | P x}.indicator Word.massWeight w := by
  rw [geomMass_eq_tsum_indicator, tsum_subtype, Set.indicator_indicator]
  rfl

/-- First-letter decomposition of the geometric mass of a set of words of length `H + 1`. -/
theorem geomMass_setOf_length_succ_and (H : ℕ) (P : Word → Prop) :
    geomMass {x : Word | x.length = H + 1 ∧ P x} =
      ∑' a : ℕ+, 2⁻¹ ^ (a : ℕ) * geomMass {y : Word | y.length = H ∧ P (a :: y)} := by
  rw [geomMass_setOf_length_and, Word.tsum_setOf_length_succ]
  refine tsum_congr fun a => ?_
  rw [geomMass_setOf_length_and, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun y => ?_
  by_cases h : P (a :: (y : Word))
  · rw [Set.indicator_of_mem (s := {x | P x}) h, Set.indicator_of_mem (s := {x | P (a :: x)}) h]
    simp [Word.massWeight, pow_add]
  · rw [Set.indicator_of_notMem (s := {x | P x}) h,
      Set.indicator_of_notMem (s := {x | P (a :: x)}) h, mul_zero]

/-- For every `t`, the words of length `t` have geometric mass `𝐩(ℤ_{≥1}^t) = 1`. -/
@[collatz_pos_dens "lem_geometric_total"]
theorem geomMass_setOf_length_eq (t : ℕ) : geomMass {w : Word | w.length = t} = 1 := by
  induction t with
  | zero =>
    simp
  | succ t ih =>
    rw [geomMass_def, ← (Word.consLengthEquiv t).tsum_eq]
    simp only [Word.consLengthEquiv, Equiv.coe_fn_mk, Word.massWeight, Word.valSum_cons,
      pow_add]
    rw [ENNReal.tsum_prod (f := fun (a : ℕ+) (w : {w : Word | w.length = t}) =>
      (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * 2⁻¹ ^ (w : Word).valSum)]
    simp_rw [ENNReal.tsum_mul_left]
    rw [← geomMass_def, ih]
    simp only [mul_one, tsum_two_inv_pow_pnat]

end CollatzPosDens
