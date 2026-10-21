/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Seed.S05OfflawCdf

/-!
# The recursion of the offset distribution function

Splitting off the first letter of a word, `u = (a) v` with `a ≥ 1`, gives
`off(u) = 2^{-a} (1 + 3 off(v))` and `A(u) = a + A(v)`. Hence `off(u) ≤ x` if and only if
`off(v) ≤ (2^a x - 1)/3`, and summing the geometric weights first over `v` gives the recursion
$$\mathsf F_{D+1}(x) = \sum_{a \ge 1} 2^{-a}\, \mathsf F_D\Bigl(\frac{2^a x - 1}{3}\Bigr)$$
in `[0, ∞]`, for every `D ∈ ℕ` and every real `x`.

## Main results

* `CollatzPosDens.off_cons_le_iff`: `off((a) v) ≤ x ↔ off(v) ≤ (2^a x - 1)/3`.
* `CollatzPosDens.offlawCdf_succ`: the recursion
  `𝖥_{D+1}(x) = ∑_{a ≥ 1} 2^{-a} 𝖥_D((2^a x - 1)/3)`.

## Implementation notes

The sum over `a ≥ 1` is a `tsum` over `ℕ+` in `ℝ≥0∞`, and `2^{-a}` is written `2⁻¹ ^ a`, as in
the geometric mass.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal

namespace CollatzPosDens

/-- Splitting off the first letter: `off((a) v) ≤ x` if and only if `off(v) ≤ (2^a x - 1)/3`. -/
theorem off_cons_le_iff (a : ℕ+) (v : Word) (x : ℝ) :
    ((off (a :: v) : ℚ) : ℝ) ≤ x ↔ (off v : ℝ) ≤ (2 ^ (a : ℕ) * x - 1) / 3 := by
  have h : off (a :: v) = ((2 : ℚ) ^ (a : ℕ))⁻¹ * (1 + 3 * off v) := by
    rw [show a :: v = [a] ++ v from rfl, off_append, Word.weight_singleton]
    simp only [off_cons, off_nil]
    ring
  rw [h]
  push_cast
  have h2 : (0 : ℝ) < 2 ^ (a : ℕ) := by positivity
  rw [inv_mul_le_iff₀ h2, le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
  constructor <;> intro h <;> linarith

/-- **Recursion of the offset distribution function**: for every `D ∈ ℕ` and real `x`,
`𝖥_{D+1}(x) = ∑_{a ≥ 1} 2^{-a} 𝖥_D((2^a x - 1)/3)`, an identity in `[0, ∞]`. -/
@[collatz_pos_dens "lem_s05_offlaw_recursion"]
theorem offlawCdf_succ (D : ℕ) (x : ℝ) :
    offlawCdf (D + 1) x =
      ∑' a : ℕ+, (2⁻¹ : ℝ≥0∞) ^ (a : ℕ) * offlawCdf D ((2 ^ (a : ℕ) * x - 1) / 3) := by
  set S : Set Word := {u : Word | u.length = D + 1 ∧ (off u : ℝ) ≤ x} with hS
  set f : Word → ℝ≥0∞ := S.indicator Word.massWeight with hf
  have hinj : Function.Injective (fun p : ℕ+ × Word => p.1 :: p.2) := by
    rintro ⟨a, v⟩ ⟨b, w⟩ h
    simp only [List.cons.injEq] at h
    rw [h.1, h.2]
  have hsupp : Function.support f ⊆ Set.range (fun p : ℕ+ × Word => p.1 :: p.2) := by
    intro u hu
    have hu' : u ∈ S := by
      by_contra hn
      exact hu (Set.indicator_of_notMem hn _)
    match u, hu' with
    | a :: v, _ => exact ⟨(a, v), rfl⟩
  rw [offlawCdf_def, geomMass_eq_tsum_indicator, ← hinj.tsum_eq hsupp]
  rw [ENNReal.tsum_prod (f := fun a v => f (a :: v))]
  refine tsum_congr fun a => ?_
  rw [offlawCdf_def, geomMass_eq_tsum_indicator, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun v => ?_
  simp only [hf, hS, Set.indicator_apply, Set.mem_ofPred_eq, List.length_cons,
    Nat.add_right_cancel_iff, off_cons_le_iff, Word.massWeight, Word.valSum_cons, pow_add]
  split_ifs <;> simp

end CollatzPosDens
