/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Mixing.MxOffsetTail
public import CollatzPosDens.Mixing.MxShPartialSumsOffset
public import CollatzPosDens.Mixing.MxShRenewalMass
public import CollatzPosDens.Mixing.MxShSplitOffset

/-!
# Offset tail of fair bits

For `q ∈ ℕ` and real `y ≥ 0`, a uniformly random subset `β ⊆ {1, …, q}` has offset at least `y`
with probability at most `7 / (y + 2)`:
$$2^{-q}\,\#\{\beta \subseteq \{1, \dots, q\} : \operatorname{Of}(\beta) \ge y\}
  \le \frac{7}{y + 2}.$$

## Main results

* `CollatzPosDens.geomMass_setOf_mem_finset`: the geometric mass of the words with a property `P`
  whose image under `f` lies in a finite set `s` is the sum over `a ∈ s` of the masses of the
  fibres.
* `CollatzPosDens.card_setOffset_ge_le`: the offset tail of fair bits.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026]
-/

@[expose] public section

open scoped ENNReal
open Finset

namespace CollatzPosDens

/-- Geometric mass is additive over the fibres of a map into a finite set:
`𝐩({w : P w ∧ f w ∈ s}) = ∑_{a ∈ s} 𝐩({w : P w ∧ f w = a})`. -/
theorem geomMass_setOf_mem_finset {α : Type*} (P : Word → Prop) (f : Word → α)
    (s : Finset α) :
    geomMass {w | P w ∧ f w ∈ s} = ∑ a ∈ s, geomMass {w | P w ∧ f w = a} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, ← ih, ← geomMass_union]
    · congr 1
      ext w
      simp only [mem_insert, Set.mem_ofPred_eq, Set.mem_union]
      tauto
    · rw [Set.disjoint_left]
      rintro w ⟨-, rfl⟩ ⟨-, hw⟩
      exact ha hw

/-- **Offset tail of fair bits.** For `q ∈ ℕ` and real `y ≥ 0`,
`2^{-q} #{β ⊆ {1, …, q} : Of(β) ≥ y} ≤ 7 / (y + 2)`. -/
@[collatz_pos_dens "lem_mx_sh_fair_bits"]
theorem card_setOffset_ge_le (q : ℕ) {y : ℝ} (hy : 0 ≤ y) :
    (2 : ℝ)⁻¹ ^ q * #{β ∈ (Icc 1 q).powerset | y ≤ (setOffset β : ℝ)} ≤ 7 / (y + 2) := by
  set F := {β ∈ (Icc 1 q).powerset | y ≤ (setOffset β : ℝ)} with hF
  have hmass : geomMass {w : Word | w.length = q ∧ w.partialSums ∩ Icc 1 q ∈ F} =
      (#F : ℝ≥0∞) * 2⁻¹ ^ q := by
    rw [geomMass_setOf_mem_finset, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun β hβ => ?_
    exact geomMass_partialSums_inter_Icc_eq q (mem_powerset.1 (mem_filter.1 hβ).1)
  have hsub : {w : Word | w.length = q ∧ w.partialSums ∩ Icc 1 q ∈ F} ⊆
      {w : Word | w.length = q ∧ y ≤ (off w : ℝ)} := by
    rintro w ⟨hw, hβ⟩
    refine ⟨hw, (mem_filter.1 hβ).2.trans ?_⟩
    have hsplit := setOffset_eq_add_of_one_le
      (fun s hs => Word.pos_of_mem_partialSums hs) (S := w.partialSums) q
    have hrest : 0 ≤ (3 : ℚ) ^ (w.partialSums ∩ Icc 1 q).card * ((2 : ℚ) ^ q)⁻¹ *
        setOffset (((w.partialSums).filter (q < ·)).image (· - q)) := by
      have := setOffset_nonneg (((w.partialSums).filter (q < ·)).image (· - q))
      positivity
    rw [Word.off_eq_setOffset_partialSums]
    exact_mod_cast (le_add_of_nonneg_right hrest).trans_eq hsplit.symm
  have h := (hmass ▸ geomMass_mono hsub).trans (geomMass_offsetTail_le q hy)
  have hpos : (0 : ℝ) ≤ 7 / (y + 2) := by positivity
  rw [← ENNReal.ofReal_le_ofReal_iff hpos, mul_comm, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos
    (by norm_num)]
  simpa using h

end CollatzPosDens
