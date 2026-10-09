/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import CollatzPosDens.Attr
public import CollatzPosDens.Renewal.RnPascal
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The raw-prefix mass `𝖱(k, t)`

For `k ∈ ℕ` and `t ∈ ℤ`, the raw-prefix mass is
`𝖱(k, t) = ∑ ∏_{i=1}^k ϖ(c_i)`, the sum running over the words `c = (c₁, …, c_k) ∈ ℤ^k` whose
letters are all at least `2` and sum to `t`. It is the `k`-fold convolution power of the Pascal
law `ϖ`, evaluated at `t`.

## Main definitions

* `CollatzPosDens.rawWords k t`: the finite set of words `c : Fin k → ℤ` with `c_i ≥ 2` and
  `c₁ + ⋯ + c_k = t`.
* `CollatzPosDens.rawMass k t`: the raw-prefix mass `𝖱(k, t)`.

## Main results

* `CollatzPosDens.mem_rawWords`: membership in `rawWords k t` is exactly the condition
  `(∀ i, 2 ≤ c i) ∧ ∑ i, c i = t`.
* `CollatzPosDens.rawMass_zero`: `𝖱(0, t) = [t = 0]`.
* `CollatzPosDens.rawMass_succ`: the convolution recursion
  `𝖱(k + 1, t) = ∑_{2 ≤ a ≤ t} ϖ(a) 𝖱(k, t - a)`.
* `CollatzPosDens.rawMass_nonneg`: `𝖱(k, t) ≥ 0`.
* `CollatzPosDens.rawMass_of_neg`, `CollatzPosDens.rawMass_succ_of_lt_two`: the vanishing ranges.

## Implementation notes

A word of length `k` is a function `Fin k → ℤ`. Every letter of a word with letters at least `2`
and sum `t` lies in `[2, t]`, so the index set of the sum is the finite set `rawWords k t`, carved
out of the box `[2, t]^k`, and `𝖱(k, t)` is a finite sum. By `mem_rawWords`, the box constraint
adds nothing beyond the conditions `c_i ≥ 2` and `c₁ + ⋯ + c_k = t`.

## References

* [Mazur, *Collatz positive density*], §6.1.
-/

@[expose] public section

namespace CollatzPosDens

open Finset

/-- The words `c = (c₁, …, c_k) ∈ ℤ^k` with every letter `c_i ≥ 2` and `c₁ + ⋯ + c_k = t`, as a
finite set (every such letter lies in `[2, t]`). -/
def rawWords (k : ℕ) (t : ℤ) : Finset (Fin k → ℤ) :=
  (Fintype.piFinset fun _ : Fin k ↦ Icc 2 t).filter fun c ↦ ∑ i, c i = t

/-- A word lies in `rawWords k t` iff its letters are at least `2` and sum to `t`. -/
theorem mem_rawWords {k : ℕ} {t : ℤ} {c : Fin k → ℤ} :
    c ∈ rawWords k t ↔ (∀ i, 2 ≤ c i) ∧ ∑ i, c i = t := by
  simp only [rawWords, mem_filter, Fintype.mem_piFinset, mem_Icc]
  refine ⟨fun h ↦ ⟨fun i ↦ (h.1 i).1, h.2⟩, fun ⟨h2, hs⟩ ↦ ⟨fun i ↦ ⟨h2 i, ?_⟩, hs⟩⟩
  rw [← hs]
  exact single_le_sum (fun j _ ↦ by linarith [h2 j]) (mem_univ i)

/-- The raw-prefix mass `𝖱(k, t) = ∑ ∏_{i=1}^k ϖ(c_i)`, summed over the words `c ∈ ℤ^k` with
`c_i ≥ 2` for all `i` and `c₁ + ⋯ + c_k = t`. -/
@[collatz_pos_dens "def_rn_raw_mass"]
noncomputable def rawMass (k : ℕ) (t : ℤ) : ℝ :=
  ∑ c ∈ rawWords k t, ∏ i, varpi (c i)

/-- `𝖱(0, t)` is `1` if `t = 0` and `0` otherwise (the empty word). -/
theorem rawMass_zero (t : ℤ) : rawMass 0 t = if t = 0 then 1 else 0 := by
  by_cases ht : t = 0
  · subst ht
    have : rawWords 0 0 = {Fin.elim0} := by
      ext c; simp [mem_rawWords, Subsingleton.elim c Fin.elim0]
    simp [rawMass, this]
  · have : rawWords 0 t = ∅ := by
      ext c; simp [mem_rawWords, Ne.symm ht]
    simp [rawMass, this, ht]

/-- The convolution recursion `𝖱(k + 1, t) = ∑_{2 ≤ a ≤ t} ϖ(a) 𝖱(k, t - a)`, splitting off the
first letter. -/
theorem rawMass_succ (k : ℕ) (t : ℤ) :
    rawMass (k + 1) t = ∑ a ∈ Icc 2 t, varpi a * rawMass k (t - a) := by
  simp only [rawMass, mul_sum]
  rw [sum_sigma']
  refine sum_nbij' (fun c ↦ ⟨c 0, Fin.tail c⟩) (fun x ↦ Fin.cons x.1 x.2) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    rw [mem_rawWords, Fin.sum_univ_succ] at hc
    simp only [mem_sigma, mem_Icc, mem_rawWords]
    refine ⟨⟨hc.1 0, ?_⟩, fun i ↦ hc.1 _, ?_⟩
    · have : 0 ≤ ∑ i : Fin k, c i.succ := sum_nonneg fun i _ ↦ by linarith [hc.1 i.succ]
      linarith [hc.2]
    · simp only [Fin.tail]; linarith [hc.2]
  · rintro ⟨a, d⟩ hx
    simp only [mem_sigma, mem_Icc, mem_rawWords] at hx
    rw [mem_rawWords, Fin.sum_univ_succ]
    refine ⟨fun i ↦ Fin.cases hx.1.1 (fun j ↦ hx.2.1 j) i, ?_⟩
    simp only [Fin.cons_zero, Fin.cons_succ]
    linarith [hx.2.2]
  · intro c _
    simp
  · rintro ⟨a, d⟩ _
    simp
  · intro c _
    simp [Fin.prod_univ_succ, Fin.tail]

/-- The raw-prefix mass is nonnegative. -/
theorem rawMass_nonneg (k : ℕ) (t : ℤ) : 0 ≤ rawMass k t :=
  sum_nonneg fun _ _ ↦ prod_nonneg fun _ _ ↦ varpi_nonneg _

/-- `𝖱(k, t) = 0` for `t < 0`: a word with letters `≥ 2` has nonnegative sum. -/
theorem rawMass_of_neg (k : ℕ) {t : ℤ} (ht : t < 0) : rawMass k t = 0 := by
  refine sum_eq_zero fun c hc ↦ ?_
  exfalso
  rw [mem_rawWords] at hc
  have : 0 ≤ ∑ i, c i := sum_nonneg fun i _ ↦ by linarith [hc.1 i]
  linarith [hc.2]

/-- `𝖱(k + 1, t) = 0` for `t < 2`: a nonempty word with letters `≥ 2` has sum at least `2`. -/
theorem rawMass_succ_of_lt_two (k : ℕ) {t : ℤ} (ht : t < 2) : rawMass (k + 1) t = 0 := by
  rw [rawMass_succ, Icc_eq_empty (by omega), sum_empty]

end CollatzPosDens
