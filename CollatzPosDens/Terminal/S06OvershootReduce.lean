/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Ring.GeomSum
public import CollatzPosDens.Attr
public import CollatzPosDens.Maps.Admissible
public import CollatzPosDens.Terminal.LastValuationShift
public import CollatzPosDens.Maps.InverseOrbit
public import CollatzPosDens.Maps.Valsum
public import CollatzPosDens.Maps.Word
public import CollatzPosDens.FirstCrossing.Barrier
public import CollatzPosDens.FirstCrossing.FirstCrossing
public import CollatzPosDens.FirstCrossing.S03BarrierMono

/-!
# Reducing the overshoot of a first-crossing word

Let `w = (a₁, …, a_d) ∈ 𝒲(b, u, K)` be admissible from `R`. Then for some `i ≥ 0` with
`a_d > 2i` the word `w° = (a₁, …, a_{d-1}, a_d - 2i)` lies in `𝒲(b, u, 1)` and is admissible
from `R`. One takes `i = ⌊o / 2⌋` for the overshoot `o = A(w) - H_{b,u}(d) ∈ [0, K]`: the
proper prefixes of `w°` are those of `w`, its valuation sum `A(w) - 2i` exceeds the barrier
by `o - 2i ∈ {0, 1}`, and `a_d - 2i ≥ 1` because `A(w_{≤ d-1}) < H_{b,u}(d-1) ≤ H_{b,u}(d)`.
Admissibility is preserved since `4 ≡ 1 [MOD 3]`, so
`2 ^ {a_d - 2i} R_{d-1} ≡ 2 ^ {a_d} R_{d-1} ≡ 1 [MOD 3]`.

## Main results

* `CollatzPosDens.exists_overshoot_reduce`: the reduction `w ↦ w°`.

## Implementation notes

A nonempty word is written `v ++ [a]`, with `v = (a₁, …, a_{d-1})` and `a = a_d`; every word of
`𝒲(b, u, K)` is nonempty. The new last letter is the positive integer `a - 2i`. The result
holds for every `b : ℕ` and every rational `R`; the hypotheses `b ≥ 1` and `R` a positive odd
integer are not needed. The barrier `H_{b,u}` is `CollatzPosDens.barrier`.

## References

* [Mazur, *Explicit Positive-Density Collatz Convergence in Logarithmic Time*][mazur2026], §17.3.
-/

@[expose] public section

namespace CollatzPosDens

/-- **Overshoot reduction.** If `w = (a₁, …, a_d) ∈ 𝒲(b, u, K)` is admissible from `R`, then
there is `i ≥ 0` with `a_d > 2i` such that `(a₁, …, a_{d-1}, a_d - 2i) ∈ 𝒲(b, u, 1)` is
admissible from `R`. Here `w = v ++ [a]`, and the new last letter is the positive integer
`a - 2i`. -/
@[collatz_pos_dens "lem_s06_overshoot_reduce"]
theorem exists_overshoot_reduce {b : ℕ} {u : ℤ} {K : ℕ} {R : ℚ} {v : Word} {a : ℕ+}
    (hw : v ++ [a] ∈ firstCrossing b u K) (hR : Admissible R (v ++ [a])) :
    ∃ (i : ℕ) (hi : 2 * i < a),
      v ++ [⟨a - 2 * i, Nat.sub_pos_of_lt hi⟩] ∈ firstCrossing b u 1 ∧
      Admissible R (v ++ [⟨a - 2 * i, Nat.sub_pos_of_lt hi⟩]) := by
  obtain ⟨hl, hh, hpre, hlo, hhi⟩ := hw
  simp only [List.length_append, List.length_singleton, Word.valSum_append,
    Word.valSum_singleton] at hl hh hpre hlo hhi
  set o : ℕ := ((Word.valSum v : ℤ) + (a : ℕ) - barrier b u (v.length + 1)).toNat with ho
  have ho' : (o : ℤ) = (Word.valSum v : ℤ) + (a : ℕ) - barrier b u (v.length + 1) := by
    rw [ho, Int.toNat_of_nonneg (by push_cast at hlo ⊢; linarith)]
  have hv : (Word.valSum v : ℤ) < barrier b u v.length := by
    have := hpre v.length (by omega) (by omega)
    rwa [List.take_append_of_le_length le_rfl, List.take_length] at this
  have hmono := barrier_le_barrier_succ b u v.length
  have hj : 2 * (o / 2) < a := by
    have h2 : (2 * (o / 2 : ℕ) : ℤ) ≤ o := by exact_mod_cast Nat.mul_div_le o 2
    have : (2 * (o / 2 : ℕ) : ℤ) < (a : ℕ) := by linarith
    exact_mod_cast this
  have hmod : (o : ℤ) - 2 * (o / 2 : ℕ) ≤ 1 ∧ 0 ≤ (o : ℤ) - 2 * (o / 2 : ℕ) := by
    constructor <;> push_cast <;> omega
  have key : ∀ a' : ℕ+, (a' : ℕ) + 2 * (o / 2) = a → v ++ [a'] ∈ firstCrossing b u 1 := by
    intro a' ha'
    have ha'' : ((a' : ℕ) : ℤ) = (a : ℕ) - 2 * (o / 2 : ℕ) := by
      rw [← ha']; push_cast; ring
    simp only [mem_firstCrossing, List.length_append, List.length_singleton,
      Word.valSum_append, Word.valSum_singleton]
    refine ⟨hl, hh, fun i hi his => ?_, ?_, ?_⟩
    · rw [List.take_append_of_le_length (by omega)]
      have := hpre i hi his
      rwa [List.take_append_of_le_length (by omega)] at this
    · push_cast [ha'']
      linarith [hmod.2]
    · push_cast [ha'']
      linarith [hmod.1]
  have hlet : ((⟨a - 2 * (o / 2), Nat.sub_pos_of_lt hj⟩ : ℕ+) : ℕ) + 2 * (o / 2) = a :=
    Nat.sub_add_cancel hj.le
  have hsh : shiftLastLetter ⟨a - 2 * (o / 2), Nat.sub_pos_of_lt hj⟩ (o / 2) = a := PNat.eq hlet
  exact ⟨o / 2, hj, key _ hlet, (admissible_append_shiftLastLetter_iff _).1 (by rwa [hsh])⟩

end CollatzPosDens
